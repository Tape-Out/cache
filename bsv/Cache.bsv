package Cache;

import Vector::*;
import ConfigReg::*;
import RegFile::*;
import RegIf::*;
import CacheRegs::*;

// 直接映射、写穿透、读时装填的一级缓存。核这一侧是会停顿的目标（RegTarget），
// 存储那一侧自己当发起方（RegManager）。
//
// 为什么先做这一档：E32 量过，每多一拍存储延迟，那段自检程序就多约 65 拍——
// 51 条指令、约 65 次访存，等于**每次访存把延迟原价付出去**，一点没摊掉。
// 缓存能省下的上限就是这个数，所以先要一个能证明「摊掉了」的最简实现。
//
// 直接映射而不是组相联：D51 说过并行比对只能用触发器加比较器，那是 CAM 的代价。
// 写穿透而不是写回：写回要脏位、要牺牲行的回写通路，还要在核看不见的时候占总线。
//
// **请求先寄存一拍再答**。组合直答的目标就是 RegIf，不需要另立形态；而 mkPipe
// 那条规则既写请求线又读应答，同拍相关就是 BypassWire 在一条规则里读写（G0004）。
// 命中也要一拍，这跟真实的缓存一样。

typedef struct {
  Bool stats;
} CacheCfg deriving (Bits, FShow);

interface CacheIfc#(numeric type aw, numeric type dw,
                    numeric type cachedBit, numeric type lines,
                    numeric type wpl);
  interface RegTarget#(32, 32)  up;
  interface RegManager#(32, 32) down;
  interface RegIf#(aw, dw)      regs;
endinterface

module mkCache#(CacheCfg cfg)(CacheIfc#(aw, dw, cachedBit, lines, wpl))
    provisos (Mul#(TDiv#(dw, 8), 8, dw), Add#(_z, 8, aw),
              Log#(wpl, lw), Add#(_a, lw, 32), Add#(_b, TLog#(lines), 32),
              Add#(_c, 16, dw), Add#(_d, 32, dw));

  CacheRegsIfc#(aw, dw) r <- mkCacheRegs(CacheRegsCfg { stats: cfg.stats });

  Integer nl = valueOf(lines);
  Integer nw = valueOf(wpl);
  Integer lw = valueOf(lw);
  // 可缓存窗口：地址的第 cachedBit 位为 1 才进缓存。外设寄存器不是内存——
  // 缓存一整行地拉回来、下次还从缓存答，语义就错了。soc-linux 上第一次挂
  // 缓存就撞了这个：程序读 clint 的 mtimecmp，读回来的是陈值。
  Integer cb = valueOf(cachedBit);

  // 标签与有效位用触发器：直接映射一次只比一个，量小。
  // 数据阵列走 RegFile——换成 SRAM 宏时只动这一行，接口不必改。
  Vector#(lines, Reg#(Bit#(32))) tag <- replicateM(mkConfigReg(0));
  Vector#(lines, Reg#(Bool))     vld <- replicateM(mkConfigReg(False));
  RegFile#(Bit#(16), Bit#(32))   dat <- mkRegFile(0, fromInteger(nl * nw - 1));

  Reg#(Bool)            busy <- mkConfigReg(False);   // 手上有一笔没答完
  Reg#(RegReq#(32, 32)) q    <- mkReg(unpack(0));
  Reg#(Bool)            ansV <- mkConfigReg(False);
  Reg#(Bit#(32))        ansD <- mkConfigReg(0);

  Reg#(Bool)     filling <- mkConfigReg(False);
  Reg#(Bit#(32)) fillAd  <- mkConfigReg(0);
  Reg#(Bit#(16)) fillIx  <- mkConfigReg(0);
  Reg#(Bit#(32)) fillLn  <- mkConfigReg(0);
  // 直通：写穿透与不可缓存的读共用这条路——都是「原样发下去，等回复」。
  Reg#(Bool)     thru    <- mkConfigReg(False);
  Reg#(Bool)     thruRd  <- mkConfigReg(False);   // 回复要不要交给核

  Wire#(Bool)            uV <- mkBypassWire;
  Wire#(RegReq#(32, 32)) uQ <- mkBypassWire;
  Wire#(Bool)            dRspV <- mkBypassWire;
  Wire#(RegRsp#(32))     dRspX <- mkBypassWire;

  function Bit#(32) lineOf(Bit#(32) a) = (a >> (2 + lw)) % fromInteger(nl);
  function Bit#(32) tagOf(Bit#(32) a)  = a >> (2 + lw);
  function Bit#(16) slotOf(Bit#(32) ln, Bit#(32) w) =
      truncate(ln * fromInteger(nw) + w);
  function Bit#(32) wordOf(Bit#(32) a) = (a >> 2) % fromInteger(nw);

  Bit#(32) ln  = lineOf(q.addr);
  Bool     hit = vld[ln] && tag[ln] == tagOf(q.addr);
  Bit#(16) slt = slotOf(ln, wordOf(q.addr));

  rule geom;
    r.geom_lines_in(fromInteger(nl));
    r.geom_wpl_in(fromInteger(nw));
  endrule

  rule accept (uV && !busy);
    q    <= uQ;
    busy <= True;
  endrule

  // 查表：命中当拍出答复；缺失起一次填充，填完这条规则会再跑一遍并命中。
  rule lookup (busy && !ansV && !filling && !thru);
    Bool cacheable = q.addr[cb] == 1;
    if (!cacheable) begin
      thru   <= True;
      thruRd <= !q.write;
    end else if (q.write) begin
      if (hit) dat.upd(slt, applyStrb(dat.sub(slt), q.wdata, q.wstrb));
      thru   <= True;
      thruRd <= False;
    end else if (hit) begin
      if (cfg.stats) r.hits_in(r.hits + 1);
      ansD <= dat.sub(slt);
      ansV <= True;
    end else begin
      if (cfg.stats) r.misses_in(r.misses + 1);
      filling <= True;
      fillAd  <= q.addr & ~fromInteger(nw * 4 - 1);
      fillIx  <= 0;
      fillLn  <= ln;
      vld[ln] <= False;
    end
  endrule

  rule fill (filling && dRspV);
    dat.upd(slotOf(fillLn, zeroExtend(fillIx)), dRspX.rdata);
    if (fillIx + 1 == fromInteger(nw)) begin
      filling     <= False;
      vld[fillLn] <= True;
      tag[fillLn] <= tagOf(fillAd);
    end else
      fillIx <= fillIx + 1;
  endrule

  rule thruDone (thru && dRspV);
    thru <= False;
    ansD <= thruRd ? dRspX.rdata : 0;
    ansV <= True;
  endrule

  // 答复只举一拍：发起方那一侧是组合看 resp 的，看过就算收到。
  rule finish (ansV);
    ansV <= False;
    busy <= False;
  endrule

  interface RegTarget up;
    method Action req(Bool v, RegReq#(32, 32) x);
      uV._write(v);
      uQ._write(x);
    endmethod
    // 三个输出都只看寄存器，不看这一拍进来的请求——否则 mkPipe 那条规则
    // 就在同一条规则里读写同一根线。
    method Bool ready = !busy;
    method Bool rspValid = ansV;
    method RegRsp#(32) rsp = RegRsp { rdata: ansD, err: False };
  endinterface

  interface RegManager down;
    method Bool valid = filling || thru;
    method RegReq#(32, 32) req =
      thru ? q
             : RegReq { addr: fillAd + (zeroExtend(fillIx) << 2), write: False,
                        wdata: 0, wstrb: 4'hF };
    method Action ready(Bool v); noAction; endmethod
    method Action resp(Bool v, RegRsp#(32) x);
      dRspV._write(v);
      dRspX._write(x);
    endmethod
  endinterface

  interface regs = r.regs;
endmodule

endpackage
