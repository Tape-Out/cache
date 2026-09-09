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
// 缓存能省下的上限就是这个数，所以先要一个能证明「摊掉了」的最简实现，
// 而不是一上来就四路组相联。
//
// 直接映射而不是组相联：D51 说过并行比对只能用触发器加比较器，那是 CAM 的
// 代价；直接映射一次只比一个标签。相联度值不值，等命中率数据出来再说。
//
// 写穿透而不是写回：写回要脏位、要牺牲行的回写通路，还要在核看不见的时候
// 占总线。第一次流片不值得，而写穿透的代价是明确的——写永远付全价。

typedef struct {
  Bool stats;
} CacheCfg deriving (Bits, FShow);

interface CacheIfc#(numeric type aw, numeric type dw,
                    numeric type lines, numeric type wpl);
  interface RegTarget#(32, 32)  up;
  interface RegManager#(32, 32) down;
  interface RegIf#(aw, dw)      regs;
endinterface

module mkCache#(CacheCfg cfg)(CacheIfc#(aw, dw, lines, wpl))
    provisos (Mul#(TDiv#(dw, 8), 8, dw), Add#(_z, 8, aw),
              Log#(wpl, lw), Add#(_a, lw, 32), Add#(_b, TLog#(lines), 32),
              Add#(_c, 16, dw), Add#(_d, 32, dw));

  CacheRegsIfc#(aw, dw) r <- mkCacheRegs(CacheRegsCfg { stats: cfg.stats });

  Integer nl = valueOf(lines);
  Integer nw = valueOf(wpl);
  Integer lw = valueOf(lw);

  // 标签与有效位用触发器：直接映射一次只比一个，量小。
  // 数据阵列走 RegFile——换成 SRAM 宏时只动这一行，接口不必改。
  Vector#(lines, Reg#(Bit#(32))) tag <- replicateM(mkConfigReg(0));
  Vector#(lines, Reg#(Bool))     vld <- replicateM(mkConfigReg(False));
  RegFile#(Bit#(16), Bit#(32))   dat <- mkRegFile(0, fromInteger(nl * nw - 1));

  Reg#(Bool)     filling <- mkConfigReg(False);
  Reg#(Bit#(32)) fillAd  <- mkConfigReg(0);
  Reg#(Bit#(16)) fillIx  <- mkConfigReg(0);
  Reg#(Bit#(32)) fillLn  <- mkConfigReg(0);

  Reg#(Bool)            wrPend <- mkConfigReg(False);
  Reg#(RegReq#(32, 32)) wrReq  <- mkReg(unpack(0));


  Wire#(Bool)        uV   <- mkBypassWire;
  Wire#(RegReq#(32, 32)) uQ <- mkBypassWire;
  Wire#(Bool)        dRspV <- mkBypassWire;
  Wire#(RegRsp#(32)) dRspX <- mkBypassWire;

  function Bit#(32) lineOf(Bit#(32) a) = (a >> (2 + lw)) % fromInteger(nl);
  function Bit#(32) tagOf(Bit#(32) a)  = a >> (2 + lw);
  function Bit#(16) slotOf(Bit#(32) ln, Bit#(32) w) =
      truncate(ln * fromInteger(nw) + w);
  function Bit#(32) wordOf(Bit#(32) a) = (a >> 2) % fromInteger(nw);

  Bit#(32) ln  = lineOf(uQ.addr);
  Bool     hit = vld[ln] && tag[ln] == tagOf(uQ.addr);
  Bit#(16) slt = slotOf(ln, wordOf(uQ.addr));

  // 读命中当拍就答；读缺失起一次填充，期间 ready 拉低，发起方举着手等。
  // 写穿透：命中就顺手更新那一份，无论如何都往下写一次。
  rule serve (uV && !filling && !wrPend);
    if (uQ.write) begin
      if (hit) dat.upd(slt, applyStrb(dat.sub(slt), uQ.wdata, uQ.wstrb));
      wrReq  <= uQ;
      wrPend <= True;
    end else if (hit) begin
      if (cfg.stats) r.hits_in(r.hits + 1);
    end else begin
      if (cfg.stats) r.misses_in(r.misses + 1);
      filling <= True;
      fillAd  <= uQ.addr & ~fromInteger(nw * 4 - 1);
      fillIx  <= 0;
      fillLn  <= ln;
      vld[ln] <= False;
    end
  endrule

  rule geom;
    r.geom_lines_in(fromInteger(nl));
    r.geom_wpl_in(fromInteger(nw));
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

  rule wrDone (wrPend && dRspV);
    wrPend <= False;
  endrule

  interface RegTarget up;
    method Action req(Bool v, RegReq#(32, 32) q);
      uV._write(v);
      uQ._write(q);
    endmethod
    // 读命中当拍就收得下；写要等穿透那一拍；缺失要等整行拉回来。
    method Bool ready = !filling && !wrPend;
    method Bool rspValid = uV && !filling && !wrPend && (uQ.write || hit);
    method RegRsp#(32) rsp = RegRsp { rdata: dat.sub(slt), err: False };
  endinterface

  interface RegManager down;
    method Bool valid = filling || wrPend;
    method RegReq#(32, 32) req =
      wrPend ? wrReq
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
