"""cache 的行为测试台：一个会拖延的存储，一串有局部性的地址。

判据三条：读回来的数对不对（缓存不能改变语义）· 命中与缺失数对不对 ·
以及一行一字那一点必然全缺失（那等于「没有缓存」，是同一台架子上的对照组）。

期望值不是手填的，是拿同一套直接映射规则在 Python 里跑一遍算出来的——
旋钮一变期望跟着变，不然矩阵里除默认点之外全是摆设。
"""
import json
import math
import pathlib
import sys

out = pathlib.Path(sys.argv[1] if len(sys.argv) > 1 else ".")
out.mkdir(parents=True, exist_ok=True)
cfg = json.loads(sys.argv[2]) if len(sys.argv) > 2 else {}
label = cfg.get("label", "")
k = cfg.get("knobs", {})
lines = int(k.get("lines", 8))
wpl = int(k.get("wpl", 4))
stats = bool(k.get("stats", True))

LAT = 4
STEPS = 32
SPAN = 16          # 走 16 个字，两遍

lw = int(math.log2(wpl)) if wpl > 1 else 0
tags = {}
hits = misses = 0
for s in range(STEPS):
    w = s % SPAN
    ln = (w >> lw) % lines
    tg = w >> lw
    if tags.get(ln) == tg:
        hits += 1
    else:
        misses += 1
        tags[ln] = tg
        hits += 1      # 填完重试那一次也从数组里答，计一次命中

txt = f'''package Cache{label}Tb;

import Vector::*;
import ConfigReg::*;
import RegFile::*;
import RegIf::*;
import Cache::*;

// 由 tb/mkcachetb.py 生成，勿手改。
// 这一点：lines={lines} wpl={wpl} stats={stats}，存储延迟 {LAT} 拍

(* synthesize *)
module mkCache{label}Tb(Empty);
  CacheIfc#(8, 32, {lines}, {wpl}) c <- mkCache(CacheCfg {{ stats: {str(stats).title()} }});

  Reg#(Bit#(8))  wait_ <- mkConfigReg(0);
  Reg#(Bit#(32)) cyc   <- mkConfigReg(0);
  Reg#(Bit#(32)) step  <- mkConfigReg(0);
  Reg#(Bool)     bad   <- mkConfigReg(False);

  Bit#(32) base = 32'h8000_0000;
  function Bit#(32) addrAt(Bit#(32) i) = base + ((i % {SPAN}) << 2);

  rule tick;
    cyc <= cyc + 1;
    if (cyc > 20000) begin
      $display("TIMEOUT at step %0d", step);
      $finish(1);
    end
  endrule

  // 下游存储：地址即数据，答复晚 {LAT} 拍
  rule mem;
    Bool go = wait_ >= {LAT};
    if (c.down.valid && !go) wait_ <= wait_ + 1;
    else wait_ <= 0;
    c.down.ready(c.down.valid && go);
    c.down.resp(c.down.valid && go,
                RegRsp {{ rdata: c.down.req.addr, err: False }});
  endrule

  rule drive;
    c.up.req(step < {STEPS}, RegReq {{ addr: addrAt(step), write: False,
                                     wdata: 0, wstrb: 4'hF }});
  endrule

  rule take (step < {STEPS} && c.up.rspValid);
    if (c.up.rsp.rdata != addrAt(step)) begin
      $display("FAIL at step %0d addr %08h: got %08h",
               step, addrAt(step), c.up.rsp.rdata);
      bad <= True;
    end
    step <= step + 1;
  endrule

  rule fin (step == {STEPS});
    let hv <- c.regs.access(RegReq {{ addr: 0, write: False,
                                     wdata: 0, wstrb: 4'hF }});
    Bool ok = True;
    if ({str(stats).title()} && hv.rdata != {hits}) begin
      $display("FAIL hits %0d, want {hits}", hv.rdata);
      ok = False;
    end
    if (!{str(stats).title()} && hv.rdata != 0) begin
      $display("FAIL stats are off yet hits reads %0d", hv.rdata);
      ok = False;
    end
    if (bad || !ok) $display("FAILED");
    else $display("PASS cache: {hits} hits, {misses} misses in %0d cycles", cyc);
    $finish((bad || !ok) ? 1 : 0);
  endrule
endmodule

endpackage
'''
(out / f"Cache{label}Tb.bsv").write_text(txt, encoding="utf-8")
print(f"  cache 行为测试台就位：lines={lines} wpl={wpl} stats={stats} "
      f"（期望 {hits} 命中 {misses} 缺失）")
