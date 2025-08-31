// SystemVerilog Assertions generated from WaveDrom
// Generated on 2025-08-31T02:57:35.640Z
// Generator: WaveformToSVAGenerator v2.0 (Enhanced)
// Total properties: 2
// Statistics: Sharp=2, Splines=0, Bidirectional=0

module generated_assertions(
  input logic clk,
  input logic rst_n,
  input logic req,
  input logic ack,
  input logic enable
);

  // ========================================
  // Generated Properties
  // ========================================

  property edge_d_to_f_0;
  @(posedge clk) disable iff (!rst_n)
  $rose(req) |=> ##1 (ack && enable);
endproperty
edge_d_to_f_0_a: assert property(edge_d_to_f_0)
  else $error("[SVA] Timing violation: req(d) -> ack(f) failed at cycle %0d with operator '->' (expected delay:  ##1)", ($time / $realtime));

  property edge_f_to_e_1;
  @(posedge clk) disable iff (!rst_n)
  ack |=> ##1 req;
endproperty
edge_f_to_e_1_a: assert property(edge_f_to_e_1)
  else $error("[SVA] Timing violation: ack(f) -> req(e) failed at cycle %0d with operator '-|>' (expected delay:  ##1)", ($time / $realtime));

endmodule
