// SystemVerilog Assertions generated from WaveDrom
// Generated on 2025-08-31T03:13:18.986Z
// Generator: WaveformToSVAGenerator v2.0 (Enhanced)
// Total properties: 2
// Statistics: Sharp=1, Splines=1, Bidirectional=0

module generated_assertions(
  input logic clk,
  input logic rst_n,
  input logic req,
  input logic ack,
  input logic data,
  input logic enable
);

  // ========================================
  // Generated Properties
  // ========================================

  property edge_a_to_b_0;
  @(posedge clk) disable iff (!rst_n)
  $rose(req) |=> ##1 (ack && enable);
endproperty
edge_a_to_b_0_a: assert property(edge_a_to_b_0)
  else $error("[SVA] Timing violation: req(a) -> ack(b) failed at cycle %0d with operator '->' (expected delay:  ##1)", ($time / $realtime));

  property edge_c_to_d_1;
  @(posedge clk) disable iff (!rst_n)
  $changed(data) |=> ##[2:5] $changed(data);
endproperty
edge_c_to_d_1_a: assert property(edge_c_to_d_1)
  else $error("[SVA] Timing violation: data(c) -> data(d) failed at cycle %0d with operator '~>' (expected delay:  ##[2:5])", ($time / $realtime));

endmodule
