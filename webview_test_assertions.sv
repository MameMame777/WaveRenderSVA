// SystemVerilog Assertions generated from WaveDrom edge/node/comment syntax
// Generated on 2025-09-01T14:01:01.054Z
// Using WaveDrom Sharp Lines and Splines for timing relationships

// ========================================
// WaveDrom-generated SystemVerilog Assertions
// Generated: 2025-09-01T14:01:01.054Z
// Sharp Lines: Strict timing constraints
// Splines: Flexible timing constraints
// ========================================

module wavedrom_assertions (
  input logic clk,
  input logic rst_n,
  input logic req,
  input logic ack,
  input logic data
);

  // ========================================
  // Edge-based Property Definitions
  // ========================================

  property edge_a_to_c_0;
    @(posedge clk) disable iff (!rst_n)
    $rose(req) |=> ##[0:1] ack;
  endproperty
  edge_a_to_c_0_a: assert property(edge_a_to_c_0)
    else $error("[SVA] Timing violation: req(a) -> ack(c) failed at cycle %0d with operator '~>' (expected delay: ##[0:1])", ($time / $realtime));

  property edge_c_to_e_1;
    @(posedge clk) disable iff (!rst_n)
    ack |=> $changed(data);
  endproperty
  edge_c_to_e_1_a: assert property(edge_c_to_e_1)
    else $error("[SVA] Timing violation: ack(c) -> data(e) failed at cycle %0d with operator '->' (expected delay: 0)", ($time / $realtime));

  property edge_b_to_d_2;
    @(posedge clk) disable iff (!rst_n)
    req |=> ack;
  endproperty
  edge_b_to_d_2_a: assert property(edge_b_to_d_2)
    else $error("[SVA] Timing violation: req(b) -> ack(d) failed at cycle %0d with operator '-|>' (expected delay: 0)", ($time / $realtime));

  // Comment-derived properties
endmodule