module priority_encoder (
  input  logic [3:0] in,      // 4-bit input
  output logic [1:0] out,     // Encoded 2-bit output
  output logic       valid    // High if any input is 1
);

  always_comb begin
    valid = |in;  // OR reduction
    unique casez (in)
      4'b1???: out = 2'd3; // Bit 3 highest priority
      4'b01??: out = 2'd2;
      4'b001?: out = 2'd1;
      4'b0001: out = 2'd0;
      default: out = 2'd0;
    endcase
  end
endmodule
