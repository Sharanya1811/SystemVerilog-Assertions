module decoder_3to8 (
  input logic [2:0] in,
  input logic       en,
  output logic [7:0] out
);
  always_comb begin
    if (en)
      out = 8'b00000001 << in;
    else
      out = 8'b00000000;
  end
endmodule
