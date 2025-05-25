module comparator #(
  parameter N = 4
)(
  input  logic [N-1:0] a,
  input  logic [N-1:0] b,
  output logic         less,
  output logic         equal,
  output logic         greater
);

  always_comb begin
    if (a < b) begin
      less    = 1;
      equal   = 0;
      greater = 0;
    end else if (a == b) begin
      less    = 0;
      equal   = 1;
      greater = 0;
    end else begin
      less    = 0;
      equal   = 0;
      greater = 1;
    end
  end

endmodule
