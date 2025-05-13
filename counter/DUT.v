module counter4bit (
  input  logic        clk,
  input  logic        rst,
  input  logic        enable,
  input  logic        load,
  input  logic [3:0]  load_val,
  output logic [3:0]  count_val
);

  always @(posedge clk or posedge rst) begin
    if (rst)
      count_val <= 0;
    else if (load)
      count_val <= load_val;
    else if (enable)
      count_val <= count_val + 1;
  end

endmodule
