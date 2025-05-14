module shift_register (
  input  logic        clk,
  input  logic        rst,
  input  logic        shift_en,
  input  logic        load_en,
  input  logic [7:0]  data_in,
  output logic [7:0]  data_out
);

  always_ff @(posedge clk or posedge rst) begin
    if (rst)
      data_out <= 8'b0;
    else if (load_en)
      data_out <= data_in;
    else if (shift_en)
      data_out <= {data_out[6:0], 1'b0};  // Left shift by 1, insert 0
  end

endmodule
