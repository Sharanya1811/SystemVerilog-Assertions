module edge_detector (
  input  logic clk,
  input  logic rst,
  input  logic signal_in,
  output logic edge_out
);
  logic signal_d;

  always_ff @(posedge clk or posedge rst) begin
    if (rst) begin
      signal_d <= 0;
      edge_out <= 0;
    end else begin
      signal_d <= signal_in;
      edge_out <= signal_in & ~signal_d; // rising edge
    end
  end
endmodule
