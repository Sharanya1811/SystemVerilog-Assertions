module alu (
  input  logic        clk,
  input  logic        rst,
  input  logic [2:0]  opcode,
  input  logic [7:0]  a,
  input  logic [7:0]  b,
  output logic [15:0] result,
  output logic        valid
);

  always @(posedge clk or posedge rst) begin
    if (rst) begin
      result <= 0;
      valid  <= 0;
    end else begin
      valid <= 1;
      unique case (opcode)
        3'b000: result <= a + b;
        3'b001: result <= a - b;
        3'b010: result <= a & b;
        3'b011: result <= a | b;
        3'b100: result <= a ^ b;
        3'b101: result <= a * b;
        default: begin
          result <= 16'hDEAD;
          valid  <= 0;
        end
      endcase
    end
  end
endmodule
