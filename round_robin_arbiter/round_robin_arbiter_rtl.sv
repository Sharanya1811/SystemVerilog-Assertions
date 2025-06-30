
module round_robin_arbiter #(parameter N=4)(
    input  logic        clk,
    input  logic        reset,
  input  logic [N-1:0]  req,   
  output logic [N-1:0]  grant  
);
  
  logic [(N/2-1):0] current_priority;

  always_ff @(posedge clk or negedge reset) begin
    if (!reset) begin
      current_priority <= 2'b00;
      grant<=0;
    end
    else if (|req) begin
      repeat (4) begin
        if (req[current_priority]) begin
          grant <= 4'b0001 << current_priority;
          current_priority <= current_priority + 2'd1;
          break;
        end
        current_priority <= current_priority + 2'd1;
      end
    end else begin
      grant <= 4'b0000;
    end
  end

endmodule
