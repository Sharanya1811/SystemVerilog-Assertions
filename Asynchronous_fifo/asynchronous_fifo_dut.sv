module synchronous_fifo #(parameter WIDTH=8,parameter DEPTH=4) (
  input  logic        clk,
  input  logic        rst,
  input  logic        wr_en,
  input  logic        rd_en,
  input  logic [(WIDTH-1):0]  data_in,
  output logic  [(WIDTH-1):0] data_out,              
  output logic        full,
    output logic  empty
);
  reg [(WIDTH-1):0] mem[(DEPTH-1):0];
  logic [((DEPTH/2)-1):0] wr_ptr,rd_ptr;
  int count=0;
  
 
  always @(posedge clk or posedge rst) begin
    if(rst) begin
      wr_ptr<=0;
      rd_ptr<=0;
      count<=0;
    end
    else begin
      if(wr_en && !full) begin
        mem[wr_ptr]<=data_in;
        wr_ptr<=wr_ptr+1'b1;
       count<=count+1'b1;
      end
      else if(rd_en && !empty) begin
        data_out<=mem[rd_ptr];
        rd_ptr<=rd_ptr+1;
        count<=count-1'b1;
      end 
    end
  end
  
  assign full = ((wr_ptr==(DEPTH-1))  && (rd_ptr==0)) ? 1: 0;
  assign empty =(wr_ptr===rd_ptr)?1:0;
  

endmodule
