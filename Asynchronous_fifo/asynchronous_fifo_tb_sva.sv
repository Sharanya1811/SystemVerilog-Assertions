`timescale 1ns / 1ps
 

module tb_sync_fifo;

  logic clk, rst, wr_en, rd_en;
  logic [7:0] data_in, data_out;
  logic full, empty;

  synchronous_fifo dut (
    .clk(clk),
    .rst(rst),
    .wr_en(wr_en),
    .rd_en(rd_en),
    .data_in(data_in),
    .data_out(data_out),
    .full(full),
    .empty(empty)
  );
  
  
  //Assertions
 
  //PROBLEM 1:FIFO must not write when full is high.  
 property no_write_when_full;
   @(posedge clk) disable iff(rst)
   full |=> (dut.wr_ptr == $past(dut.wr_ptr));
 endproperty
  
  PROBLEM1: assert property(no_write_when_full)
    $display("write not happened when full");
           else
             $error("write happened when full");
  
  
  //PROBLEM 2:FIFO must not read when empty is high.

  
 property  no_read_when_empty;
   @(posedge clk) disable iff (rst)
   empty |=> (dut.rd_ptr== $past(dut.rd_ptr));
 endproperty
  
  PROBLEM2: assert property(no_read_when_empty)
    $display("no read when empty");
           else
             $error("ready happened when fifo is empty");
    
 //PROBLEM 3:If FIFO is full and no reads happen, full stays asserted

 property full_stability;
   @(posedge clk) disable iff(rst)
   full && !rd_en |-> full;
 endproperty
  
  PROBLEM3: assert property(full_stability)
    $display("full is stable when no reads happened");
           else
             $error(" full is not stable when no reads happen");
  

   //PROBLEM 4:When writing 4 times in a row to an empty FIFO, the FIFO must be full.

 property full_state;
   @(posedge clk) disable iff(rst)
   //((dut.wr_ptr==((dut.DEPTH)-1)) && (dut.rd_ptr==0)) |->(full);
   wr_en[*4] |-> full;
 endproperty
  
  PROBLEM4: assert property(full_state)
    $display("for continous write upto depth full is asserted");
           else
             $error("when depth has reached full is not asserted");
   
  
      //PROBLEM 5:After 4 reads without writes, the FIFO must be empty
  
 property empty_state;
   @(posedge clk) disable iff(rst)
  // (dut.wr_ptr==dut.rd_ptr)|-> empty;
   rd_en[*4]|-> empty;
 endproperty
  
  PROBLEM5: assert property(empty_state)
    $display("4 complete reads happened so empty is high");
           else
             $error("empty is not high after the fifo is empty");
   
      //PROBLEM 6:dout should remain stable if rd_en is low.
  
 property no_read_data_out;
   @(posedge clk) disable iff(rst)
   !rd_en |-> $stable(data_out);
 endproperty
  
  PROBLEM6: assert property(no_read_data_out)
    $display("data_out is stable when rd_en is low");
           else
             $error("unstable data_out when rd_en is low ");
  
  
      //PROBLEM 7:If wr_en and rd_en are asserted together, and FIFO is neither full nor empty, data written must not be lost.
  
 property enables_high_condition;
   @(posedge clk) disable iff(rst)
   (wr_en && rd_en && !full && !empty) |-> $stable(data_out);
 endproperty
  
  PROBLEM7: assert property(enables_high_condition)
    $display("when both enbales are high then fifo is neither empty or full and written data is not lost");
           else
             $error("check the fifo states and data_out when both enbales are high");
  
 
      //PROBLEM 8: dout must match the first din value after one write and one read cycle.
 
 property fifo_data;
   @(posedge clk) disable iff(rst)
   ##[1:$] (wr_en && full && !rd_en)|-> ##[1:$](rd_en [*1]) ##1 (data_out== dut.mem[0]);
 endproperty
  
  PROBLEM8: assert property(fifo_data)
    $display("first read data matched with first match of data_in");
           else
             $error("data_out doesn't match with first match in data_in ");
   
   
   
     //PROBLEM 9:when wr_en and rd_en both high FIFO is not full or empty 
  
 property enables_when_full_or_empty;
   @(posedge clk) disable iff(rst)
   wr_en && rd_en |-> !full || !empty;
 endproperty
 
  PROBLEM9: assert property(enables_when_full_or_empty)
    $display("rd_en and wr_en are high fido is neither full nor empty");
           else
             $error("fifo is full or empty when enables are high");
 
  //PROBLEM 10:Reset (rst) must cause empty to assert
  
 property reset_condition;
   @(posedge clk) 
   rst|-> empty;
 endproperty
  
  PROBLEM10: assert property(reset_condition)
    $display("empty is high and data_out is 0 or undefined upon reset");
           else
             $error("check empty or data_out upon reset");
   

  initial clk = 0;
  always #5 clk = ~clk;

  initial begin
    rst = 1; wr_en = 0; rd_en = 0; data_in = 0;
    #10 rst = 0;

    // Write 5 values
    repeat (5) begin
      @(posedge clk);
      wr_en = 1;
      data_in = $urandom_range(1, 255);
    end
    @(posedge clk); wr_en = 0;

    // Read 2 values
    repeat (2) begin
      @(posedge clk);
      rd_en = 1;
    end
    @(posedge clk); rd_en = 0;

    // Write 2 more values
    repeat (2) begin
      @(posedge clk);
      wr_en = 1;
      data_in = $urandom_range(1, 255);
    end
    @(posedge clk); wr_en = 0;

    // Read remaining values
    repeat (4) begin
      @(posedge clk);
      rd_en = 1;
    end
    @(posedge clk); rd_en = 0;
    
    repeat (2) begin
      wr_en = 1;
      data_in = $urandom_range(1, 255);
      rd_en=1;
    end
    
    #30 $finish;
  end
  
  initial begin
  
   $dumpfile("dump.vcd");
    $dumpvars;
  end
endmodule
  
