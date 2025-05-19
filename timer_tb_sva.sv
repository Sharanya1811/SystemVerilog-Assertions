`timescale 1ns / 1ps
 
module tb_timer;
  logic clk, rst, start;
  logic [3:0] load_val;
  logic done;
  logic [3:0] count;

  timer dut (
    .clk(clk),
    .rst(rst),
    .start(start),
    .load_val(load_val),
    .done(done),
    .count(count)
  );

  
  
  //Assertions
  
  //PROBLEM 1:Timer loads only when start is asserted in IDLE.
  
 property timer_load;
   @(posedge clk) disable iff(rst)
   (start && dut.state==dut.IDLE) |=>( count==load_val);
 endproperty
  
  PROBLEM1: assert property(timer_load)
    $display("timer is loaded when start and state is IDLE");
           else
             $error("check for start and state for timer load");
   
   
  //PROBLEM 2:Countdown begins in the cycle after start is asserted.

  
 property countdown;
   @(posedge clk) disable iff (rst)
   (dut.state==dut.RUN && start) |=> (count==($past(count)-1'b1));
 endproperty
  
  PROBLEM2: assert property(countdown)
    $display("count down has started when start is asserted");
           else
             $error("count down started before count down");
         
 //PROBLEM 3:done must only be high for one cycle after countdown reaches 0.

 property done_for_one_cycle;
   @(posedge clk) disable iff(rst)
   ( count==0 && start) |=> done ##1 !done;
 endproperty
  
  PROBLEM3: assert property(done_for_one_cycle)
    $display("done is high for only clock cycle");
           else
             $error(" done is high for more clocks");
  

   //PROBLEM 4:During RUN state, count must decrease by 1 each cycle.
  
 property count_decrement;
   @(posedge clk) disable iff(rst)
   ((dut.state== dut.RUN) && start) |=>(count==$past(count-1'b1))[*1];
 endproperty
  
  PROBLEM4: assert property(count_decrement)
    $display("count is decrement by 1 each clock cycle");
           else
             $error("count is decrementing more");
   
    
      //PROBLEM 5: If load_val is 0 and start is high, done should go high immediately.
  
 property done_when_zero_load;
   @(posedge clk) disable iff(rst)
   (load_val==0 && start) |=> done;
 endproperty
  
  PROBLEM5: assert property(done_when_zero_load)
    $display("done is high when load_val is 0");
           else
             $error("done is not high when load is 0");
   
      //PROBLEM 6:Timer must not transition to RUN unless start is high.
  
 property state_of_timer;
   @(posedge clk) disable iff(rst)
   (start && count !=0) |=> dut.state==dut.RUN;
 endproperty
  
  PROBLEM6: assert property(state_of_timer)
    $display("timer state is not RUN high unless start is high");
           else
             $error("timer state is RUN with low start ");
  
    
      //PROBLEM 7:If rst is high, state must immediately go to IDLE and count to 0.
  
 property reset_states;
   @(posedge clk) 
   rst |-> (dut.state==dut.IDLE && count==0);
 endproperty
  
  PROBLEM7: assert property(reset_states)
    $display("upon reset state is IDLE and count is 0");
           else
             $error("state is not IDLE or count is not 0 upon reset");
   
 
      //PROBLEM 8: Once countdown starts, count must never increase.

   
 property count_down;
   @(posedge clk) disable iff(rst)
   ( start && load_val!=0) |=> (count< $past(count));
 endproperty
  
  PROBLEM8: assert property(count_down)
    $display("countdown is never increased when timer started");
           else
             $error(" when timer started countdown was increased");
    
    
   
      //PROBLEM 9: If start is asserted while the timer is already in the RUN state, the count value must not reload.
  
 property no_reload_during_timer;
   @(posedge clk) disable iff(rst)
   (start && dut.state==dut.RUN)|=> (count != load_val);
 endproperty
  
  PROBLEM9: assert property(no_reload_during_timer)
    $display("counter not reloaded when timer started");
           else
             $error("counter is reloaded when timer is started");
  
        //PROBLEM 10:Illegal: done and start should never be high in same cycle.

  
 property illegal_condition;
   @(posedge clk) disable iff(rst)
   !(done && start) ;
 endproperty
  
  PROBLEM10: assert property(illegal_condition)
    $display("done and start are not high at a time");
           else
             $error("done and start are high at a time");
     
    
  // Clock generation
  initial begin
    clk = 0;
    forever #5 clk = ~clk;
  end

  // Stimulus
  initial begin
    rst = 1; start = 0; load_val = 0;
    #5 rst = 0;
     
    
    load_val =4'd10;
    start=1;#10;
    start=0;
    
    // Load 5, expect countdown
    load_val = 4'd5;
    start = 1; #40;
    start = 0;

    #60;

    // Load 0, edge case
    load_val = 4'd0;
    start = 1; #10;
    start = 0;

    #20;

    // Load 3
    load_val = 4'd3;
    start = 1; #10;
    start = 0;

    #50;

    $finish;
  end
  
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars();
  end
endmodule
