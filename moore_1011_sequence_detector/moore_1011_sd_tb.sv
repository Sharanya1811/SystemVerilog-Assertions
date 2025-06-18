`timescale 1ns / 1ps
 

module tb_moore_sequence_detector;

  logic clk, rst, din;
  logic dout;

  moore_sequence_detector_1011 dut (
    .clock(clk),
    .reset(rst),
    .din(din),
    .dout(dout)
  );

     
  
  //PROBLEM 1: Output must only be 1 when correct sequence ends
 property correct_sequence;
   @(posedge clk) disable iff(!rst)
   (din==1 ##1 din==0 ##1 din==1 ##1 din==1) |=>##1 (dout==1) ;
 endproperty
  
  PROBLEM1: assert property(correct_sequence)
    $display("observed the correct sequence");
           else
             $error("no correct sequence is at time=%t",$time);
  
    

  //PROBLEM 2:  Output should never be 1 outside of S4
 property no_out_of_state_output;
   @(posedge clk) 
   (dout) |-> ($past(dut.state)==dut.s4);
 endproperty
  
  PROBLEM2: assert property(no_out_of_state_output)
    $display("dout is high only when state is s4");
           else
             $error("check the state and dout ");
  
  
    
    
 
  //PROBLEM 3:   No detection on incorrect sequences like 1001, 1111 etc.
 property incorrect_input;
   @(posedge clk) 
   (din==1 ##1 din==0 ##1 din==1 ##1 din==1) |=> ##1 (dout==0) ;
 endproperty
  
  PROBLEM3: assert property(incorrect_input)
    $display("dout is high when sequence is incorrect");
           else
             $error("incorrect detection");
  
     
  //PROBLEM 4:Ensure that after reset, the FSM returns to the initial state (s0) regardless of current state or input

 property reset_state;
   @(posedge clk)
   !rst |=> dut.state==dut.s0;
 endproperty
  
  PROBLEM4: assert property(reset_state)
    $display("on reset state is at s0");
           else
             $error("check the states on reset");
  
   
    
 
  //PROBLEM 5:Ensure that two consecutive sequences of 1011 with 1-bit overlap (like 1011011) produce two separate detections

  sequence seq1;
    din==1 ##1 din==0 ##1 din==1 ##1 din==1;
  endsequence
  

  
 property two_consecutive_sd;
   @(posedge clk) 
   seq1 |->##1 din==0 ##1 din==1 ##1 din==1 ;
 endproperty
  
  PROBLEM5: assert property(two_consecutive_sd)
    $display("only one property is high");
           else
             $error("check the comparsion property");

  
  // Clock generation
  initial clk = 0;
  always #5 clk = ~clk;

  initial begin
    rst = 0;
    din = 0;
    #12 rst = 1;

    // Input stream: 1 0 1 1 -> detect at end
    repeat (2) @(posedge clk); din = 1;
    repeat (1) @(posedge clk); din = 0;
    repeat (1) @(posedge clk); din = 1;
    repeat (1) @(posedge clk); din = 1; // Detect here
 

    repeat (1) @(posedge clk); din = 0; // clear
    repeat (1) @(posedge clk); din = 1;
    repeat (2) @(posedge clk); din = 1; // Clear
    repeat (1) @(posedge clk); din = 0;
    repeat (1) @(posedge clk); din = 1;
    repeat (1) @(posedge clk); din = 1; // Second detect

    repeat (2) @(posedge clk);
    $finish;
  end
initial begin
  $dumpfile("dump.vcd");
  $dumpvars;
  $monitor("state=%d,dout=%d,din=%d",dut.state,dout,din);
end

endmodule


