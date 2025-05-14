
//NOTE:: While checking each assertions comment the necessary tb simulation code

`timescale 1ns / 1ps

`include "assertions.sv"
module shift_register_tb;

  logic clk = 0;
  logic rst, shift_en, load_en;
  logic [7:0] data_in;
  logic [7:0] data_out;

  always #5 clk = ~clk;

  shift_register dut (
    .clk(clk),
    .rst(rst),
    .shift_en(shift_en),
    .load_en(load_en),
    .data_in(data_in),
    .data_out(data_out)
  );
  
  bind shift_register shift_register_assertions sra (.clk(clk),
    .rst(rst),
    .shift_en(shift_en),
    .load_en(load_en),
    .data_in(data_in),
    .data_out(data_out));

  // Stimulus
  initial begin
    rst = 1; shift_en = 0; load_en = 0; data_in = 8'b10000000;
    #12 rst = 0;
    
    // p1+p2+p4+p10
    load_en = 1; data_in = 8'b10000000;
    #10;
    load_en = 0;
    shift_en = 1;
    #70;  // 7 shifts

    
    //p3    
    load_en=1;data_in=8'b0000_0000;
    #10 load_en=0;
    
    repeat(5) begin
      shift_en=1; #10; end 
    shift_en=0;
    
    
     //p5 
    load_en=1;data_in=8'b1000_0000;
    #20 load_en=0;
    shift_en=1; 
    #20 shift_en=0;
    
    
    //p6
    load_en = 1; #30; load_en = 0;
    
    
    //p7
    shift_en = 1; #10 shift_en = 0;
    #20; 
   
   //p8
   #25;
   
   
   //p9
   #20
   
   //p10
    load_en=1;data_in=8'b1010_0001;   
    #20 load_en=0;

     
    $finish;
  end
 initial begin
   $dumpfile("dump.vcd");
   $dumpvars;
 end
endmodule
