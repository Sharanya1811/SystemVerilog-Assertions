
`timescale 1ns / 1ps

`include "assertions.sv"
module edge_detector_tb;
 logic clk = 0, rst, signal_in, edge_out;

  edge_detector dut (.clk(clk), .rst(rst), .signal_in(signal_in), .edge_out(edge_out));

    bind edge_detector edge_detector_assertions sra (.clk(clk),.rst(rst), .signal_in(signal_in), .edge_out(edge_out));
  
  always #5 clk = ~clk;

  // Add other assertions here based on the 10 questions…

  initial begin
    // Reset
    rst = 1; signal_in = 0; #12;
    rst = 0;

    // Single rising edge
    signal_in = 0; #10;
    signal_in = 1; #10;
    signal_in = 1; #10;
    signal_in = 0; #10;

    // Rapid toggling
    signal_in = 1; #10;
    signal_in = 0; #10;
    signal_in = 1; #10;
    signal_in = 0; #10;

    // Stay high
    signal_in = 1; #100;

    $finish;
  end
endmodule
 
