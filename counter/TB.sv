  //NOTE FOR TESTING EACH ASSERTION COMMENT ALL THE ASSERTION RELATED SIMULATION CODE

`timescale 1ns/1ps
`include "assertions.sv"

module tb_counter;

  logic clk = 0;
  logic rst;
  logic enable;
  logic load;
  logic [3:0] load_val;
  logic [3:0] count_val;

  // Clock Generation
  always #5 clk = ~clk;

  // DUT Instantiation
  counter4bit dut (.clk(clk), .rst(rst), .enable(enable),.load(load), .load_val(load_val), .count_val(count_val));
  
  // binding sv file in tb
  //syntax
  /* bind <dut_module name or dut_instance name> <assertion_module_name>    <assertion_instance> <signals>;*/
  
  bind counter4bit counter_assertions counter_sva (.clk(clk), .rst(rst), .enable(enable),.load(load), .load_val(load_val), .count_val(count_val));
  
  
  // Test Sequence
  initial begin
    $dumpfile("counter_wave.vcd"); 
    $dumpvars(0, tb_counter);

    // Initial values
    rst = 0; enable = 0; load = 0; load_val = 0;

    // Reset the counter
    rst = 1; #10;
    rst = 0;

    // Enable counting for a few cycles
    enable = 1;
    repeat (5) @(posedge clk);
    
    //for forbidden load test
    load_val = 7;
    load = 1;
    @(posedge clk);
    load = 0;

    // Let it increment from loaded value
    repeat (3) @(posedge clk);
    

    // Force stall by disabling enable
    enable = 0;
    repeat (5) @(posedge clk);

    // Try a load without enable
    load_val = 10;
    load = 1;
    @(posedge clk);
   load = 0;

    // Wrap from 15 to 0 scenario
    load_val = 14;
    load = 1;
    @(posedge clk);
    load = 0;
    enable = 1;
    repeat (3) @(posedge clk); // Wrap around will happen here

    // Hold load high for too long (glitch case)
    load_val = 5;
    load = 1;
    repeat (4) @(posedge clk); // Load high for 4 cycles
    load = 0;

    // Premature reset
    rst = 1;
    @(posedge clk);
    rst = 0;
    


  // Finish
    repeat (3) @(posedge clk);
   
    $finish;
  end

endmodule
