`timescale 1ns / 1ps
 

module tb_comparator;

  logic clk, rst;
  logic [3:0] a, b;
  logic less, equal, greater;

  comparator #(.N(4)) dut (
    .a(a), .b(b),
    .less(less),
    .equal(equal),
    .greater(greater)
  );
  
  
   //Assertions
 
  //PROBLEM 1:Only one of less, equal, or greater should be high at any time.  
 property one_at_a_time;
   @(posedge clk) 
   (less && !equal && !greater) || (!less && equal && !greater) || (!less && !equal && greater) ;
 endproperty
  
  PROBLEM1: assert property(one_at_a_time)
    $display("only one property is high");
           else
             $error("check the comparsion property");
  
  
  //PROBLEM 2:Less than comparison   
 property  a_less_than_b;
   @(posedge clk) 
   a<b |-> (less && !equal && !greater);
 endproperty
  
  PROBLEM2: assert property(a_less_than_b)
    $display(" when a is less than b less is high");
           else
             $error("when a <b check the comparsion  value");
   
   //PROBLEM 3: equals to comparison   
 property  a_equals_b;
   @(posedge clk) 
   (a==b) |-> (!less && equal && !greater);
 endproperty
  
  PROBLEM3: assert property(a_equals_b)
    $display(" when a is equals to b equal bit is high");
           else
             $error("when a==b check the comparsion  value");
             
   //PROBLEM 4:greater than comparison 
 property  a_greater_than_b;
   @(posedge clk) 
   a>b |-> (!less && !equal && greater);
 endproperty
  
  PROBLEM4: assert property(a_greater_than_b)
    $display(" when a is greater than b less is high");
           else
             $error("when a>b check the comparsion  value");
 
  
 //PROBLEM 5: Output must change when input values changed

 property changed_outputs_with_changed_inputs;
   @(posedge clk) disable iff(rst)
   $changed(a)  or  $changed(b) |=> ($changed({less,equal,greater}));
 endproperty
  
  PROBLEM5: assert property(changed_outputs_with_changed_inputs)
    $display("when an input is changed output is changed");
           else
             $error(" when inputs are changed output doesn't change check the comparison ");
  

   //PROBLEM 6:Only one output is HIGH at a time

 property only_one_output;
   @(posedge clk)
   $onehot({less,equal,greater});
 endproperty
  
  PROBLEM6: assert property(only_one_output)
    $display("only one output is high at a time");
           else
             $error("more outputs are high");
   

  // Clock generation
  always #5 clk = ~clk;


  // Stimulus
  initial begin
    clk = 0;
    rst = 1;
    a = 0;
    b = 0;
    #10;
    rst = 0;

    repeat (10) begin
      @(negedge clk);
      a = $urandom_range(0, 15);
      b = $urandom_range(0, 15);
    end

    #20;
    $display("Test Completed");
    $finish;
  end
    
    initial begin
      $dumpfile("dump.vcd");
      $dumpvars();
    end

endmodule
