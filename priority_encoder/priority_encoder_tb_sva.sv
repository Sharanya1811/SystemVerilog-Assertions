
`timescale 1ns / 1ps
module priority_encoder_tb;
  logic [3:0] in;
  logic [1:0] out;
  logic valid;
  logic clk = 0;

  priority_encoder dut (.in(in), .out(out), .valid(valid));

  always #5 clk = ~clk;

  //Assertions
  // PROBLEM 1:If in == 0, valid == 0 and out == 0.
   property zero_in;
     @(posedge clk) 
     (in==4'b0000) |->(valid==0 && out ==2'b00);
   endproperty
  
  PROBLEM1: assert property (zero_in)
       $display("valid and out are 0 when in =0");
    else
      $error("check valid and out in=0");

   
   // PROBLEM 2:For each single-hot input, the output must match its index
  
  property in_onehot_encoding_index3;
     @(posedge clk)
    (in==4'b1000)  |-> (out==2'b11); 
  endproperty
  PROBLEM23: assert property (in_onehot_encoding_index3)
    $display("onehot encoding is proper with index3");
    else
      $error("check out  and in");
    
  
  property in_onehot_encoding_index2;
     @(posedge clk)
       (in==4'b0100)  |-> (out==2'b10); 
  endproperty
  PROBLEM22: assert property (in_onehot_encoding_index2)
      $display("onehot encoding is proper with index 2");
    else
      $error("check  out  and in");

    
  property in_onehot_encoding_index1;
     @(posedge clk)
             (in==4'b0010)  |-> (out==2'b01); 
  endproperty
   PROBLEM21: assert property (in_onehot_encoding_index1)
        $display("onehot encoding is proper with index 1");
    else
      $error("check out and in");
       
       
  property in_onehot_encoding_index0;
     @(posedge clk)
             (in==4'b0001)  |-> (out==2'b00); 
  endproperty
  PROBLEM20: assert property (in_onehot_encoding_index3)
       $display("onehot encoding is proper with index 0");
    else
      $error("check out  and in");
   
   
    // PROBLEM 3:If multiple inputs are high, out must reflect the highest-priority (leftmost) 1.
   property multiple_high_in;
     @(posedge clk) 
     (in==4'b1100) |->(out ==2'd3);
   endproperty
  
  PROBLEM3: assert property (multiple_high_in)
    $display("when in has multiple high out is taken as priority");
    else
      $error("out is not based on priority");
    
   
  
      // PROBLEM 4:valid should never be 0 when any in[i] == 1..
   property valid_when_in;
     @(posedge clk) 
     $onehot(in)|->valid;
   endproperty
  
  PROBLEM4: assert property (valid_when_in)
    $display("valid is high when in[i]==1");
    else
      $error("in[i]==1 but valid is 0");
    
  
   // PROBLEM 5:When valid == 1, output must always be one of {0,1,2,3}
   property out_with_valid;
     @(posedge clk) 
     valid |->(out inside {[0:3]});
   endproperty
  
  PROBLEM5: assert property (out_with_valid)
    $display("out value is in range{0,1,2,3} when valid");
    else
      $error("out is out of range with valid");
     
   
    
      // PROBLEM 6:Output should be stable for the same input over multiple cycles.
   property stable_out_for_stable_in;
     @(posedge clk) 
     ($stable(in)[*1:$]) |->$stable(out);
   endproperty
  
  PROBLEM6: assert property (stable_out_for_stable_in)
    $display("output is stable for stable input");
    else
      $error("output is not stable when input is stable");
    
      // PROBLEM 7:If in toggles from all-0 to any valid bit, valid must rise in the next cycle.

   property valid_with_valid_in;
     @(posedge clk) 
     $onehot(in) |=> $rose(valid);
   endproperty
  
  PROBLEM7: assert property (valid_with_valid_in)
    $display("when in toggles with valid bit, valid is high");
    else
      $error("valid doesn't change when in toggles valid");
  
  // PROBLEM 8:Output must never be > 3 if in[3] == 1.
   property out_based_on_in;
     @(posedge clk) 
     (in[3]==1) |->(out ==2'd3);
   endproperty
  
  PROBLEM8: assert property (out_based_on_in)
    $display("out is correct based on priority");
    else
      $error("out is wrong");
    
  
 //PROBLEM 9: Output should only change when input changes


   property out_changed_when_in_change;
     @(posedge clk) 
     $changed(in) |->$changed(out);
   endproperty
  
  PROBLEM9: assert property (out_changed_when_in_change)
    $display("out only changed when has changed");
    else
      $error("out changed irrespective of in");
  
      // PROBLEM 10:After a valid input, valid should stay high until in == 0.
   property valid_with_in;
     @(posedge clk) 
     valid until (in==4'b0000);
   endproperty
  
  PROBLEM10: assert property (valid_with_in)
    $display("valid when in is valid");
    else
      $error("invalid check the valid with in");
    
  
 initial begin
    in = 4'b0000; #20;
    in = 4'b0001; #20;
    in = 4'b0010; #20;
    in = 4'b0100; #20;
    in = 4'b1000; #10;
    in = 4'b0100; #40;
    in = 4'b1000; #10;
    in = 4'b1100; #10;
    in = 4'b0110; #10;
    in = 4'b0000; #10;
    in = 4'b1010; #10;
    $finish;
  end
    
    initial begin
       $dumpfile("dump.vcd");
     $dumpvars;
    end
endmodule
