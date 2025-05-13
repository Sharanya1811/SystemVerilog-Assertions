
//NOTE Please check each assertion individually by making necessary changes in TB
module counter_assertions(input logic clk, rst, enable, load, [3:0] count_val, load_val);
 
  //PROBLEM 1: Write an assertion to detect if load is high while enable is also high. This is forbidden in the spec
 
  property forbidden_load;
    @(posedge clk) disable iff(rst)
    !( load && enable);  
  endproperty 
    
  PROBLEM1: assert property (forbidden_load)
               $display("Forbidden load has executed properly ");
             else 
               $error("Not executed properly check the error");
  
  
  //PROBLEM 2:  Assert that whenever load and enable are both high, the counter must take load_val and not increment

  property load_priority_over_enable;
    logic [3:0] d;
       @(posedge clk) disable iff(rst)
    (load && enable , d=count_val) |=>  (count_val==load_val  && count_val!=d+1);  
  endproperty
  
    
    PROBLEM2: assert property (load_priority_over_enable)
             $display("load priorty is executed over enable");
             else 
             $error("load priorty is not executed over enable");
              
  
  
  //PROBLEM 3: Detect if count remains unchanged for 4 or more consecutive clock cycles while enable is high and load is low.
 
  property stall_detection;
       @(posedge clk) disable iff(rst)
    (enable && !load ) |->  $stable(count_val)[->4] ;
  endproperty
       
      PROBLEM3: assert property (stall_detection)
                $display("stall detection happend");
               else 
               $error("stall detection is not happend");
  
  
  // PROBLEM 4:  Write an assertion that fails if count ever increases by more than 1 between two consecutive clock edges
  
  property skipped_values;
       @(posedge clk) disable iff(rst)
    (enable && !load) |=> (count_val == $past(count_val)+1);
  endproperty
            
        PROBLEM4: assert property (skipped_values)
                  $display("counter incremented properly");
                  else 
                  $error("counter incremented properly");
  
  // PROBLEM 5: Detect if count goes from 15 (max) directly to a value other than 0, without a load
  property count_wrap_check;
       @(posedge clk) disable iff(rst)
    (count_val== 4'd15 && !load && enable) |=> (count_val==0 && !load && enable);
  endproperty
  
          PROBLEM5: assert property (count_wrap_check)
                    $display("counter value wrapping done properly");
                   else 
                  $error("check the counter value wrapping");
          
 
  // PROBLEM 6: Write an assertion that fails if reset happens when count is less than 5.
  property premature_reset;
       @(posedge clk) 
     rst |-> count_val<5;
  endproperty
            
            PROBLEM6: assert property (premature_reset)
                     $error("reset happened based on counter value");
                     else 
                     $display("no reset happened");
              

          
  // PROBLEM 7:After load is asserted, count must equal load_val within 1 clock cycle.
  property delayed_load;
       @(posedge clk) disable iff(rst)
    load |=> count_val == $past(load_val);
  endproperty
                       
          PROBLEM7: assert property (delayed_load)
                   $display("delayed_load asserted properly");
                   else 
                   $error("check property-8");
  
   // PROBLEM 8:Detect if load stays high for more than 2 consecutive cycles.
  property load_glitch;
       @(posedge clk) disable iff(rst)
    load[*3];
  endproperty
            
         PROBLEM8: assert property(load_glitch)
                    $error("load glitch detected ");
                   else 
                  $display("load has executed properly");
  
endmodule
