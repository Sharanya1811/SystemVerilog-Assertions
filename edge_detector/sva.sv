module edge_detector_assertions(input logic clk, rst, signal_in,edge_out);
 

  //PROBLEM 1: Assert that edge_out is high only for one cycle per rising edge of signal_in

  property edge_out_functionality;
    @(posedge clk) disable iff(rst)
    $rose(signal_in) |=> edge_out ##1 !edge_out;
  endproperty 
    
  PROBLEM1: assert property (edge_out_functionality)
    $display("edge_out functionality has been asserted properly ");
             else 
               $error("check for edge_out functionality is wrong");
 
 
  //PROBLEM 2:  edge_out should never go high during or immediately after reset

  property no_edge_on_reset;
        @(posedge clk) 
     rst |=> !edge_out;
  endproperty
  
    
  PROBLEM2: assert property (no_edge_on_reset)
    $display("edge_out is working properly after reset");
             else 
               $error("check edge_out after reset");
              
 

  // PROBLEM 3: edge_out only goes high when signal_in rises (not on fall)
  
  property only_rise_edge_detection;
       @(posedge clk) disable iff(rst)
    $rose(signal_in) |=> edge_out;
  endproperty
            
  PROBLEM3: assert property (only_rise_edge_detection)
    $display("edge_out goes high when signal_in rises");
             else 
               $error("edge_out is going high when signal_in is not rising");



  // PROBLEM 4: Two rising edges must not occur within 3 cycle
  property space_between_rising;
       @(posedge clk) disable iff(rst)
    edge_out |=> !edge_out[*2];
  endproperty
  
  PROBLEM4: assert property (space_between_rising)
    $display("two rising edges not occured in 3 cycles");
             else 
               $error("two rising edges occured in 3 cycles");
         
 
  // PROBLEM 5:During reset, signal_d and edge_out must always be 0
  property reset_state_check;
       @(posedge clk) 
    rst |=> (dut.signal_d ==0 && edge_out==0);
  endproperty
            
  PROBLEM5: assert property (reset_state_check)
    $display("on Reset signal conditions are valid ");
             else 
               $error("checck signals on reset");
              

        
  // PROBLEM 6:After edge_out is high, signal_in must stay high for at least 1 cycle
  property signal_hold_after_edge;
       @(posedge clk) disable iff(rst)
    edge_out |=> signal_in[*1];
  endproperty
                       
    PROBLEM6: assert property (signal_hold_after_edge)
           $display("signal is high for 1 cycle after edge_out");
             else 
               $error("change of signal_in afetr edge_out");

     //PROBLEM 7: If signal_in is stable for 5 cycles, edge_out remains 0
  property stable_input_no_edge;
    @(posedge clk) disable iff(rst)
    $stable(signal_in)[*5] |=> !edge_out;
  endproperty
  
         PROBLEM7: assert property(stable_input_no_edge)
                $display("with stable signal_in edge_out is 0");
               else 
                 $error("toggling of edge_out with stable signal_in");
                  

//PROBLEM 8: For every edge_out pulse, signal_in must have been 0 in the previous cycle and now 1
 
  property valid_edge_detection;
     @(posedge clk) disable iff(rst)
    edge_out |=> (signal_in && ($past(signal_in)==0));
  endproperty
       
  PROBLEM8: assert property (valid_edge_detection)
    $display(" valid edge_out on signal_in");
            else 
              $error("invalid edge_out on signal_in");
 
  //PROBLEM 9:If signal_in becomes 1 and stays high, edge_out pulses only once

 
  property pulse_only_on_first_rise;
     @(posedge clk) disable iff(rst)
    signal_in |=> ($stable(signal_in) && edge_out) ##1 !edge_out;
  endproperty
       
        PROBLEM9: assert property (pulse_only_on_first_rise)
          $display("edge_out pulsed only once");
             else 
               $error("edge_out pulsing multiple times on first rise");  

  
endmodule
