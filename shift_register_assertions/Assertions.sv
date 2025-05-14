
// NOTE:: comment the each individual assertions condition while checking other as per tb simulation code
module shift_register_assertions(input logic clk, rst, shift_en, load_en, [7:0] data_in, [7:0] data_out);
 
  
  //PROBLEM 1: Detect if load_en and shift_en are high in the same cycle. This is illegal.

  property forbidden_condition;
    @(posedge clk) disable iff(rst)
    !( shift_en && load_en);  
  endproperty 
    
  PROBLEM1: assert property (forbidden_condition)
               $display("Forbidden load has executed properly ");
             else 
               $error("Not executed properly check the error");
  
  
  //PROBLEM 2: If load_en is high in a cycle, the next 2 cycles must NOT assert shift_en to prevent premature shifting.

  property shift_after_load;
        @(posedge clk) disable iff(rst)
    load_en |=> (!shift_en)[*2];
  endproperty
  
    
 PROBLEM2: assert property (shift_after_load)
          $display("shifting after load is done");
          else 
          $error("shifting after load is not done");
              
 
  
  //PROBLEM 3: If shift_en is high for 5 or more consecutive cycles and data_out does not change, raise an error.

 sequence seq;
   shift_en[*5];
 endsequence
      
 property shift_stuck;
     @(posedge clk) disable iff(rst)
    seq  |-> !($changed(data_out)); 
 endproperty
       
PROBLEM3: assert property (shift_stuck)
        $error("shift_en  got stuck");
       else 
        $display("shift_en not got stuck and change of data is proper");
  
  
  // PROBLEM 4: If load_en loads data_in = 8'b1000_0000, verify that after exactly 7 shifts, data_out == 8'b0000_0000.
  
  property data_out_check;
     @(posedge clk) disable iff(rst)
    (load_en && data_in== 8'b1000_0000) |-> shift_en[*7] ##1 (data_out==8'b0000_0000);
  endproperty
            
  PROBLEM4: assert property (data_out_check)
          $display("data shifting is proper");
         else 
        $error("data shifting is not proper");



  // PROBLEM 5: Whenever shift_en is asserted, ensure that the MSB (bit 7) of data_out becomes 0 in the next cycle.
  property msb_check;
       @(posedge clk) disable iff(rst)
    shift_en |=> (data_out[7]==0);
  endproperty
  
 PROBLEM5: assert property (msb_check)
            $display("msb value is correct and shift is correct");
          else 
          $error("msb value is not correct check the dut code");
         
 
  // PROBLEM 6: If load_en is high for 3+ cycles in a row, it should raise an error (invalid condition).
  property load_lock_check;
       @(posedge clk) 
    load_en[*3];
  endproperty
            
   PROBLEM6: assert property (load_lock_check)
              $error("Load_en is high for more than 3 pulses Invalid condition ");
             else 
              $display("proper load_en");
              

        
  // PROBLEM 7:If shift_en pulses high for only 1 cycle and data_out doesn't change, raise an error.
  property shift_en_glitch;
       @(posedge clk) disable iff(rst)
      shift_en |=> $stable(data_out);
  endproperty
                       
  PROBLEM7: assert property (shift_en_glitch)
           $error("with shift_en high data doesn't changed check the error");
           else 
          $display("data_out is properly changed when shift_en is high");
 
                  //PROBLEM 8: After reset, data_out should remain 0 for at least 2 more clock cycles.
  property hold_after_reset;
       @(posedge clk) 
    rst ##1 !rst |=> (data_out==0)[*1:2];
  endproperty
  
  PROBLEM8: assert property(hold_after_reset)
           $display("data_out is 0 after reset ");
            else 
          $error("data_out changed after reset");
                   

//PROBLEM 9: If shift_en and load_en are both low, data_out must remain unchanged.
 
  property unexpected_transition;
     @(posedge clk) disable iff(rst)
    (!shift_en && !load_en) |=> $stable(data_out);
  endproperty
       
PROBLEM9: assert property (unexpected_transition)
         $display("data_out is stable when shift_en and load_en are low");
        else 
        $error("unexpected transition of data_out when shift_en , load_en are low");
   
  //PROBLEM 10: When load_en is asserted, data_out must match data_in in the next cycle.

 
  property valid_load;
     @(posedge clk) disable iff(rst)
    load_en |=> (data_out==data_in);
  endproperty
       
 PROBLEM10: assert property (valid_load)
          $display("valid data_out when load_en is high");
          else 
           $error("invalid data_out when load_en is high"); 
   
endmodule
