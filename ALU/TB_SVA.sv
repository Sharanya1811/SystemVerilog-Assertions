
`timescale 1ns / 1ps

module alu_tb;
  logic clk = 0, rst;
  logic [2:0] opcode;
  logic [7:0] a, b;
  logic [15:0] result;
  logic valid; 

  
  alu dut (.clk(clk), .rst(rst), .opcode(opcode), .a(a), .b(b), .result(result), .valid(valid));

  
  always #5 clk = ~clk;

  // assertions
  //PROBLEM 1: valid should never be high on reset
  property valid_on_reset;
    @(posedge clk) rst |-> !valid;
  endproperty
  
  PROBLEM1: assert property (valid_on_reset)
    $display("Valid when reset id proper");
           else 
             $error("on Reset valid is is high");
   
 //PROBLEM 2: When opcode is invalid (> 3'b101), valid must go low and result == 16'hDEAD
    property opcode_invalid;
      @(posedge clk) disable iff(rst)
      (opcode> 3'b101) |=> !valid && result ==16'hDEAD;
    endproperty
    
    PROBLEM2: assert property (opcode_invalid)
              $display("valid and result when opcode is invalid is true");
              else 
                $error("on opcode invalid condition check the valid and result");
   
     
    //PROBLEM 3: For opcode == ADD, result == a + b   
    property ADD_operation;
      @(posedge clk) disable iff(rst)
      (opcode ==3'b000) |=> (result == (a+b)) ;
    endproperty
    
  PROBLEM3:assert property (ADD_operation)
    $display("valid ADD operation");
           else 
             $error("invalid ADD operation");
     
   // PROBLEM 4: If a == b, and opcode == SUB, then result must be 0.  
    property SUB_check;
      @(posedge clk) disable iff(rst)
           (opcode== 3'b001 && a==0 && b==0) |=> (result ==0);
    endproperty
    
        PROBLEM4: assert property (SUB_check)
          $display("valid SUB operation");
           else 
             $error("invalid SUB operation");
        
     //PROBLEM 5:After every MUL, result must remain unchanged for 2 cycles. 
      property MUL_stable;
      @(posedge clk) disable iff(rst)
        (opcode== 3'b101) |=> ($stable(result)[->2]);  
    endproperty
    
          PROBLEM5: assert property (MUL_stable)
            $display("valid MUL operation");
           else 
             $error("invalid MUL operation");
  
  //PROBLEM 6:When opcode is XOR, result should never be all 0s unless a == b.
     property XOR_check;
      @(posedge clk) disable iff(rst)
       ((opcode ==3'b100) && (a==b)) |=> (result==0);
    endproperty
    
     PROBLEM6: assert property (XOR_check)
       $display("valid XOR operation");
           else 
             $error("invalid XOR operation");
 
 
 //PROBLEM 7: When opcode == AND, and a == 8'hFF, result must be equal to b. 
     property AND_check;
      @(posedge clk) disable iff(rst)
       ((opcode==3'b010) && (a==8'hFF)) |=> (result==b);
    endproperty
    
       PROBELM7: assert property (AND_check)
         $display("valid AND operation with A value");
           else 
             $error("invalid AND operation with A value");

     
    //PROBLEM 8: For OR, if a == 0, then result == b     
    property OR_check;
      @(posedge clk) disable iff(rst)
      ((opcode==3'b011) ); //&& (a==0)) |-> (result==b);
    endproperty
    
    PROBLEM8: assert property (OR_check)
      $display("valid OR operation with A value");
           else 
             $error("valid OR operation with A value");

      
    //PROBLEM 9: After 3 consecutive cycles of the same opcode, result must remain stable  
     property opcode_stable_result;
      @(posedge clk) disable iff(rst)
       $stable(opcode)[*3] |=> $stable(result);
    endproperty
    
      PROBLEM9:assert property (opcode_stable_result)
        $display("stable result on stable opcode");
           else 
             $error("unstable result on stable opcode");

  //PROBLEM 10: If rst is high at any clock, result must be zero in the next cycle.
  
    property result_on_reset;
      @(posedge clk)
      rst |=>(result==0);
    endproperty
    
    PROBLEM10: assert property (result_on_reset)
      $display("valid result on reset");
           else 
             $error("invalid result on reset");
      

  

   initial begin
    rst = 1; opcode = 0; a = 0; b = 0; #20;
    rst = 0;

    // ADD
    opcode = 3'b000; a = 8'd10; b = 8'd15; #20;
    $display("result=%d",result);

    // SUB
    opcode = 3'b001; a = 8'd20; b = 8'd20; #20;
   
    // SUB
    opcode = 3'b001; a = 0; b = 0; #20;

    // MUL
    //p5
    opcode = 3'b101; a = 8'd3; b = 8'd4; #60;

    // Invalid opcode
    opcode = 3'b111; a = 8'd10; b = 8'd5; #20;
    // AND, OR, XOR
    //p7
    opcode = 3'b010; a = 8'hFF; b = 8'd5; #20; 
     //p8
    opcode = 3'b011; a = 8'd0; b = 8'd100; #20;
     //p6
    opcode = 3'b100; a = 8'd55; b = 8'd55; #20;
    opcode= 3'b100 ; #20;
    opcode= 3'b100 ; #20;
  
    $finish;
    
  end
    
    initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
    end
endmodule




