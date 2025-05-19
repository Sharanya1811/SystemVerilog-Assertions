

`timescale 1ns / 1ps
module tb_decoder_3to8;
  logic [2:0] in;
  logic en;
  logic [7:0] out;
  logic clk;

  decoder_3to8 dut (.in(in), .en(en), .out(out));

  //Assertions
  
  //PROBLEM 1:One-hot output: When en = 1, only one output bit must be high.
  
 property onehot_encoding;
   @(posedge clk)
   en |-> $onehot(out);
 endproperty
  
  PROBLEM1: assert property(onehot_encoding)
    $display("only one bit in high in out when en=1");
           else
             $error("out has many high when en=1");
   
    
  //PROBLEM 2:All zeros when disabled: When en = 0, all bits of out must be 0.
  
 property all_zeros;
   @(posedge clk)
   !en |-> (out==7'b0);
 endproperty
  
  PROBLEM2: assert property(all_zeros)
            $display("out is 0 when en is 0");
           else
             $error("out is not zero when en =0");
            
 //PROBLEM 3:Output index check: When in = i and en = 1, then out[i] must be 1.
  
 property output_index_check;
   @(posedge clk)
   ( en && in) |->(out[in]==1);
 endproperty
  
  PROBLEM3: assert property(output_index_check)
    $display("out[i]=1 based on value in");
           else
             $error("out[i] is not one based on in ");
    
   
   //PROBLEM 4:Output must be stable if input and en remain constant.
  
 property stable_out_for_stable_in;
   @(posedge clk)
   ($stable(in) && $stable(en)) |-> $stable(out);
 endproperty
  
  PROBLEM4: assert property(stable_out_for_stable_in)
    $display("output is stable for stable in and en");
           else
             $error("unstable out for stable in and en");
    
    
      //PROBLEM 5: Output should change only if in or en changes.
  
 property output_change_for_in;
   @(posedge clk)
   ( $changed(in) || $changed(en)) |-> $changed(out);
 endproperty
  
  PROBLEM5: assert property(output_change_for_in)
    $display("output change based on in and en");
           else
             $error("output is stable even though in and en changed");
    
      //PROBLEM 6:Valid output should not persist after en is deasserted
  
 property out_when_en;
   @(posedge clk)
   !en |->(out==0);
 endproperty
  
  PROBLEM6: assert property(out_when_en)
    $display("output is 0 when en is 0");
           else
             $error("output is not 0 when en =0");
    
    
      //PROBLEM 7:Glitch-free transition: No more than one output bit changes between consecutive cycles when in changes by 1.
  
 property glitch_free_transition;
   @(posedge clk)
   (in==3'b001 && en) |-> ($onehot(out) && ((out==8'b0000_0010 ) && ($past(out)==8'b0000_0001)));
 endproperty
  
  PROBLEM7: assert property(glitch_free_transition)
    $display("only one bit changed when in is");
           else
             $error("more bits changed when in =1");
   
 
      //PROBLEM 8: Output must update within 1 clock cycle after input change.
   
 property latency_check;
   @(posedge clk)
   ($changed(in) && en) |-> (out==8'b0000_0001<<in);
 endproperty
  
  PROBLEM8: assert property(latency_check)
    $display("output changed within one clock");
           else
             $error("output changed after 1 clock ");
    
    
   
      //PROBLEM 9: If out has more than 1 bit set, raise an error.
  
 property illegal_state_detection;
   @(posedge clk)
   en |-> $onehot(out);
 endproperty
  
  PROBLEM9: assert property(illegal_state_detection)
    $display("out has only one bit changed ");
           else
             $error("out has more than one bit changed");
  
        //PROBLEM 10:No output should go high when in is X or Z.
  
 property when_in_x_or_z;
   @(posedge clk)
   (in==3'bx || in ==3'bz) |-> (out==8'b0);
 endproperty
  
  PROBLEM10: assert property(when_in_x_or_z)
    $display("when in is z or x  output should not go high");
           else
             $error("when in is z or x output is high");
      

  initial begin
    clk = 0;
    forever #5 clk = ~clk;
  end

  initial begin
    in = 0; en = 0;
    #10 en = 1;
    for (int i = 0; i < 8; i++) begin
      in = i;
      #10;
    end 
   in=1;#30;//for p4
    
    en = 0;
    #10;
    /*comment for assertion 5 to pass if not commented then you can the failing assertion and learn why it is failing*/
    in = 3'bx; #10;
    in = 3'bz; #10;
    $finish;
  end
  
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars();
  end
endmodule
