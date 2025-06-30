      
module rr_arbiter_tb;
  parameter S=4;
  logic clk, reset;
  logic [(S-1):0] req;
  logic [(S-1):0] grant;

  round_robin_arbiter #(.N(4))dut (
    .clk(clk),
    .reset(reset),
    .req(req),
    .grant(grant)
  );

  
 //PROBLEM 1: Assert that at any time, only one grant is high, or all are zero no requests
  
  property one_hot_grant;
    @(posedge clk) disable iff(!reset)
    req |=> $onehot(grant);
   // !req |=> (grant==0);
 endproperty
  
  PROBLEM1: assert property(one_hot_grant)
    $display("only one grant for one request");
           else
             $error("more grants for one request");
   
    //PROBLEM 2: No grant when no requests
  
  property one_hot_grant;
    @(posedge clk) disable iff(!reset)
    !req |=> (grant==0);
 endproperty
  
  PROBLEM2: assert property(one_hot_grant)
    $display("no grant when no request");
           else
             $error("grant when no request");
  


 //PROBLEM 3: On reset (rst_n == 0), the grant output should be zero.

  property reset_state;
   @(posedge clk) 
      !reset |=> (grant==0);
 endproperty
  
  PROBLEM3: assert property(reset_state)
    $display("when reset grant are non");
           else
             $error("check the grants when rest");
 
   //PROBLEM 4: Assert that grant[i] & grant[j] == 0 for i ≠ j in the same cycle.

   genvar i;
generate
  for (i = 1; i < 4; i++) begin
    assert property (
      @(posedge clk) disable iff(!reset)
      ( grant[i-1] && grant[i]) ==0
    )
      $display("no two grants are equal at same time");
      else
        $error("two grants are equal at same time");
  end
endgenerate
    
 
  
  //PROBLEM 5: Assert that a granted signal must have had a corresponding request.

    genvar i;
   generate
     for(i=0;i<S;i++) begin
       assert property(
         @(posedge clk) disable iff(!reset)
         req[i] |=>grant[i])
         
         $display("grant with respect to request");
      else
        $error("not correct grants w.r.t reqs");
     end
   endgenerate
   
             //PROBLEM 6: If all req[i] are held high continuously, the arbiter should cycle grants across all requests
    property all_process_request;
      @(posedge clk) disable iff(!reset)
      req==4'b1111 |=> $onehot(grant) ##1  $onehot(grant)##1 $onehot(grant) ##1 $onehot(grant);
 endproperty
  
  PROBLEM6: assert property(all_process_request)
    $display("only one grant for all the requests");
           else
             $error("more grants when all the request simultaneously");
  

  
  
  always #5 clk = ~clk;

  initial begin
    clk = 0; reset = 0; req = 4'b0000;
    #10 reset = 1;

    // Test: single request
    #10 req = 4'b0001;
    #20 req = 4'b0010;
    #20 req = 4'b0100;
    #20 req = 4'b1000;

    // multiple requests
    #20 req = 4'b1010;
    
    //all the requests
    #20 reset = 0;
    #10 reset = 1;
    #90 req = 4'b1111;

    // Reset again
    #20 reset = 0;
    #10 reset = 1;
    #10 req = 4'b0010;

    #100 $finish;
  end
      
      initial begin
  $dumpfile("dump.vcd");
  $dumpvars;
      end

endmodule


