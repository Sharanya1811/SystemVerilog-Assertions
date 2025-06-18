module moore_sequence_detector_1011 (
  input logic clock,
  input  logic reset,
  input logic  din,
  output logic  dout
);
  
  typedef enum logic [2:0]{s0=0,s1=1,s2=2,s3=3,s4=4} state_t;
  state_t state;
  
  
  
   always @(posedge clock or negedge reset) begin
    if(!reset) begin
       dout<=0;
       state<=s0;
     end
    else begin
      case(state) 
        s0: begin
          dout<=0;
          if(din) begin
            state<=s1;
          end
          else begin
            state<=s0;
          end
        end 
        s1: begin
          dout<=0;
          if(!din) begin
            state<=s2;
          end
          else begin
            state<=s1;
          end
        end
        s2: begin
          dout<=0;
          if(din) begin
            state<=s3;
          end
          else begin
            state<=s0;
          end
        end
        s3: begin
          dout<=0;
          if(din) begin
            state<=s4;
          end
          else begin
            state<=s1;
          end
        end
        s4: begin
          dout<=1'b1;
          if(din) begin
            state<=s1;
          end
          else begin
            state<=s2;
          end
        end
        default: state<=s0;
      endcase
    end
  end
     
endmodule
