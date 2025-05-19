module timer (
  input  logic        clk,
  input  logic        rst,
  input  logic        start,
  input  logic [3:0]  load_val,
  output logic        done,
  output logic [3:0]  count
);

  typedef enum logic [1:0] {IDLE, RUN, DONE} state_t;
  state_t state, next_state;

  always_ff @(posedge clk or posedge rst) begin
    if (rst)
      state <= IDLE;
    else
      state <= next_state;
  end

  always_ff @(posedge clk or posedge rst) begin
    if (rst)
      count <= 0;
    else if (state == IDLE && start)
      count <= load_val;
    else if (state == RUN)
      count <= count - 1;
  end

  always_comb begin
    next_state = state;
    case (state)
      IDLE: if (start) next_state = RUN;
      RUN:  if (count == 0) next_state = DONE;
      DONE: next_state = IDLE;
    endcase
  end

  assign done = (state == DONE);

endmodule
