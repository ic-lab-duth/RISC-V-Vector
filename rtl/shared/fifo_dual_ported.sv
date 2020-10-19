/*
* @info Dual Ported FIFO
* @info Sub-Modules: and_or_mux.sv
*
* @author VLSI Lab, EE dept., Democritus University of Thrace
*
* @brief Instructions assigned: Branches, Shifts, Compares
*
* @note  Priority is given to the input interface 1 : If 2 pushes simultaneously, push_data_1 will get the first available slot
* @note  Output Interfaces are linked. Can not pop_2 without pop_1
*
* @param DW    : # of Data Bits (default 16 bits)
* @param DEPTH : # of Entries (default 4 entries) (if DEPTH==1, then 50% throughput)
*/
module fifo_dual_ported #(
    parameter int DW    = 16,
    parameter int DEPTH = 4
) (
    input  logic          clk        ,
    input  logic          rst        ,
    //Flush Interface
    input  logic          valid_flush,
    //input interface 1
    input  logic          push_1     ,
    output logic          ready_1    ,
    input  logic [DW-1:0] push_data_1,
    //input interface 2
    input  logic          push_2     ,
    output logic          ready_2    ,
    input  logic [DW-1:0] push_data_2,
    //output interface 1
    output logic [DW-1:0] pop_data_1 ,
    output logic          valid_1    ,
    input  logic          pop_1      ,
    //output interface 2
    output logic [DW-1:0] pop_data_2 ,
    output logic          valid_2    ,
    input  logic          pop_2
);

// #Internal Signals#
logic[DEPTH-1:0][DW-1:0]    memory;
logic[DEPTH-1:0]            tail, tail_plus;
logic[DEPTH-1:0]            head, head_plus;
logic[DEPTH  :0]            status_cnt;
logic[3      :0]            shift_vector;
logic                       double_push, single_push, double_pop, single_pop;
logic                       shift_left_double, shift_left_single;
logic                       shift_right_double, shift_right_single;

assign valid_1 = ~status_cnt[0];
assign valid_2 = ~status_cnt[1] & ~status_cnt[0];
assign ready_1 = ~status_cnt[DEPTH];
assign ready_2 = ~status_cnt[DEPTH] & ~status_cnt[DEPTH-1];
//intermidiate logic
assign single_push = push_1 | push_2;
assign double_push = push_1 & push_2;
assign single_pop  = pop_1 | pop_2;
assign double_pop  = pop_1 & pop_2;

assign shift_left_double  = double_push & ~single_pop;
assign shift_left_single  = ((double_push & single_pop) | (single_push & ~single_pop)) & ~shift_left_double;
assign shift_right_double = double_pop & ~single_push;
assign shift_right_single = ((double_pop & single_push) | (single_pop & ~single_push)) & ~shift_right_double; 
assign shift_vector = {shift_left_double,shift_left_single,shift_right_double,shift_right_single};
// Tail Pointer update (one-hot shifting pointers)
always_ff @ (posedge clk, posedge rst) begin: TailManagement
    if (rst) begin
        tail <= 1;
    end else if (valid_flush) begin
        tail <= 1;
    end else begin
        // push pointer
        if (double_push) begin
            tail <= {tail[DEPTH-3:0], tail[DEPTH-1:DEPTH-2]};
        end else if(single_push) begin
            tail <= {tail[DEPTH-2:0], tail[DEPTH-1]};
        end
    end
end
assign tail_plus = {tail[DEPTH-2:0], tail[DEPTH-1]};
// Head Pointer update (one-hot shifting pointers)
always_ff @ (posedge clk, posedge rst) begin: HeadManagement
    if (rst) begin
        head <= 1;
    end else if (valid_flush) begin
        head <= 1;
    end else begin
        // pop pointer
        if (double_pop) begin
            head <= {head[DEPTH-3:0], head[DEPTH-1:DEPTH-2]};
        end else if(single_pop) begin
            head <= {head[DEPTH-2:0], head[DEPTH-1]};
        end
    end
end
assign head_plus = {head[DEPTH-2:0], head[DEPTH-1]};    
// Status Counter (onehot coded)
always_ff @ (posedge clk, posedge rst) begin: ff_status_cnt
    if (rst) begin
        status_cnt <= 1;
    end else if (valid_flush) begin
        status_cnt <= 1;
    end else begin
        case (shift_vector)
            4'b1000 : status_cnt <= {status_cnt[DEPTH-2:0], 2'b0};
            4'b0100 : status_cnt <= {status_cnt[DEPTH-1:0], 1'b0};
            4'b0010 : status_cnt <= {2'b0, status_cnt[DEPTH:2]};
            4'b0001 : status_cnt <= {1'b0, status_cnt[DEPTH:1]};
            default : status_cnt <= status_cnt;
        endcase
    end
end 
// Data write (push) 
// address decoding needed for onehot push pointer
always_ff @ (posedge clk) begin: ff_reg_dec
    for (int i=0; i < DEPTH; i++) begin
        if(double_push) begin
            if(push_1 && tail[i]) begin
                memory[i] <= push_data_1;
            end else if(push_2 && tail_plus[i]) begin
                memory[i] <= push_data_2;
            end
        end else begin
            if(push_1 && tail[i]) begin
                memory[i] <= push_data_1;
            end else if(push_2 && tail[i]) begin
                memory[i] <= push_data_2;
            end
        end
    end
end

and_or_mux #(
    .INPUTS (DEPTH),
    .DW     (DW)
)
mux_out_1 (
    .data_in  (memory),
    .sel      (head),
    .data_out (pop_data_1)
);

and_or_mux #(
    .INPUTS (DEPTH),
    .DW     (DW)
)
mux_out_2 (
    .data_in  (memory),
    .sel      (head_plus),
    .data_out (pop_data_2)
);
    
assert property (@(posedge clk) disable iff(rst) pop_2       |-> pop_1)     else $error(1, "DP FIFO:Illegal Scenario");
endmodule
