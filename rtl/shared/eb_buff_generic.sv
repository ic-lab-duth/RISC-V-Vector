/**
 * @info fifo_duth
 *
 * @author VLSI Lab, EE dept., Democritus University of Thrace
 *
 * @brief
 *
 * @param 
 * @param 
 */

// Set BUFF_TYPE as follows:
//  0: One-slot Half-Bandwidth EB (50% throughput)
//  1: One-slot Full-Bandwidth EB (100% throughput - comb backpressure paths)
//  2: Two-slot Full-Bandwidth EB (100% throughput)
//  3: FIFO (use param DEPTH to set the depth)
module eb_buff_generic
#(
    parameter int   DW          = 32,
    parameter int   BUFF_TYPE   = 2,
    parameter int   DEPTH       = 4
)
(
    input  logic            clk,
    input  logic            rst,
    // input channel
    input  logic[DW-1:0]    data_i,
    input  logic            valid_i,
    output logic            ready_o,
    // output channel
    output logic[DW-1:0]    data_o,
    output logic            valid_o,
    input  logic            ready_i
);

generate
    if ( (BUFF_TYPE == 0) | (BUFF_TYPE == 1) ) begin: gen_one_slot_eb
        eb_one_slot #(
            .FULL_THROUGHPUT(BUFF_TYPE == 1),
            .DATA_WIDTH     (DW            ),
            .GATING_FRIENDLY(1'b1          )
        ) eb (
            .clk      (clk    ),
            .rst      (rst    ),
            
            .valid_in (valid_i),
            .ready_out(ready_o),
            .data_in  (data_i ),
            
            .valid_out(valid_o),
            .ready_in (ready_i),
            .data_out (data_o )
        );

    end else if (BUFF_TYPE == 2) begin: gen_two_slot_eb
        eb_two_slot #(
            .DATA_WIDTH     (DW  ),
            .GATING_FRIENDLY(1'b1)
        ) eb (
            .clk      (clk    ),
            .rst      (rst    ),
            
            .valid_in (valid_i),
            .ready_out(ready_o),
            .data_in  (data_i ),
            
            .valid_out(valid_o),
            .ready_in (ready_i),
            .data_out (data_o )
        );
    end else begin: gen_fifo
        // FIFO has a different interface that is NOT flow-controlled
        logic fifo_push;
        logic fifo_pop;

        assign fifo_push    = valid_i & ready_o;
        assign fifo_pop     = valid_o & ready_i;

        fifo_duth #(
            .DW   (DW   ),
            .DEPTH(DEPTH)
        ) fifo (
            .clk      (clk      ),
            .rst      (rst      ),
            
            .push_data(data_i   ),
            .push     (fifo_push),
            .ready    (ready_o  ),
            
            .pop_data (data_o   ),
            .valid    (valid_o  ),
            .pop      (fifo_pop )
        );
    end
endgenerate

endmodule
