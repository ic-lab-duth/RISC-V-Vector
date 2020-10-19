/**
 * @info eb_one_slot
 *
 * @author VLSI Lab, EE dept., Democritus University of Thrace
 *
 * @brief 1-slot Elastic Buffer (EB) with parameter that determines the implementation in terms of throughput
 *        and propagation of back-notification path ('ready_out').
 *
 * @param FULL_THROUGHPUT Determines the implementation.
 *        - If set to 0, a Half-Bandwidth EB (HBEB) is generated, where back notification ('ready_out') is deasserted whenever the buffer is full,
 *        which cannot offer more than 50% throughput
 *        - If set to 1, a Pipelined EB (PEB) is generated, which supports 100% throughput, but the notification signal is
 *        send backwards combinationally
 * @param DATA_WIDTH data width
 * @param GATING_FRIENDLY determines if data are always registered (==0) or only when 'valid_in' is asserted (==1).
 */
 
module eb_one_slot
#(
    parameter logic FULL_THROUGHPUT = 1'b0,
    parameter int   DATA_WIDTH      = 16,
    parameter logic GATING_FRIENDLY = 1'b1
)
(
    input   logic                   clk,
    input   logic                   rst,
    // input side
    input   logic                   valid_in,
    output  logic                   ready_out,
    input   logic[DATA_WIDTH-1:0]   data_in,
    
    //output side
    output  logic                   valid_out,
    input   logic                   ready_in,
    output  logic[DATA_WIDTH-1:0]   data_out
);
// ------------------------------------------------------------------------------------------------ //
logic[DATA_WIDTH-1:0]   data_r;
logic                   full_r;
logic                   write_en;
// ------------------------------------------------------------------------------------------------ //
assign valid_out    = full_r;
assign ready_out    = write_en;
assign data_out     = data_r;

// write_en depends on impl.
generate
    if (FULL_THROUGHPUT) begin: gen_if_ft
        assign write_en = ready_in | ~full_r;
    end else begin: gen_if_ht
        assign write_en = ~full_r;
    end
endgenerate

// Full reg
always_ff @(posedge clk, posedge rst) begin: ff_full_r
    if (rst) begin
        full_r <= 0;
    end else begin
        if (write_en) begin
            full_r <= valid_in;
        end
    end
end

// data reg
always_ff @(posedge clk) begin: ff_data_r
    if (write_en) begin
        if (!GATING_FRIENDLY | valid_in) begin
            data_r <= data_in;
        end
    end
end

endmodule
