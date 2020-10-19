/**
 * @info eb_two_slot
 *
 * @author VLSI Lab, EE dept., Democritus University of Thrace
 *
 * @brief 2-slot Elastic Buffer (EB) that achieves 100% throughput without combinational back-notification propagation.
 *        Combines the benefits of HBEB and PEB (@see eb_one_slot) but requires 2 buffer slots.
 *        Note: It is not mandatory that the sender checks the EB's ready_out to assert its valid.
 *        Design Concerns:
 *          + Completely cuts off the forward path. Output Data do not go through any MUX (as would happen in a
 *            circular buffer FIFO). This comes at the cost of the following:
 *             - The Input Data path sees a 2:1 MUX.
 *             - It is not a really power friendly design (the input buffer slot makes redundant writes) & in case
 *               of a stall, it SHIFTS data
 *         It may be preferred in cases where Output paths are slower and the FIFO MUX must be removed.
 *        (can be used combined with circular buffer FIFO, @see fifo_duth)
 *
 * @param DATA_WIDTH data width
 * @param GATING_FRIENDLY determines if data are always registered (==0) or only when 'valid_in' is asserted (==1).
 */

module eb_two_slot
#(
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
// Main
logic                   valid_to_main_eb;
logic                   ready_from_main_eb;
logic[DATA_WIDTH-1:0]   data_to_main_eb;
// Buffered ready
logic                   ready_main_buf;
//Aux
logic                   ready_from_aux_eb;
logic                   valid_from_aux_eb; 
logic                   ready_to_aux_eb; 
logic[DATA_WIDTH-1:0]   data_from_aux_eb;
// ------------------------------------------------------------------------------------------------ //

// Back
assign ready_out = ready_from_aux_eb;
    
// Aux reg
eb_one_slot
#(
    .FULL_THROUGHPUT    (1'b1),
    .DATA_WIDTH         (DATA_WIDTH),
    .GATING_FRIENDLY    (GATING_FRIENDLY)
)
eb_aux
(
    .clk          (clk),
    .rst          (rst),
    .valid_in     (valid_in),
    .ready_out    (ready_from_aux_eb),
    .data_in      (data_in),
    .valid_out    (valid_from_aux_eb),
    .ready_in     (ready_to_aux_eb),
    .data_out     (data_from_aux_eb)
);

assign ready_to_aux_eb = ready_main_buf;

// buffer ready from main reg
always_ff @ (posedge clk, posedge rst) begin: ff_ready_main_buf
    if (rst) begin
        ready_main_buf <= 1;
    end else begin
        ready_main_buf <= ready_from_main_eb;
    end
end

// Main reg
assign  valid_to_main_eb = ready_from_aux_eb ? valid_in : valid_from_aux_eb;
assign  data_to_main_eb  = ready_from_aux_eb ? data_in  : data_from_aux_eb;

eb_one_slot
#(
    .FULL_THROUGHPUT    (1'b1),
    .DATA_WIDTH         (DATA_WIDTH),
    .GATING_FRIENDLY    (GATING_FRIENDLY)
)
eb_main
(
    .clk          (clk),
    .rst          (rst),
    .valid_in     (valid_to_main_eb),
    .ready_out    (ready_from_main_eb),
    .data_in      (data_to_main_eb),
    .valid_out    (valid_out),
    .ready_in     (ready_in),
    .data_out     (data_out)
);

endmodule
