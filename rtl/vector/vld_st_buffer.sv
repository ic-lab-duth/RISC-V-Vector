/*
* @info Load/Store Buffer Module
* @info Top Modules: data_cache.sv
*
* @author VLSI Lab, EE dept., Democritus University of Thrace
*
* @brief  Used in the non-blocking Data Cache.
*
* @param DATA_WIDTH    : # of Data Bits (default 32 bits)
* @param ADDR_BITS     : # of Address Bits (default 32 bits)
* @param BLOCK_ID_START: # of Bit from which the Block ID starts
* @param R_WIDTH       : # of Register Bits (default 6 bits)
* @param MICROOP_WIDTH       : # of Microoperation Bits (default 5 bits)
* @param ROB_TICKET    : # of ROB Ticket Bits (default 3 bits)
* @param DEPTH         : # of Entries in Buffer (default 8 entries)
*/
module vld_st_buffer #(
    parameter DATA_WIDTH     = 32,
    parameter ADDR_BITS      = 32,
    parameter BLOCK_ID_START = 5 ,
    parameter R_WIDTH        = 5 ,
    parameter MICROOP_WIDTH  = 7 ,
    parameter TICKET_WIDTH   = 4 ,
    parameter SIZE_WIDTH     = 3 ,
    parameter DEPTH          = 4
) (
    input  logic                     clk             ,
    input  logic                     rst_n           ,
    //Write Port
    input  logic                     push            ,
    input  logic [    ADDR_BITS-1:0] write_address   ,
    input  logic [   DATA_WIDTH-1:0] write_data      ,
    input  logic [ TICKET_WIDTH-1:0] write_ticket    ,
    input  logic [MICROOP_WIDTH-1:0] write_microop   ,
    input  logic [   SIZE_WIDTH-1:0] write_size      ,
    //Update Port for fetch status
    input  logic                     valid_update_i  ,
    input  logic [    ADDR_BITS-1:0] update_address_i,
    //Head Output
    input  logic                     pop             ,
    output logic                     head_is_store   ,
    output logic                     head_is_fetched ,
    output logic [    ADDR_BITS-1:0] head_address    ,
    output logic [   DATA_WIDTH-1:0] head_data       ,
    output logic [MICROOP_WIDTH-1:0] head_microop    ,
    output logic [ TICKET_WIDTH-1:0] head_ticket     ,
    output logic [   SIZE_WIDTH-1:0] head_size       ,
    //Status Port
    output logic                     valid_o         ,
    output logic                     ready_o
);

    localparam INFO_WIDTH = TICKET_WIDTH + MICROOP_WIDTH + SIZE_WIDTH;
    // #Memory Arrays#
    logic [     DEPTH-1:0][ ADDR_BITS-1:0] saved_address     ;
    logic [     DEPTH-1:0][DATA_WIDTH-1:0] saved_data        ;
    logic [     DEPTH-1:0][INFO_WIDTH-1:0] saved_info        ;
    logic [INFO_WIDTH-1:0]                 head_info, search_info;
    logic [     DEPTH-1:0]                 saved_valid       ;
    logic [     DEPTH-1:0]                 saved_isstore     ;
    logic [     DEPTH-1:0]                 saved_is_fetched  ;
    logic [     DEPTH-1:0]                 matched_update    ;
    logic [     DEPTH-1:0]                 head_oh           ;
    logic                                  write_isstore     ;
    logic                                  will_update       ;


    // #Internal Signals#
    logic [DEPTH-1:0] head, tail;
    logic [DEPTH:0]   stat_counter;

    assign valid_o = ~stat_counter[0];
    assign ready_o = ~stat_counter[DEPTH];

    assign write_isstore = write_microop[4:3] === 2'b11;
    assign head_oh       = 1 << head;

    //Tail Management (moves on new pops)
    always_ff @(posedge clk or negedge rst_n) begin : TailManagement
        if(!rst_n) begin
            tail <= 1;
        end else begin
            if (push) tail <= {tail[DEPTH-2:0], tail[DEPTH-1]};
        end
    end
    // Head Management (moves when it points to an invalid entry)
    always_ff @(posedge clk or negedge rst_n) begin : HeadManagement
        if(!rst_n) begin
            head <= 1;
        end else begin
            if (pop) begin
                head <= {head[DEPTH-2:0], head[DEPTH-1]};
            end
        end
    end
    //Status Counter Management
    always_ff @(posedge clk or negedge rst_n) begin : statCounter
        if(!rst_n) begin
            stat_counter <= 1;
        end else begin
            if (push & !pop) begin
                // shift left status counter (increment)
                stat_counter <= stat_counter << 1;
            end else if (!push &  pop) begin
                // shift right status counter (decrement)
                stat_counter <= stat_counter >> 1;
            end
        end
    end
    // Memory Management (Data Write)
    always_ff @(posedge clk) begin : MemoryData
        for (int i = 0; i < DEPTH; i++) begin
            if(push && tail[i]) begin
                saved_address[i] <= write_address;
                saved_data[i]    <= write_data;
                saved_isstore[i] <= write_isstore;
                saved_info[i]    <= {write_size,write_ticket,write_microop};
            end
        end
    end
    // Memory Management (Validity)
    always_ff @(posedge clk or negedge rst_n) begin : MemoryValidity
        if(!rst_n) begin
            saved_valid <= 'b0;
        end else begin
            for (int i = 0; i < DEPTH; i++) begin
                if(push && tail[i]) begin
                    saved_valid[i] <= 1'b1;
                end else if(pop && head[i]) begin
                    saved_valid[i] <= 1'b0;
                end
            end
        end
    end
    //Search the Locations to update as Fetched
    always_comb begin : matchUpdate
        for (int i = 0; i < DEPTH; i++) begin
            matched_update[i] = saved_valid[i] ? (update_address_i[ADDR_BITS-1:BLOCK_ID_START]==saved_address[i][ADDR_BITS-1:BLOCK_ID_START]) : 1'b0;
        end
    end
    assign will_update = |matched_update & valid_update_i;
    // Memory Management (is_fetched)
    always_ff @(posedge clk or negedge rst_n) begin : MemoryFetched
        if(!rst_n) begin
            saved_is_fetched <= 'b0;
        end else begin
            for (int i = 0; i < DEPTH; i++) begin
                if(push && tail[i]) begin
                    saved_is_fetched[i] <= 1'b0;
                end else if(will_update && matched_update[i]) begin
                    saved_is_fetched[i] <= 1'b1;
                end
            end
        end
    end

    //HEAD OUTPUTS
    // Pick the Address Output
    and_or_mux #(
        .INPUTS(DEPTH    ),
        .DW    (ADDR_BITS)
    ) mux_addr (
        .data_in (saved_address),
        .sel     (head         ),
        .data_out(head_address )
    );
    // Pick the Data Output
    and_or_mux #(
        .INPUTS(DEPTH     ),
        .DW    (DATA_WIDTH)
    ) mux_data (
        .data_in (saved_data),
        .sel     (head      ),
        .data_out(head_data )
    );

    //Pick the MICROOP_WIDTH/Destination Output
    and_or_mux #(
        .INPUTS(DEPTH     ),
        .DW    (INFO_WIDTH)
    ) mux_info (
        .data_in (saved_info),
        .sel     (head      ),
        .data_out(head_info )
    );

    assign head_microop = head_info[0 +: MICROOP_WIDTH];
    assign head_ticket  = head_info[MICROOP_WIDTH +: TICKET_WIDTH];
    assign head_size    = head_info[MICROOP_WIDTH + TICKET_WIDTH +: SIZE_WIDTH];

    //Pick the is_fetched Output
    and_or_mux #(
        .INPUTS(DEPTH),
        .DW    (1    )
    ) mux_is_fetched (
        .data_in (saved_is_fetched),
        .sel     (head            ),
        .data_out(head_is_fetched )
    );

    //Pick the is_store Output
    and_or_mux #(
        .INPUTS(DEPTH),
        .DW    (1    )
    ) mux_is_store (
        .data_in (saved_isstore),
        .sel     (head         ),
        .data_out(head_is_store)
    );


    assert property (@(posedge clk) disable iff(!rst_n) push |-> ready_o) else $error("ERROR:vLD_ST Buffer: Push on Full");
    assert property (@(posedge clk) disable iff(!rst_n) pop |-> valid_o) else $error("ERROR:vLD_ST Buffer: Pop on Empty");

    assert property (@(posedge clk) disable iff(!rst_n) valid_update_i |-> ~$isunknown(update_address_i)) else $error("ERROR:vLD_ST Buffer: update_address_i");
    assert property (@(posedge clk) disable iff(!rst_n) ~$isunknown(will_update)) else $error("x-check:vLD_ST Buffer: will_update");
    assert property (@(posedge clk) disable iff(!rst_n) ~$isunknown(push)) else $error("x-check:vLD_ST Buffer: push");
    assert property (@(posedge clk) disable iff(!rst_n) ~$isunknown(pop)) else $error("x-check:vLD_ST Buffer: pop");
    assert property (@(posedge clk) disable iff(!rst_n) ~$isunknown(|saved_valid)) else $error("x-check:vLD_ST Buffer: saved_valid");

endmodule