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
 * @param MICROOP       : # of Microoperation Bits (default 5 bits)
 * @param ROB_TICKET    : # of ROB Ticket Bits (default 3 bits)
 * @param DEPTH         : # of Entries in Buffer (default 8 entries)
 */
module ld_st_buffer #(
    parameter DATA_WIDTH     = 32,
    parameter ADDR_BITS      = 32,
    parameter BLOCK_ID_START = 5 ,
    parameter R_WIDTH        = 6 ,
    parameter MICROOP        = 5 ,
    parameter ROB_TICKET     = 3 ,
    parameter DEPTH          = 4
) (
    input  logic                  clk               ,
    input  logic                  rst_n             ,
    //Write Port
    input  logic                  push              ,
    input  logic [ ADDR_BITS-1:0] write_address     ,
    input  logic [DATA_WIDTH-1:0] write_data        ,
    input  logic [   MICROOP-1:0] write_microop     ,
    input  logic [   R_WIDTH-1:0] write_dest        ,
    input  logic [ROB_TICKET-1:0] write_ticket      ,
    input  logic                  write_isfetched   ,
    //Search Port & Forward
    input  logic [ ADDR_BITS-1:0] search_address    ,
    input  logic [   MICROOP-1:0] search_microop_in ,
    output logic [DATA_WIDTH-1:0] search_data       ,
    output logic [   MICROOP-1:0] search_microop    ,
    output logic [   R_WIDTH-1:0] search_dest       ,
    output logic [ROB_TICKET-1:0] search_ticket     ,
    output logic                  search_valid_hit  ,
    output logic                  search_partial_hit,
    //Update Port
    input  logic                  valid_update      ,
    input  logic [ ADDR_BITS-1:0] update_address    ,
    //Head Output
    input  logic                  pop               ,
    output logic                  head_isfetched    ,
    output logic [ ADDR_BITS-1:0] head_address      ,
    output logic [DATA_WIDTH-1:0] head_data         ,
    output logic [   MICROOP-1:0] head_microop      ,
    output logic [   R_WIDTH-1:0] head_dest         ,
    output logic [ROB_TICKET-1:0] head_ticket       ,
    //Status Port
    output logic                  valid             ,
    output logic                  ready
);

    localparam INFO_WIDTH = R_WIDTH + MICROOP;
	// #Memory Arrays#
    logic [DEPTH-1:0][ADDR_BITS-1:0]  saved_address;
    logic [DEPTH-1:0][DATA_WIDTH-1:0] saved_data;
    logic [DEPTH-1:0][ROB_TICKET-1:0] saved_ticket;
    logic [DEPTH-1:0][INFO_WIDTH-1:0] saved_info;
    logic [INFO_WIDTH-1:0]            head_info, search_info;
    logic [DEPTH-1:0]                 saved_valid, saved_isfetched;


    // #Internal Signals#
    logic [    DEPTH-1:0] head, tail, stat_counter ;
    logic [    DEPTH-1:0] matched_update, matched_search_main, matched_search_sec, matched_search;
    logic                 will_update, one_found, microop_ok;

    localparam int LD_BF_SIZE = $bits(saved_address) + $bits(saved_ticket) + $bits(saved_info);
    localparam int ST_BF_SIZE = $bits(saved_address) + $bits(saved_data) + $bits(saved_ticket) + $bits(saved_info);

    assign valid = ~stat_counter[0];
    assign ready = ~stat_counter[DEPTH-1];


    //Create the Search Match Vectors
    always_comb begin : MatchSearch
        for (int i = 0; i < DEPTH; i++) begin
            matched_search_main[i] = saved_valid[i] ? (search_address[ADDR_BITS-1:BLOCK_ID_START]==saved_address[i][ADDR_BITS-1:BLOCK_ID_START]) : 1'b0;
            matched_search_sec[i] = saved_valid[i] ? (search_address[BLOCK_ID_START-1:0]==saved_address[i][BLOCK_ID_START-1:0]) : 1'b0;
        end
        for (int i = 0; i < DEPTH; i++) begin
            matched_search[i] = matched_search_main[i] & matched_search_sec[i];// & microop_ok;
        end
    end
    //Check the Microops for forwarding hazards
    always_comb begin : MicroopOk
        if(search_microop_in==5'b00001) begin
            //load==LW
            microop_ok = (search_microop == 5'b00110);
        end else if(search_microop_in==5'b00010 | search_microop_in==5'b00011) begin
            //load==LH
            microop_ok = (search_microop == 5'b00111 | search_microop == 5'b00110);
        end else if(search_microop_in==5'b00100 | search_microop_in==5'b00101) begin
            //load==LB
            microop_ok = 1;
        end else begin
            microop_ok = 0;
        end
    end
    // assign search_valid_hit = |matched_search;
    always_comb begin : ValidHit
        search_valid_hit = 0;
        for (int i = 0; i < DEPTH; i++) begin
            if(matched_search[i] && microop_ok) begin
                search_valid_hit = 1;
            end
        end
    end
    assign search_partial_hit = |matched_search_main;
    //Search the Locations to update as Fetched
    always_comb begin : matchUpdate
        for (int i = 0; i < DEPTH; i++) begin
            matched_update[i] = saved_valid[i] ? (update_address[ADDR_BITS-1:BLOCK_ID_START]==saved_address[i][ADDR_BITS-1:BLOCK_ID_START]) : 1'b0;
        end
    end
    assign will_update = |matched_update & valid_update;
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
                saved_ticket[i]  <= write_ticket;
                saved_info[i]    <= {write_dest,write_microop};
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
                    saved_valid[i]   <= 1'b1;
                end else if(pop && head[i]) begin
                    saved_valid[i]   <= 1'b0;
                end
            end
        end
    end
    // Memory Management (is_fetched)
    always_ff @(posedge clk or negedge rst_n) begin : MemoryFetched
        if(!rst_n) begin
            saved_isfetched <= 'b0;
        end else begin
            for (int i = 0; i < DEPTH; i++) begin
                if(push && tail[i]) begin
                    saved_isfetched[i] <= write_isfetched;
                end else if(will_update && matched_update[i]) begin
                    saved_isfetched[i] <= 1'b1;
                end
            end
        end
    end

    //HEAD OUTPUTS
    // Pick the Address Output
    and_or_mux #(
        .INPUTS    (DEPTH     ),
        .DW        (ADDR_BITS)
    ) mux_addr (
        .data_in (saved_address ),
        .sel     (head       ),
        .data_out(head_address)
    );
    // Pick the Data Output
    and_or_mux #(
        .INPUTS    (DEPTH     ),
        .DW        (DATA_WIDTH)
    ) mux_data (
        .data_in (saved_data ),
        .sel     (head       ),
        .data_out(head_data)
    );

    //Pick the Microop/Destination Output
    and_or_mux #(
        .INPUTS    (DEPTH  ),
        .DW        (INFO_WIDTH)
    ) mux_info (
        .data_in (saved_info ),
        .sel     (head       ),
        .data_out(head_info)
    );
    assign head_microop = head_info[0 +: MICROOP];
    assign head_dest    = head_info[MICROOP +: R_WIDTH];
    //Pick the Ticket Output
    and_or_mux #(
        .INPUTS    (DEPTH     ),
        .DW        (ROB_TICKET)
    ) mux_ticket (
        .data_in (saved_ticket ),
        .sel     (head         ),
        .data_out(head_ticket)
    );
    //Pick the is_fetched Output
    and_or_mux #(
        .INPUTS    (DEPTH     ),
        .DW        (1)
    ) mux_is_fetched (
        .data_in (saved_isfetched ),
        .sel     (head         ),
        .data_out(head_isfetched)
    );


    //SEARCH OUTPUTS
    // Pick the Data Output
    and_or_mux #(
        .INPUTS    (DEPTH     ),
        .DW        (DATA_WIDTH)
    ) mux_data_s (
        .data_in (saved_data ),
        .sel     (matched_search),
        .data_out(search_data)
    );
    //Pick the Microop/Destination Output
    and_or_mux #(
        .INPUTS    (DEPTH  ),
        .DW        (INFO_WIDTH)
    ) mux_info_s (
        .data_in (saved_info ),
        .sel     (matched_search),
        .data_out(search_info)
    );
    assign search_microop = search_info[0 +: MICROOP];
    assign search_dest    = search_info[MICROOP +: R_WIDTH];
    //Pick the Ticket Output
    and_or_mux #(
        .INPUTS    (DEPTH     ),
        .DW        (ROB_TICKET)
    ) mux_ticket_s (
        .data_in (saved_ticket ),
        .sel     (matched_search),
        .data_out(search_ticket)
    );

    assert property (@(posedge clk) disable iff(!rst_n) push |-> ready) else $error("ERROR:LD_ST Buffer: Push on Full");
    assert property (@(posedge clk) disable iff(!rst_n) pop |-> valid) else $error("ERROR:LD_ST Buffer: Pop on Empty");

endmodule