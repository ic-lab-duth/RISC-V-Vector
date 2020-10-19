/*
 * @info Wait Buffer Module
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
module wait_buffer #(
    parameter DATA_WIDTH     = 32,
    parameter ADDR_BITS      = 32,
    parameter BLOCK_ID_START = 5 ,
    parameter R_WIDTH        = 6 ,
    parameter MICROOP        = 5 ,
    parameter ROB_TICKET     = 3 ,
    parameter DEPTH          = 8  )
    //Interfaces
    (input logic                  clk,
    input  logic                  rst_n,
    //Write Port
    input  logic                  write_enable,
    input  logic                  write_is_store,
    input  logic[ADDR_BITS-1:0]   write_address,
    input  logic[DATA_WIDTH-1:0]  write_data,
    input  logic[MICROOP-1 : 0]   write_microop,
    input  logic[R_WIDTH-1 : 0]   write_dest,
    input  logic[ROB_TICKET-1 : 0]write_ticket,
    //Search Port
    input  logic                  search_invalidate,
    output logic                  search_is_store,
    input  logic[ADDR_BITS-1:0]   search_address,
    input  logic[MICROOP-1 : 0]   search_microop_in,
    output logic[ADDR_BITS-1:0]   search_address_o,
    output logic[DATA_WIDTH-1:0]  search_data,
    output logic[DATA_WIDTH-1:0]  search_frw_data,
    output logic[MICROOP-1 : 0]   search_microop,
    output logic[R_WIDTH-1 : 0]   search_dest,
    output logic[ROB_TICKET-1 : 0]search_ticket,
    output logic                  search_valid_hit,
    //Status Port
    output logic                  valid,
    output logic                  ready,
    output logic                  search_found_one,
    output logic                  search_found_multi,
    output logic                  in_walk_mode
);
    localparam INFO_WIDTH = MICROOP + R_WIDTH + ROB_TICKET;
    // #Memory Arrays#
    logic [DEPTH-1:0][ADDR_BITS-1:0]  saved_address;
    logic [DEPTH-1:0][DATA_WIDTH-1:0] saved_data;
    logic [DEPTH-1:0][INFO_WIDTH-1:0] saved_info;
    logic [INFO_WIDTH-1:0]            search_info;
    logic [DEPTH-1:0]                 saved_is_store, saved_valid;

    // #Internal Signals#
    logic [    DEPTH-1:0] head, tail, peek, tail_reversed, stat_counter, arb_priority ;
    logic [    DEPTH-1:0] matched_search_main, matched_search_sec, matched, match_picked, forward_matched;
    logic                 pop, one_found, multi_found, microop_ok;

    localparam int WT_BF_SIZE = $bits(saved_info) + $bits(saved_data) + $bits(saved_address);
    //FSM Type
    typedef enum logic {IDLE, WALK} buffer_mode;
    buffer_mode mode;

    assign valid = ~stat_counter[0];
    assign ready = ~stat_counter[DEPTH-1];
    assign in_walk_mode = (mode==WALK);

    // Search in the Array
    always_comb begin : Search
        for (int i = 0; i < DEPTH; i++) begin
            matched_search_main[i] = saved_valid[i] ? (search_address[ADDR_BITS-1:BLOCK_ID_START]==saved_address[i][ADDR_BITS-1:BLOCK_ID_START]) : 1'b0;
            matched_search_sec[i]  = saved_valid[i] ? (search_address[BLOCK_ID_START-1:0]==saved_address[i][BLOCK_ID_START-1:0]) : 1'b0;
            // matched[i]  = saved_valid[i] ? (search_address[31:2] == saved_address[i][31:2]) : 1'b0;
            matched[i]  = matched_search_main[i] & matched_search_sec[i] & microop_ok;
        end
    end
    assign search_valid_hit = |matched;
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
    assign arb_priority = (mode==IDLE) ? head : {peek[DEPTH-2:0], peek[DEPTH-1]};
    //Initialize the Arbiter (oldest entry->newest entry)
    arbiter #(DEPTH)
    arbiter(
        .request_i      (matched_search_main), //instead of matched
        .priority_i     (arb_priority),
        .grant_o        (match_picked),
        .anygnt_o       (one_found)
        );
    //Initialize the One-Hot Detector
    onehot_detect #(DEPTH)
    onehot_detect  (
        .vec_in         (matched_search_main), //- matched <> matched_search_main
        .exactly_one    (),
        .more_than_one  (multi_found)
        );

    // Peek Pointer Management
    always_ff @(posedge clk or negedge rst_n) begin : PeekManagement
        if(!rst_n) begin
            peek <= 1;
        end else begin
            if(mode==IDLE && search_invalidate) begin
                peek <= match_picked;
            end else if(mode==IDLE && pop) begin
                peek <= peek << 1;
            end else if(mode==WALK && !multi_found) begin
                peek <= head;
            end else if(mode==WALK) begin
                peek <= match_picked;
            end else begin
                peek <= head;
            end
        end
    end
    //FSM Management
    always_ff @(posedge clk or negedge rst_n) begin : proc_
        if(~rst_n) begin
            mode <= IDLE;
        end else begin
            unique case (mode)
                IDLE: if(search_invalidate) begin
                          mode <= WALK;
                      end else begin
                          mode <= IDLE;
                      end
                WALK: if(!multi_found) begin
                          mode <= IDLE;
                      end else begin
                          mode <= WALK;
                      end
            endcase
        end
    end
    // Create the Rest of the Outputs
    assign search_found_multi = multi_found;
    assign search_found_one   = one_found;

    // Create the Pop Command
    always_comb begin : PopCommand
        pop = 0;
        for (int i = 0; i < DEPTH; i++) begin
            if (head[i] && !saved_valid[i]) begin
                pop = valid;
            end
        end
    end
    //Tail Management (moves on new pops)
    always_ff @(posedge clk or negedge rst_n) begin : TailManagement
        if(!rst_n) begin
            tail <= 1;
        end else begin
            if (write_enable) tail <= {tail[DEPTH-2:0], tail[DEPTH-1]};
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
            if (write_enable & !pop) begin
                // shift left status counter (increment)
                stat_counter <= stat_counter << 1;
            end else if (!write_enable &  pop) begin
                // shift right status counter (decrement)
                stat_counter <= stat_counter >> 1;
            end
        end
    end
    // Memory Management (Data Write)
    always_ff @(posedge clk) begin : Memory
        for (int i = 0; i < DEPTH; i++) begin
            if(write_enable && tail[i]) begin
                saved_is_store[i] <= write_is_store;
                saved_address[i]  <= write_address;
                saved_data[i]     <= write_data;
                saved_info[i]     <= {write_microop,write_dest,write_ticket};
            end
        end
    end
    // Memory Management (Validity)
    always_ff @(posedge clk or negedge rst_n) begin : Memory_Validity
        if(!rst_n) begin
            saved_valid <= 'b0;
        end else begin
            for (int i = 0; i < DEPTH; i++) begin
                if(write_enable && tail[i]) begin
                    saved_valid[i] <= 1'b1;
                end else if(mode==WALK && peek[i]) begin
                    saved_valid[i] <= 1'b0;
                end
            end
        end
    end
    logic [    DEPTH-1:0] matched_reversed,final_frw_matched,forward_matched_r;
    always_comb begin : InvertPointers
        for (int i = 0; i < DEPTH; i++) begin
            tail_reversed[i] = tail[DEPTH-1-i];
            matched_reversed[i] = matched[DEPTH-1-i];
            final_frw_matched[i]  = forward_matched_r[DEPTH-1-i];
        end

    end
    //FORWARDED OUTPUTS
    //Forwarded
     // Data Arbiter (newest entry -> oldest entry)
    arbiter #(DEPTH)
    frw_arbiter(
        .request_i      (matched_reversed),
        .priority_i     (tail_reversed),
        .grant_o        (forward_matched_r),
        .anygnt_o       ()
        );
    // Pick the Forwarded Data Output
    and_or_mux #(
        .INPUTS    (DEPTH     ),
        .DW        (DATA_WIDTH)
    ) mux_frw_data (
        .data_in (saved_data ),
        .sel     (final_frw_matched),
        .data_out(search_frw_data)
    );

    //SEARCH OUTPUTS (+Walk Mode Outputs)
    // Pick the Address Output
    and_or_mux #(
        .INPUTS    (DEPTH     ),
        .DW        (ADDR_BITS)
    ) mux_addr (
        .data_in (saved_address ),
        .sel     (peek       ),
        .data_out(search_address_o)
    );
    // Pick the Data Output
    and_or_mux #(
        .INPUTS    (DEPTH     ),
        .DW        (DATA_WIDTH)
    ) mux_data (
        .data_in (saved_data ),
        .sel     (peek       ),
        .data_out(search_data)
    );

    //Pick the is_store Output
    and_or_mux #(
        .INPUTS    (DEPTH),
        .DW        (1    )
    ) mux_is_store (
        .data_in (saved_is_store ),
        .sel     (peek           ),
        .data_out(search_is_store)
    );
    //Pick the Ticket/Microoperation/Destination Output
    and_or_mux #(
        .INPUTS    (DEPTH     ),
        .DW        (INFO_WIDTH)
    ) mux_info (
        .data_in (saved_info ),
        .sel     (peek         ),
        .data_out(search_info)
    );
    assign search_ticket  = search_info[0 +: ROB_TICKET];
    assign search_dest    = search_info[ROB_TICKET +: R_WIDTH];
    assign search_microop = search_info[ROB_TICKET+R_WIDTH +: MICROOP];

    //Pick the valid match bit
    // and_or_mux #(
    //     .INPUTS    (DEPTH),
    //     .DW        (1    )
    // ) mux_valid (
    //     .data_in (matched ),
    //     .sel     (peek           ),
    //     .data_out(search_valid_hit)
    // );

    assert property (@(posedge clk) disable iff(!rst_n) write_enable |-> ready) else $error("ERROR:WT Buffer: Push on Full");
endmodule