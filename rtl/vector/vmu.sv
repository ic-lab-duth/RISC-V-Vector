/*
* @info Vector Memory Unit
*
* @author VLSI Lab, EE dept., Democritus University of Thrace
*
*/
`ifdef MODEL_TECH
    `include "vstructs.sv"
`endif
module vmu #(
    parameter int REQ_DATA_WIDTH     = 256,
    parameter int VECTOR_REGISTERS   = 32 ,
    parameter int VECTOR_LANES       = 8  ,
    parameter int DATA_WIDTH         = 32 ,
    parameter int ADDR_WIDTH         = 32 ,
    parameter int MICROOP_WIDTH      = 5  ,
    parameter int VECTOR_TICKET_BITS = 4
) (
    input  logic                                                              clk                ,
    input  logic                                                              rst_n              ,
    output logic                                                              vmu_idle_o         ,
    //Instruction In
    input  logic                                                              valid_in           ,
    input  memory_remapped_v_instr                                            instr_in           ,
    output logic                                                              ready_o            ,
    //Cache Interface (OUT)
    output logic                                                              mem_req_valid_o    ,
    output vector_mem_req                                                     mem_req_o          ,
    //Cache Interface (IN)
    input  logic                                                              cache_ready_i      ,
    input  logic                                                              mem_resp_valid_i   ,
    input  vector_mem_resp                                                    mem_resp_i         ,
    //RF Interface - Loads
    output logic [$clog2(VECTOR_REGISTERS)-1:0]                               rd_addr_0_o        ,
    input  logic [ VECTOR_LANES*DATA_WIDTH-1:0]                               rd_data_0_i        ,
    input  logic                                                              rd_pending_0_i     ,
    input  logic [      VECTOR_TICKET_BITS-1:0]                               rd_ticket_0_i      ,
    //RF Interface - Stores
    output logic [$clog2(VECTOR_REGISTERS)-1:0]                               rd_addr_1_o        ,
    input  logic [ VECTOR_LANES*DATA_WIDTH-1:0]                               rd_data_1_i        ,
    input  logic                                                              rd_pending_1_i     ,
    input  logic [      VECTOR_TICKET_BITS-1:0]                               rd_ticket_1_i      ,
    output logic [$clog2(VECTOR_REGISTERS)-1:0]                               rd_addr_2_o        ,
    input  logic [ VECTOR_LANES*DATA_WIDTH-1:0]                               rd_data_2_i        ,
    input  logic                                                              rd_pending_2_i     ,
    input  logic [      VECTOR_TICKET_BITS-1:0]                               rd_ticket_2_i      ,
    //RF Writeback Interface
    output logic [            VECTOR_LANES-1:0]                               wrtbck_en_o        ,
    output logic [$clog2(VECTOR_REGISTERS)-1:0]                               wrtbck_reg_o       ,
    output logic [ VECTOR_LANES*DATA_WIDTH-1:0]                               wrtbck_data_o      ,
    output logic [      VECTOR_TICKET_BITS-1:0]                               wrtbck_ticket_o    ,
    //RF Writeback Probing Interface
    output logic [                         3:0][$clog2(VECTOR_REGISTERS)-1:0] wrtbck_prb_reg_o   ,
    input  logic [                         3:0]                               wrtbck_prb_locked_i,
    input  logic [                         3:0][      VECTOR_TICKET_BITS-1:0] wrtbck_prb_ticket_i,
    //Unlock Interface
    output logic                                                              unlock_en_o        ,
    output logic [$clog2(VECTOR_REGISTERS)-1:0]                               unlock_reg_a_o     ,
    output logic [$clog2(VECTOR_REGISTERS)-1:0]                               unlock_reg_b_o     ,
    output logic [      VECTOR_TICKET_BITS-1:0]                               unlock_ticket_o
);

    //=======================================================
    // WIRES
    //=======================================================
    logic                                load_unlock_en    ;
    logic [$clog2(VECTOR_REGISTERS)-1:0] load_unlock_reg_a ;
    logic [$clog2(VECTOR_REGISTERS)-1:0] load_unlock_reg_b ;
    logic [      VECTOR_TICKET_BITS-1:0] load_unlock_ticket;
    logic [              ADDR_WIDTH-1:0] load_start_addr   ;
    logic [              ADDR_WIDTH-1:0] load_end_addr     ;
    logic [              ADDR_WIDTH-1:0] load_req_addr     ;
    logic [           MICROOP_WIDTH-1:0] load_req_microop  ;
    logic [  $clog2(REQ_DATA_WIDTH/8):0] load_req_size     ;
    logic [      $clog2(VECTOR_LANES):0] load_req_ticket   ;
    logic                                ld_can_inteleave  ;
    logic [            VECTOR_LANES-1:0] ld_wb_en          ;
    logic [$clog2(VECTOR_REGISTERS)-1:0] ld_wb_reg         ;
    logic [ VECTOR_LANES*DATA_WIDTH-1:0] ld_wb_data        ;
    logic [      VECTOR_TICKET_BITS-1:0] ld_wb_ticket      ;

    logic                                store_unlock_en    ;
    logic [$clog2(VECTOR_REGISTERS)-1:0] store_unlock_reg_a ;
    logic [$clog2(VECTOR_REGISTERS)-1:0] store_unlock_reg_b ;
    logic [      VECTOR_TICKET_BITS-1:0] store_unlock_ticket;
    logic [              ADDR_WIDTH-1:0] store_start_addr   ;
    logic [              ADDR_WIDTH-1:0] store_end_addr     ;
    logic [              ADDR_WIDTH-1:0] store_req_addr     ;
    logic [           MICROOP_WIDTH-1:0] store_req_microop  ;
    logic [  $clog2(REQ_DATA_WIDTH/8):0] store_req_size     ;
    logic [          REQ_DATA_WIDTH-1:0] store_req_data     ;
    logic                                st_can_interleave  ;

    logic                                toepl_unlock_en    ;
    logic [$clog2(VECTOR_REGISTERS)-1:0] toepl_unlock_reg_a ;
    logic [$clog2(VECTOR_REGISTERS)-1:0] toepl_unlock_reg_b ;
    logic [      VECTOR_TICKET_BITS-1:0] toepl_unlock_ticket;
    logic [              ADDR_WIDTH-1:0] toepl_req_addr     ;
    logic [           MICROOP_WIDTH-1:0] toepl_req_microop  ;
    logic [  $clog2(REQ_DATA_WIDTH/8):0] toepl_req_size     ;
    logic [      $clog2(VECTOR_LANES):0] toepl_req_ticket   ;
    logic [            VECTOR_LANES-1:0] tp_wb_en           ;
    logic [$clog2(VECTOR_REGISTERS)-1:0] tp_wb_reg          ;
    logic [ VECTOR_LANES*DATA_WIDTH-1:0] tp_wb_data         ;
    logic [      VECTOR_TICKET_BITS-1:0] tp_wb_ticket       ;

    logic [1:0] wb_grant    ;
    logic [1:0] wb_request  ;
    logic [2:0] is_busy     ;
    logic [1:0] tail        ;
    logic       fifo_ready  ;
    logic       is_load     ;
    logic       is_store    ;
    logic       is_toepl    ;
    logic       is_reconf   ;
    logic       push_load   ;
    logic       push_store  ;
    logic       push_toepl  ;
    logic       load_ready  ;
    logic       store_ready ;
    logic       toepl_ready ;
    logic       load_starts ;
    logic       store_starts;
    logic       toepl_starts;
    logic       load_ends   ;
    logic       store_ends  ;
    logic       toepl_ends  ;
    logic       any_request ;
    logic       any_grant   ;
    logic       ld_grant    ;
    logic       st_grant    ;
    logic       tp_grant    ;
    //Create the ready out signal
    assign ready_o = valid_in & is_load  ? (load_ready  & fifo_ready) :
                     valid_in & is_store ? (store_ready & fifo_ready) :
                     valid_in & is_toepl ? (toepl_ready & fifo_ready) :
                                           (load_ready & store_ready & toepl_ready & fifo_ready);

    assign vmu_idle_o = ~|is_busy;

    //Pick the Outputs
    assign unlock_en_o     = load_unlock_en | store_unlock_en | toepl_unlock_en;

    assign unlock_reg_a_o  = wb_grant[1]    ? toepl_unlock_reg_a  :
                             load_unlock_en ? load_unlock_reg_a   :
                                              store_unlock_reg_a;

    assign unlock_reg_b_o  = wb_grant[1]    ? toepl_unlock_reg_b  :
                             load_unlock_en ? load_unlock_reg_b   :
                                              store_unlock_reg_b;

    assign unlock_ticket_o = wb_grant[1]    ? toepl_unlock_ticket :
                             load_unlock_en ? load_unlock_ticket  :
                                              store_unlock_ticket;

    assign mem_req_valid_o   = any_grant;
    assign mem_req_o.address = ld_grant ? load_req_addr     :
                               st_grant ? store_req_addr    :
                                          toepl_req_addr;

    assign mem_req_o.microop = ld_grant ? load_req_microop  :
                               st_grant ? store_req_microop :
                                          toepl_req_microop;

    assign mem_req_o.size    = ld_grant ? load_req_size     :
                               st_grant ? store_req_size    :
                                          toepl_req_size;

    assign mem_req_o.ticket  = ld_grant ? load_req_ticket   :
                                          toepl_req_ticket;

    assign mem_req_o.data    = store_req_data;

    assign wrtbck_en_o     = wb_grant[0] ? ld_wb_en     : tp_wb_en;
    assign wrtbck_reg_o    = wb_grant[0] ? ld_wb_reg    : tp_wb_reg;
    assign wrtbck_data_o   = wb_grant[0] ? ld_wb_data   : tp_wb_data;
    assign wrtbck_ticket_o = wb_grant[0] ? ld_wb_ticket : tp_wb_ticket;

    //Push the instruction to the correct engine
    assign is_load   = ~instr_in.reconfigure & instr_in.microop[`LD_BIT]  & ~is_toepl;
    assign is_store  = ~instr_in.reconfigure & ~instr_in.microop[`LD_BIT] & ~is_toepl;
    assign is_toepl  = ~instr_in.reconfigure & (instr_in.microop === 7'b1110011 | instr_in.microop === 7'b1010011);
    assign is_reconf =  instr_in.reconfigure;

    always_comb begin
        if(is_reconf) begin //reconfiguration must happen simultaneously
            push_load  = valid_in & load_ready & store_ready & toepl_ready;
            push_store = valid_in & load_ready & store_ready & toepl_ready;
            push_toepl = valid_in & load_ready & store_ready & toepl_ready;
        end else begin
            push_load  = valid_in & is_load  & load_ready  & fifo_ready;
            push_store = valid_in & is_store & store_ready & fifo_ready;
            push_toepl = valid_in & is_toepl & toepl_ready & fifo_ready;
        end
    end

    // LOAD ENGINE
    vmu_ld_eng #(
        .REQ_DATA_WIDTH    (REQ_DATA_WIDTH    ),
        .VECTOR_REGISTERS  (VECTOR_REGISTERS  ),
        .VECTOR_LANES      (VECTOR_LANES      ),
        .DATA_WIDTH        (DATA_WIDTH        ),
        .ADDR_WIDTH        (ADDR_WIDTH        ),
        .MICROOP_WIDTH     (MICROOP_WIDTH     ),
        .VECTOR_TICKET_BITS(VECTOR_TICKET_BITS)
    ) vmu_ld_eng (
        .clk                (clk                   ),
        .rst_n              (rst_n                 ),
        //input Interface
        .valid_in           (push_load             ),
        .instr_in           (instr_in              ),
        .ready_o            (load_ready            ),
        //RF read Interface (for indexed stride)
        .rd_addr_o          (rd_addr_0_o           ),
        .rd_data_i          (rd_data_0_i           ),
        .rd_pending_i       (rd_pending_0_i        ),
        .rd_ticket_i        (rd_ticket_0_i         ),
        //RF write Interface
        .wrtbck_grant_i     (wb_grant[0]           ),
        .wrtbck_req_o       (wb_request[0]         ),
        .wrtbck_en_o        (ld_wb_en              ),
        .wrtbck_reg_o       (ld_wb_reg             ),
        .wrtbck_data_o      (ld_wb_data            ),
        .wrtbck_ticket_o    (ld_wb_ticket          ),
        //RF Writeback Probing Interface
        .wrtbck_reg_a_o     (wrtbck_prb_reg_o[0]   ),
        .wrtbck_locked_a_i  (wrtbck_prb_locked_i[0]),
        .wrtbck_ticket_a_i  (wrtbck_prb_ticket_i[0]),
        .wrtbck_reg_b_o     (wrtbck_prb_reg_o[1]   ),
        .wrtbck_locked_b_i  (wrtbck_prb_locked_i[1]),
        .wrtbck_ticket_b_i  (wrtbck_prb_ticket_i[1]),
        //Unlock Interface
        .unlock_en_o        (load_unlock_en        ),
        .unlock_reg_a_o     (load_unlock_reg_a     ),
        .unlock_reg_b_o     (load_unlock_reg_b     ),
        .unlock_ticket_o    (load_unlock_ticket    ),
        //Request Interface
        .grant_i            (ld_grant              ),
        .req_en_o           (ld_request            ),
        .req_addr_o         (load_req_addr         ),
        .req_microop_o      (load_req_microop      ),
        .req_size_o         (load_req_size         ),
        .req_ticket_o       (load_req_ticket       ),
        // Incoming Data from Cache
        .resp_valid_i       (mem_resp_valid_i      ),
        .resp_ticket_i      (mem_resp_i.ticket     ),
        .resp_size_i        (mem_resp_i.size       ),
        .resp_data_i        (mem_resp_i.data       ),
        //Sync Interface
        .is_busy_o          (is_busy[0]            ),
        .can_be_inteleaved_o(ld_can_inteleave      ),
        .start_addr_o       (load_start_addr       ),
        .end_addr_o         (load_end_addr         )
    );
    //STORE ENGINE
    vmu_st_eng #(
        .REQ_DATA_WIDTH    (REQ_DATA_WIDTH    ),
        .VECTOR_REGISTERS  (VECTOR_REGISTERS  ),
        .VECTOR_LANES      (VECTOR_LANES      ),
        .DATA_WIDTH        (DATA_WIDTH        ),
        .ADDR_WIDTH        (ADDR_WIDTH        ),
        .MICROOP_WIDTH     (MICROOP_WIDTH     ),
        .VECTOR_TICKET_BITS(VECTOR_TICKET_BITS)
    ) vmu_st_eng (
        .clk                (clk                ),
        .rst_n              (rst_n              ),
        //Input Interface
        .valid_in           (push_store         ),
        .instr_in           (instr_in           ),
        .ready_o            (store_ready        ),
        //RF Interface (per vreg)
        .rd_addr_1_o        (rd_addr_1_o        ),
        .rd_data_1_i        (rd_data_1_i        ),
        .rd_pending_1_i     (rd_pending_1_i     ),
        .rd_ticket_1_i      (rd_ticket_1_i      ),
        //RF Interface (for indexed stride)
        .rd_addr_2_o        (rd_addr_2_o        ),
        .rd_data_2_i        (rd_data_2_i        ),
        .rd_pending_2_i     (rd_pending_2_i     ),
        .rd_ticket_2_i      (rd_ticket_2_i      ),
        //Unlock Interface
        .unlock_en_o        (store_unlock_en    ),
        .unlock_reg_a_o     (store_unlock_reg_a ),
        .unlock_reg_b_o     (store_unlock_reg_b ),
        .unlock_ticket_o    (store_unlock_ticket),
        //Request Interface
        .req_en_o           (st_request         ),
        .grant_i            (st_grant           ),
        .req_addr_o         (store_req_addr     ),
        .req_microop_o      (store_req_microop  ),
        .req_size_o         (store_req_size     ),
        .req_data_o         (store_req_data     ),
        //Sync Interface
        .can_be_inteleaved_o(st_can_interleave  ),
        .is_busy_o          (is_busy[1]         ),
        .start_addr_o       (store_start_addr   ),
        .end_addr_o         (store_end_addr     )
    );
    //TOEPLITZ PREFETCHER
    vmu_tp_eng #(
        .REQ_DATA_WIDTH    (REQ_DATA_WIDTH    ),
        .VECTOR_REGISTERS  (VECTOR_REGISTERS  ),
        .VECTOR_LANES      (VECTOR_LANES      ),
        .DATA_WIDTH        (DATA_WIDTH        ),
        .ADDR_WIDTH        (ADDR_WIDTH        ),
        .MICROOP_WIDTH     (MICROOP_WIDTH     ),
        .VECTOR_TICKET_BITS(VECTOR_TICKET_BITS)
    ) vmu_tp_eng (
        .clk              (clk                   ),
        .rst_n            (rst_n                 ),
        //input Interface
        .valid_in         (push_toepl            ),
        .instr_in         (instr_in              ),
        .ready_o          (toepl_ready           ),
        //RF write Interface
        .wrtbck_grant_i   (wb_grant[1]           ),
        .wrtbck_req_o     (wb_request[1]         ),
        .wrtbck_en_o      (tp_wb_en              ),
        .wrtbck_reg_o     (tp_wb_reg             ),
        .wrtbck_data_o    (tp_wb_data            ),
        .wrtbck_ticket_o  (tp_wb_ticket          ),
        //RF Writeback Probing Interface
        .wrtbck_reg_a_o   (wrtbck_prb_reg_o[2]   ),
        .wrtbck_locked_a_i(wrtbck_prb_locked_i[2]),
        .wrtbck_ticket_a_i(wrtbck_prb_ticket_i[2]),
        .wrtbck_reg_b_o   (wrtbck_prb_reg_o[3]   ),
        .wrtbck_locked_b_i(wrtbck_prb_locked_i[3]),
        .wrtbck_ticket_b_i(wrtbck_prb_ticket_i[3]),
        //Unlock Interface
        .unlock_en_o      (toepl_unlock_en       ),
        .unlock_reg_a_o   (toepl_unlock_reg_a    ),
        .unlock_reg_b_o   (toepl_unlock_reg_b    ),
        .unlock_ticket_o  (toepl_unlock_ticket   ),
        //Request Interface
        .grant_i          (tp_grant              ),
        .req_en_o         (tp_request            ),
        .req_addr_o       (toepl_req_addr        ),
        .req_microop_o    (toepl_req_microop     ),
        .req_size_o       (toepl_req_size        ),
        .req_ticket_o     (toepl_req_ticket      ),
        // Incoming Data from Cache
        .resp_valid_i     (mem_resp_valid_i      ),
        .resp_ticket_i    (mem_resp_i.ticket     ),
        .resp_size_i      (mem_resp_i.size       ),
        .resp_data_i      (mem_resp_i.data       ),
        //Sync Interface
        .is_busy_o        (is_busy[2]            )
    );

    //=======================================================
    //Keep track of the oldest LD/TP instruction in the engine
    //and provide the grants for the writeback access
    //=======================================================
    logic [1:0] is_older               ;
    logic [1:0] nxt_is_older           ;
    logic [1:0] high_priority_grant    ;
    logic       any_high_priority_grant;
    logic       new_ld_starts          ;

    //Requests by the oldest instruction are considered high priority
    assign wb_grant = ({2{ any_high_priority_grant}} & high_priority_grant) |
                      ({2{~any_high_priority_grant}} & wb_request          );

    assign any_high_priority_grant = |high_priority_grant;
    assign high_priority_grant     = is_older & wb_request;

    assign new_ld_starts = push_load | push_toepl;
    always_ff @(posedge clk or negedge rst_n) begin
        if(~rst_n) begin
            is_older <= '0;
        end else if(new_ld_starts) begin
            is_older <= nxt_is_older;
        end
    end

    always_comb begin
        if(new_ld_starts) begin //new load started
            nxt_is_older = is_busy[2] ? 2'b10 : //the old toepl is the oldest
                                        2'b01;  //the new load is the oldest
        end else begin //new toepl started (or nothing started)
            nxt_is_older = is_busy[0] ? 2'b01 : //the old load is the oldest
                                        2'b10;  //the new toepl is the oldest
        end
    end

    //=======================================================
    //Keep track of the oldest instruction in the engine
    //and provide the grants for the memory access
    //=======================================================
    logic [1:0] push_data;
    logic [1:0] pop_data;
    logic push;
    logic pop;

    assign load_starts  =  push_load & ~push_store & ~push_toepl;
    assign store_starts = ~push_load &  push_store & ~push_toepl;
    assign toepl_starts = ~push_load & ~push_store &  push_toepl;

    assign load_ends    = ~is_busy[0];
    assign store_ends   = ~is_busy[1];
    assign toepl_ends   = ~is_busy[2];

    assign any_request = ld_request | st_request | tp_request;
    assign any_grant   = ld_grant   | st_grant   | tp_grant;

    assign push_data = load_starts  ? 2'b01 :
                       store_starts ? 2'b10 : 2'b11;
    assign push = load_starts | store_starts | toepl_starts;
    // keep active instructions in vMU
    fifo_duth #(
        .DW   (2),
        .DEPTH(3)
    ) fifo_duth (
        .clk      (clk       ),
        .rst      (~rst_n    ),
        .push_data(push_data ),
        .push     (push      ),
        .ready    (fifo_ready),
        .pop_data (pop_data  ),
        .valid    (valid     ),
        .pop      (pop       )
    );

    assign ld_grant =  valid & cache_ready_i & pop_data == 2'b01 & ld_request;
    assign st_grant =  valid & cache_ready_i & pop_data == 2'b10 & st_request;
    // prefetcher gets access to idle cycles as well
    assign tp_grant = (valid & cache_ready_i & pop_data == 2'b11 & tp_request) |
                      (~ld_grant & ~st_grant & cache_ready_i     & tp_request);

    assign pop      = (valid & pop_data == 2'b01 & load_ends)  |
                      (valid & pop_data == 2'b10 & store_ends) |
                      (valid & pop_data == 2'b11 & toepl_ends);


`ifdef MODEL_TECH
    `include "vmu_sva.sv"
`endif

endmodule