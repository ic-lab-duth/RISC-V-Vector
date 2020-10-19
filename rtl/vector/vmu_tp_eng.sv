/*
* @info Vector Prefetch Unit
*
* @author VLSI Lab, EE dept., Democritus University of Thrace
*
*/
`ifdef MODEL_TECH
    `include "vstructs.sv"
`endif
module vmu_tp_eng #(
    parameter int REQ_DATA_WIDTH     = 256,
    parameter int VECTOR_REGISTERS   = 32 ,
    parameter int VECTOR_LANES       = 8  ,
    parameter int DATA_WIDTH         = 32 ,
    parameter int ADDR_WIDTH         = 32 ,
    parameter int MICROOP_WIDTH      = 5  ,
    parameter int VECTOR_TICKET_BITS = 4
) (
    input  logic                                clk              ,
    input  logic                                rst_n            ,
    //Input Interface
    input  logic                                valid_in         ,
    input  memory_remapped_v_instr              instr_in         ,
    output logic                                ready_o          ,
    //RF write Interface
    output logic                                wrtbck_req_o     ,
    input  logic                                wrtbck_grant_i   ,
    output logic [            VECTOR_LANES-1:0] wrtbck_en_o      ,
    output logic [$clog2(VECTOR_REGISTERS)-1:0] wrtbck_reg_o     ,
    output logic [ VECTOR_LANES*DATA_WIDTH-1:0] wrtbck_data_o    ,
    output logic [      VECTOR_TICKET_BITS-1:0] wrtbck_ticket_o  ,
    //RF Writeback Probing Interface
    output logic [$clog2(VECTOR_REGISTERS)-1:0] wrtbck_reg_a_o   ,
    input  logic                                wrtbck_locked_a_i,
    input  logic [      VECTOR_TICKET_BITS-1:0] wrtbck_ticket_a_i,
    output logic [$clog2(VECTOR_REGISTERS)-1:0] wrtbck_reg_b_o   ,
    input  logic                                wrtbck_locked_b_i,
    input  logic [      VECTOR_TICKET_BITS-1:0] wrtbck_ticket_b_i,
    //Unlock Interface
    output logic                                unlock_en_o        ,
    output logic [$clog2(VECTOR_REGISTERS)-1:0] unlock_reg_a_o     ,
    output logic [$clog2(VECTOR_REGISTERS)-1:0] unlock_reg_b_o     ,
    output logic [      VECTOR_TICKET_BITS-1:0] unlock_ticket_o    ,
    //Request Interface
    input  logic                                grant_i          ,
    output logic                                req_en_o         ,
    output logic [              ADDR_WIDTH-1:0] req_addr_o       ,
    output logic [           MICROOP_WIDTH-1:0] req_microop_o    ,
    output logic [  $clog2(REQ_DATA_WIDTH/8):0] req_size_o       ,
    output logic [      $clog2(VECTOR_LANES):0] req_ticket_o     ,
    // Incoming Data from Cache
    input  logic                                resp_valid_i     ,
    input  logic [      $clog2(VECTOR_LANES):0] resp_ticket_i    ,
    input  logic [  $clog2(REQ_DATA_WIDTH/8):0] resp_size_i      ,
    input  logic [          REQ_DATA_WIDTH-1:0] resp_data_i      ,
    //Sync Interface
    output logic                                is_busy_o
);

    localparam int ELEMENT_ADDR_WIDTH   = $clog2(VECTOR_LANES);
    localparam int VREG_ADDR_WIDTH      = $clog2(VECTOR_REGISTERS);
    localparam int MAX_MEM_SERVED_LIMIT = REQ_DATA_WIDTH / DATA_WIDTH;
    localparam int MAX_RF_SERVED_COUNT  = VECTOR_REGISTERS;
    localparam int MAX_SERVED_COUNT     = (VECTOR_REGISTERS > MAX_MEM_SERVED_LIMIT) ? MAX_MEM_SERVED_LIMIT
                                                                                    : VECTOR_REGISTERS;

    //=======================================================
    // REGISTERS
    //=======================================================
    logic [1:0][VECTOR_LANES-1:0][DATA_WIDTH-1:0] scratchpad;

    logic [                                    1:0][VECTOR_LANES-1:0] pending_elem        ;
    logic [                                    1:0][VECTOR_LANES-1:0] served_elem         ;
    logic [                                    1:0][VECTOR_LANES-1:0] active_elem         ;
    logic [                      MICROOP_WIDTH-1:0]                   microop_r           ;
    logic [                 VECTOR_TICKET_BITS-1:0]                   ticket_r            ;
    logic [                    VREG_ADDR_WIDTH-1:0]                   rdst_r              ;
    logic [                    VREG_ADDR_WIDTH-1:0]                   orig_rdst_r         ;
    logic [                                    4:0]                   last_ticket_src2_r  ;
    logic [$clog2(VECTOR_REGISTERS*VECTOR_LANES):0]                   instr_vl_r          ;
    logic [                    VREG_ADDR_WIDTH-1:0]                   current_exp_loop_r  ;
    logic [                    VREG_ADDR_WIDTH-1:0]                   max_expansion_r     ;
    logic [                 ELEMENT_ADDR_WIDTH-1:0]                   current_pointer_wb_r;
    logic [                         ADDR_WIDTH-1:0]                   stride_r            ;
    logic [                                    1:0]                   size_r              ;
    logic                                                             current_row         ;
    logic [                    VREG_ADDR_WIDTH-1:0]                   row_0_rdst          ;
    logic [                    VREG_ADDR_WIDTH-1:0]                   row_1_rdst          ;

    logic [                         ADDR_WIDTH-1:0]                   base_addr_r         ;
    logic [                                   15:0]                   image_size_r        ;
    logic [                                   15:0]                   kernel_size_r       ;
    logic [                                   15:0]                   win_row_num_r       ;
    logic [                                   15:0]                   win_col_num_r       ;
    //=======================================================
    // WIRES
    // =======================================================
    logic [$clog2(VECTOR_REGISTERS*VECTOR_LANES):0] total_remaining_elements    ;
    logic [$clog2(VECTOR_REGISTERS*VECTOR_LANES):0] nxt_total_remaining_elements;
    logic [                   ELEMENT_ADDR_WIDTH:0] loop_remaining_elements     ;
    logic [                                   15:0] row_remaining_el            ;
    logic [                 ELEMENT_ADDR_WIDTH-1:0] nxt_elem                    ;
    logic [                   ELEMENT_ADDR_WIDTH:0] el_served_count             ;
    logic [                   ELEMENT_ADDR_WIDTH:0] resp_el_count               ;
    logic [            VECTOR_LANES*DATA_WIDTH-1:0] data_vector                 ;
    logic [                         VECTOR_LANES:0] current_pointer_oh          ;
    logic [                         VECTOR_LANES:0] current_served_th           ;
    logic [                         VECTOR_LANES:0] resp_elem_th                ;
    logic [                         ADDR_WIDTH-1:0] current_addr                ;
    logic [                       VECTOR_LANES-1:0] nxt_pending_elem            ;
    logic [                       VECTOR_LANES-1:0] nxt_pending_elem_loop       ;
    logic [                                    1:0] nxt_size                    ;
    logic                                           start_new_instruction       ;
    logic                                           start_prefetch              ;
    logic                                           start_new_frame             ;
    logic                                           continue_instruction        ;
    logic                                           maxvl_reached               ;
    logic                                           vl_reached                  ;
    logic                                           do_reconfigure              ;
    logic                                           do_toepl_config             ;
    logic                                           current_finished            ;
    logic                                           currently_idle              ;
    logic                                           expansion_finished          ;
    logic                                           start_new_loop              ;
    logic                                           new_transaction_en          ;
    logic                                           request_ready               ;
    logic                                           resp_row                    ;
    logic                                           writeback_complete          ;
    logic                                           row_0_ready                 ;
    logic                                           row_1_ready                 ;
    logic                                           nxt_row                     ;
    logic                                           writeback_row               ;
    logic                                           instr_mismatch_found        ;
    logic [                         ADDR_WIDTH-1:0] nxt_base_addr               ;
    logic [                                   15:0] row_base                    ;
    logic [                                   15:0] col_num                     ;
    logic [                                   15:0] row_num                     ;
    logic [                                   15:0] win_row_base                ;
    logic [                                   15:0] addr_offset                 ;
    logic [                                   15:0] nxt_win_col_num             ;
    //=======================================================
    // Prefetchng FSM
    //=======================================================
    typedef enum { IDLE, ACTIVE, PREFETCH} activity_fsm_t;
    activity_fsm_t cur_state;
    activity_fsm_t nxt_state;

    always_ff @(posedge clk or negedge rst_n) begin
        if(~rst_n) begin
            cur_state <= IDLE;
        end else begin
            cur_state <= nxt_state;
        end
    end

    always_comb begin
        case (cur_state)
            IDLE    : nxt_state = start_new_instruction ? ACTIVE   : IDLE;
            ACTIVE  : nxt_state = start_prefetch        ? PREFETCH : ACTIVE;
            PREFETCH: nxt_state = continue_instruction  ? ACTIVE   :
                                  start_new_instruction ? ACTIVE   : PREFETCH;
            default : nxt_state = activity_fsm_t'('x);
        endcase
        if (do_reconfigure | do_toepl_config) nxt_state = IDLE;
    end
    //=======================================================
    // Create basic control flow
    //=======================================================
    assign ready_o             =  currently_idle;
    assign is_busy_o           = ~currently_idle;

    //current instruction finished
    assign current_finished = ~pending_elem[current_row][nxt_elem] & expansion_finished & new_transaction_en;
    //currently no instructions are being served
    assign currently_idle = (~|pending_elem & ~|active_elem) | (cur_state === PREFETCH) | (cur_state === IDLE);

    assign expansion_finished = maxvl_reached | vl_reached;
    assign maxvl_reached      = (current_exp_loop_r === (max_expansion_r-1));
    assign vl_reached         = (((current_exp_loop_r+1) << $clog2(VECTOR_LANES)) >= instr_vl_r);

    //indicates a pipeline reconfiguration
    assign do_reconfigure        = valid_in & ready_o &  instr_in.reconfigure;
    //indicates new instruction starting fresh or after failed prefetch
    assign start_new_instruction = valid_in & ready_o & ~instr_in.reconfigure & ~do_toepl_config &
                                 ((cur_state === IDLE) | (cur_state === PREFETCH & instr_mismatch_found));
    //prefetch begins after the current instr retires
    assign start_prefetch        = ~|pending_elem & ~|active_elem & (cur_state === ACTIVE);
    assign start_new_frame       = (start_prefetch & (win_row_num_r === kernel_size_r  ))                                |
                                   (start_prefetch & (win_row_num_r === kernel_size_r-1) & win_col_num_r === kernel_size_r);

    // indicates a toeplitz reconfiguration
    assign do_toepl_config       = valid_in & ready_o & ~instr_in.reconfigure & instr_in.microop === 7'b1110011;
    // indicates that the prefetch was correct and will continue with it
    assign continue_instruction  = valid_in & ready_o & ~instr_in.reconfigure & (cur_state === PREFETCH) & ~instr_mismatch_found;
    // indicates the prefetch mismatches with the instruction flow
    assign instr_mismatch_found  = (nxt_base_addr !== base_addr_r); //REVISIT - needs more checks

    // Start from element 0 on the next destination vreg
    assign start_new_loop = (~|pending_elem[current_row] & ~expansion_finished & ~|active_elem[nxt_row]);

    // Create the memory request control signals
    assign req_en_o      = request_ready;
    assign req_addr_o    = current_addr;
    assign req_microop_o = 5'b10000; //REVISIT will change based on instruction
    assign req_ticket_o  = {current_row,current_pointer_wb_r};
    always_comb begin
        unique case (size_r)
            `SZ_8   : req_size_o = el_served_count;      //el_served_count * 1
            `SZ_16  : req_size_o = el_served_count << 1; //el_served_count * 2
            `SZ_32  : req_size_o = el_served_count << 2; //el_served_count * 4
            default : req_size_o = 'x;
        endcase
    end

    assign request_ready      = pending_elem[current_row][current_pointer_wb_r] & (cur_state === ACTIVE | cur_state === PREFETCH);
    assign new_transaction_en = request_ready & grant_i;

    // Unlock register signals
    assign unlock_en_o     = writeback_complete;
    assign unlock_ticket_o = ticket_r;
    assign unlock_reg_a_o  = row_0_ready ? row_0_rdst : row_1_rdst;
    assign unlock_reg_b_o  = row_0_ready ? row_0_rdst : row_1_rdst;

    // Create the writeback signals for the RF
    assign wrtbck_req_o       = (row_0_ready | row_1_ready) & (cur_state === ACTIVE);
    assign writeback_complete = wrtbck_req_o & wrtbck_grant_i;
    assign writeback_row      = row_0_ready ? 1'b0 : 1'b1;

    assign row_0_ready = ~|(active_elem[0] ^ served_elem[0]) & |active_elem[0] & (wrtbck_ticket_a_i === ticket_r) & wrtbck_locked_a_i;
    assign row_1_ready = ~|(active_elem[1] ^ served_elem[1]) & |active_elem[1] & (wrtbck_ticket_b_i === ticket_r) & wrtbck_locked_b_i;

    // Output aliasing
    assign wrtbck_en_o     = row_0_ready ? {VECTOR_LANES{writeback_complete}} & served_elem[0] :
                                           {VECTOR_LANES{writeback_complete}} & served_elem[1];
    assign wrtbck_data_o   = row_0_ready ? scratchpad[0] : scratchpad[1];
    assign wrtbck_reg_o    = row_0_ready ? row_0_rdst    : row_1_rdst;
    assign wrtbck_ticket_o = ticket_r;
    assign wrtbck_reg_a_o  = row_0_rdst;
    assign wrtbck_reg_b_o  = row_1_rdst;

    //=======================================================
    // Address Generation
    //=======================================================
    assign row_num = instr_in.data1[15:0];
    assign col_num = instr_in.data2[15:0];
    always_comb begin
        row_base      = row_num * image_size_r;
        nxt_base_addr = row_base + col_num;
        nxt_base_addr = nxt_base_addr << 2;
        nxt_base_addr = nxt_base_addr + instr_in.immediate;
    end
    //Hold region base address (for each kernel once)
    always_ff @(posedge clk) begin
        if(start_new_instruction)
            base_addr_r <= nxt_base_addr;
        else if (start_new_frame)
            base_addr_r <= base_addr_r + stride_r;
    end

    // generate current address offset
    always_comb begin
        win_row_base = win_row_num_r * image_size_r;
        addr_offset  = win_row_base + win_col_num_r;
        unique case (size_r)
            `SZ_8   : addr_offset = addr_offset;
            `SZ_16  : addr_offset = addr_offset << 1;
            `SZ_32  : addr_offset = addr_offset << 2;
            default : addr_offset = 'x;
        endcase
    end

    assign current_addr = base_addr_r + addr_offset;

    //Hold image & kernel sizes (needs toepl reconfig)
    always_ff @(posedge clk) begin
        if(do_toepl_config) begin
            image_size_r  <= instr_in.data1;
            kernel_size_r <= instr_in.data2;
        end
    end

    assign nxt_win_col_num = win_col_num_r + el_served_count;
    // Hold the row/col progression
    always_ff @(posedge clk) begin
        if(start_new_instruction | start_new_frame) begin
            win_row_num_r <= 0;
            win_col_num_r <= 0;
        end else if(new_transaction_en) begin
            if (nxt_win_col_num == kernel_size_r) begin
                win_row_num_r <= win_row_num_r +1;
                win_col_num_r <= 'd0;
            end else begin
                win_col_num_r <= nxt_win_col_num;
            end
        end
    end
    //Hold mem op size
    assign nxt_size   = instr_in.microop[`MEM_SZ_RANGE_HI:`MEM_SZ_RANGE_LO];
    assign nxt_stride = instr_in.immediate;
    always_ff @(posedge clk) begin
        if(do_toepl_config) size_r   <= nxt_size;
        if(do_toepl_config) stride_r <= nxt_stride;
    end
    //=======================================================
    // Scratchpad maintenance
    //=======================================================
    assign resp_row = resp_ticket_i[ELEMENT_ADDR_WIDTH];
    // Calculate the elements that have a valid response
    always_comb begin
        unique case (size_r)
            `SZ_8   : resp_el_count = resp_size_i;      //el_served_count * 1
            `SZ_16  : resp_el_count = resp_size_i >> 1; //el_served_count * 2
            `SZ_32  : resp_el_count = resp_size_i >> 2; //el_served_count * 4
            default : resp_el_count = 'x;
        endcase
    end
    assign resp_elem_th = ((~('1 << resp_el_count)) << resp_ticket_i[ELEMENT_ADDR_WIDTH-1:0]);

    // Shift data vector to match the elements positions
    assign data_vector = resp_data_i << resp_ticket_i[ELEMENT_ADDR_WIDTH-1:0] * 32;
    // Store new Data
    always_ff @(posedge clk) begin : scratchpad_maint
        for (int i = 0; i < VECTOR_LANES; i++) begin
            // row 0 maintenance
            if(resp_valid_i && !resp_row && resp_elem_th[i]) begin
                scratchpad[0][i] <= data_vector[i*32 +: 32];
            end
            // row 1 maintenance
            if(resp_valid_i && resp_row && resp_elem_th[i]) begin
                scratchpad[1][i] <= data_vector[i*32 +: 32];
            end
        end
    end
    // keep track of the rdst for each row
    always_ff @(posedge clk or negedge rst_n) begin
        if(~rst_n) begin
            row_0_rdst <= 0;
            row_1_rdst <= 0;
        end else begin
            // row 0 maintenance
            if(start_new_instruction || continue_instruction) begin
                row_0_rdst <= instr_in.dst;
            end else if(start_new_loop && !nxt_row) begin
                row_0_rdst <= rdst_r +1;
            end
            // row 1 maintenance
            if(start_new_loop && nxt_row) begin
                row_1_rdst <= rdst_r +1;
            end
        end
    end
    //=======================================================
    // Scoreboard maintenance
    //=======================================================
    assign row_remaining_el = kernel_size_r - win_col_num_r;

    always_comb begin : proc_loop_remaining_el
        loop_remaining_elements = '0;
        for (int i = 0; i < VECTOR_LANES; i++) begin
            if (pending_elem[current_row][i]) loop_remaining_elements = loop_remaining_elements +1;
        end
    end
    assign total_remaining_elements     = instr_vl_r - (current_exp_loop_r*VECTOR_LANES);
    assign nxt_total_remaining_elements = instr_vl_r - ((current_exp_loop_r+1)*VECTOR_LANES);

    always_comb begin : get_served_el_cnt
        if (row_remaining_el < loop_remaining_elements) begin
            el_served_count = row_remaining_el;
        end else begin
            el_served_count = loop_remaining_elements;
        end
        if (el_served_count > MAX_SERVED_COUNT)
            el_served_count = MAX_SERVED_COUNT;
    end

    // Maintain current pointer and row
    assign nxt_row  = ~current_row;
    assign nxt_elem = current_pointer_wb_r +el_served_count;
    always_ff @(posedge clk or negedge rst_n) begin : current_ptr
        if(~rst_n) begin
            current_pointer_wb_r <= 0;
            current_row          <= 0;
        end else begin
            if(start_new_instruction || start_prefetch) begin
                current_pointer_wb_r <= 0;
                current_row          <= 0;
            end else if(start_new_loop) begin
                current_pointer_wb_r <= 0;
                current_row          <= nxt_row;
            end else if (current_finished) begin
                current_pointer_wb_r <= 0;
            end else if(new_transaction_en) begin
                current_pointer_wb_r <= nxt_elem;
            end
        end
    end

    // Create new pending states
    always_comb begin : get_new_elem_pending
        // next pending state for new instruction
        if(instr_in.vl < VECTOR_LANES & start_prefetch)
            nxt_pending_elem = ~('1 << instr_vl_r);
        else if(instr_in.vl < VECTOR_LANES & ~start_prefetch)
            nxt_pending_elem = ~('1 << instr_in.vl);
        else
            nxt_pending_elem = '1;
        // next pending state for new loop
        if(nxt_total_remaining_elements < VECTOR_LANES)
            nxt_pending_elem_loop = ~('1 << nxt_total_remaining_elements);
        else
            nxt_pending_elem_loop = '1;
    end

    // Store new pending states
    assign current_served_th  = (~('1 << el_served_count)) << current_pointer_wb_r;
    assign current_pointer_oh = 1 << current_pointer_wb_r;
    always_ff @(posedge clk or negedge rst_n) begin: pending_status
        if(~rst_n) begin
            pending_elem <= '0;
        end else begin
            for (int i = 0; i < VECTOR_LANES; i++) begin
                //row 0 maintenance
                if(start_new_instruction || start_prefetch)
                    pending_elem[0][i] <= nxt_pending_elem[i];
                else if(start_new_loop && !nxt_row)
                    pending_elem[0][i] <= nxt_pending_elem_loop[i];
                else if(new_transaction_en && current_served_th[i] && !current_row) // single-request
                    pending_elem[0][i] <= 1'b0;
                //row 1 maintenance
                if(start_new_instruction || start_prefetch)
                    pending_elem[1][i] <= 1'b0;
                else if(start_new_loop && nxt_row)
                    pending_elem[1][i] <= nxt_pending_elem_loop[i];
                else if(new_transaction_en && current_served_th[i] && current_row) // single-request
                    pending_elem[1][i] <= 1'b0;
            end
        end
    end
    always_ff @(posedge clk or negedge rst_n) begin : active_status
        if(~rst_n) begin
            active_elem <= '0;
        end else begin
            for (int i = 0; i < VECTOR_LANES; i++) begin
                // row 0 maintenance
                if (writeback_complete && !writeback_row)
                    active_elem[0][i] <= 1'b0;
                else if(start_new_instruction || start_prefetch)
                    active_elem[0][i] <= nxt_pending_elem[i];
                else if(start_new_loop && !nxt_row)
                    active_elem[0][i] <= nxt_pending_elem_loop[i];
                // row 1 maintenance
                if (writeback_complete && writeback_row)
                    active_elem[1][i] <= 1'b0;
                else if(start_new_instruction || start_prefetch)
                    active_elem[1][i] <= 1'b0;
                else if(start_new_loop && nxt_row)
                    active_elem[1][i] <= nxt_pending_elem_loop[i];
            end
        end
    end
    // Keep track of served elements from memory
    always_ff @(posedge clk or negedge rst_n) begin
        if(~rst_n) begin
            served_elem <= '0;
        end else begin
            for (int i = 0; i < VECTOR_LANES; i++) begin
                // row 0 maintenance
                if(start_new_instruction || start_prefetch) begin
                    served_elem[0][i] <= 1'b0;
                end else if(start_new_loop && !nxt_row) begin
                    served_elem[0][i] <= 1'b0;
                end else if(resp_valid_i && resp_elem_th[i] && !resp_row) begin
                    served_elem[0][i] <= 1'b1;
                end
                // row 1 maintenance
                if(start_new_instruction || start_prefetch) begin
                    served_elem[1][i] <= 1'b0;
                end else if(start_new_loop && nxt_row) begin
                    served_elem[1][i] <= 1'b0;
                end else if(resp_valid_i && resp_elem_th[i] && resp_row) begin
                    served_elem[1][i] <= 1'b1;
                end
            end
        end
    end

    // Keep track of the expanions happening
    always_ff @(posedge clk or negedge rst_n) begin : loop_tracking
        if(~rst_n) begin
            current_exp_loop_r <= 0;
        end else begin
            if(start_new_instruction) begin
                current_exp_loop_r <= 0;
                rdst_r             <= instr_in.dst;
                orig_rdst_r        <= instr_in.dst;
            end else if (start_prefetch & ~start_new_frame) begin
                current_exp_loop_r <= 0;
            end else if (start_prefetch & start_new_frame) begin
                current_exp_loop_r <= 0;
                rdst_r             <= orig_rdst_r;
            end else if(start_new_loop) begin
                current_exp_loop_r <= current_exp_loop_r +1;
                rdst_r             <= rdst_r +1;
            end
        end
    end
    //Store the max expansion when reconfiguring
    always_ff @(posedge clk or negedge rst_n) begin : maxExp
        if(~rst_n) begin
            max_expansion_r <= 'd1;
        end else begin
            if(do_reconfigure) begin
                max_expansion_r <= instr_in.maxvl >> $clog2(VECTOR_LANES);
            end
        end
    end

    //=======================================================
    // Capture Instruction Information
    always_ff @(posedge clk or negedge rst_n) begin : proc_vl_r
        if(~rst_n) begin
            instr_vl_r <= VECTOR_LANES;
        end else begin
            if(start_new_instruction) begin
                instr_vl_r <= instr_in.vl;
            end
        end
    end
    always_ff @(posedge clk) begin
        if(start_new_instruction) begin
            microop_r          <= instr_in.microop;
        end
    end
    always_ff @(posedge clk) begin
        if(start_new_instruction || continue_instruction) begin
            ticket_r           <= instr_in.ticket;
            last_ticket_src2_r <= instr_in.last_ticket_src2;
        end
    end

//=======================================================
    logic stall_row_0_while_ready, stall_row_1_while_ready;
    logic [63:0] total_tp_stalled_due_is;

    assign stall_row_0_while_ready = ~|(active_elem[0] ^ served_elem[0]) & |active_elem[0] & (~wrtbck_locked_a_i | wrtbck_ticket_a_i !== ticket_r);
    assign stall_row_1_while_ready = ~|(active_elem[1] ^ served_elem[1]) & |active_elem[1] & (~wrtbck_locked_b_i | wrtbck_ticket_b_i !== ticket_r);

    always_ff @(posedge clk or negedge rst_n) begin
        if(~rst_n) begin
            total_tp_stalled_due_is <= 0;
        end else begin
            if (stall_row_0_while_ready | stall_row_1_while_ready)
                total_tp_stalled_due_is <= total_tp_stalled_due_is +1;
        end
    end


`ifdef MODEL_TECH
    `include "vmu_tp_eng_sva.sv"
`endif

endmodule