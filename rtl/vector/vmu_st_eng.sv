/*
* @info Vector Store Unit
*
* @author VLSI Lab, EE dept., Democritus University of Thrace
*
*/
`ifdef MODEL_TECH
    `include "vstructs.sv"
`endif
module vmu_st_eng #(
    parameter int REQ_DATA_WIDTH     = 256,
    parameter int VECTOR_REGISTERS   = 32 ,
    parameter int VECTOR_LANES       = 8  ,
    parameter int DATA_WIDTH         = 32 ,
    parameter int ADDR_WIDTH         = 32 ,
    parameter int MICROOP_WIDTH      = 5  ,
    parameter int VECTOR_TICKET_BITS = 4
) (
    input  logic                                clk                ,
    input  logic                                rst_n              ,
    //Input Interface
    input  logic                                valid_in           ,
    input  memory_remapped_v_instr              instr_in           ,
    output logic                                ready_o            ,
    //RF Interface (per vreg)
    output logic [$clog2(VECTOR_REGISTERS)-1:0] rd_addr_1_o        ,
    input  logic [ VECTOR_LANES*DATA_WIDTH-1:0] rd_data_1_i        ,
    input  logic                                rd_pending_1_i     ,
    input  logic [      VECTOR_TICKET_BITS-1:0] rd_ticket_1_i      ,
    //RF Interface (for `OP_INDEXED stride)
    output logic [$clog2(VECTOR_REGISTERS)-1:0] rd_addr_2_o        ,
    input  logic [ VECTOR_LANES*DATA_WIDTH-1:0] rd_data_2_i        ,
    input  logic                                rd_pending_2_i     ,
    input  logic [      VECTOR_TICKET_BITS-1:0] rd_ticket_2_i      ,
    //Unlock Interface
    output logic                                unlock_en_o        ,
    output logic [$clog2(VECTOR_REGISTERS)-1:0] unlock_reg_a_o     ,
    output logic [$clog2(VECTOR_REGISTERS)-1:0] unlock_reg_b_o     ,
    output logic [      VECTOR_TICKET_BITS-1:0] unlock_ticket_o    ,
    //Request Interface
    input  logic                                grant_i            ,
    output logic                                req_en_o           ,
    output logic [              ADDR_WIDTH-1:0] req_addr_o         ,
    output logic [           MICROOP_WIDTH-1:0] req_microop_o      ,
    output logic [  $clog2(REQ_DATA_WIDTH/8):0] req_size_o         ,
    output logic [          REQ_DATA_WIDTH-1:0] req_data_o         ,
    //Sync Interface
    output logic                                is_busy_o          ,
    output logic                                can_be_inteleaved_o,
    output logic [              ADDR_WIDTH-1:0] start_addr_o       ,
    output logic [              ADDR_WIDTH-1:0] end_addr_o
);

    localparam int ELEMENT_ADDR_WIDTH   = $clog2(VECTOR_LANES)                                                       ;
    localparam int VREG_ADDR_WIDTH      = $clog2(VECTOR_REGISTERS)                                                   ;
    localparam int MAX_MEM_SERVED_LIMIT = REQ_DATA_WIDTH / DATA_WIDTH                                                ;
    localparam int MAX_RF_SERVED_COUNT  = VECTOR_REGISTERS                                                           ;
    localparam int MAX_SERVED_COUNT     = (VECTOR_LANES > MAX_MEM_SERVED_LIMIT) ? MAX_MEM_SERVED_LIMIT : VECTOR_LANES;

    //=======================================================
    // REGISTERS
    //=======================================================
    logic [                       VECTOR_LANES-1:0] pending_elem        ;
    logic [                      MICROOP_WIDTH-1:0] microop_r           ;
    logic [                 VECTOR_TICKET_BITS-1:0] ticket_r            ;
    logic [                    VREG_ADDR_WIDTH-1:0] src1_r              ;
    logic [                    VREG_ADDR_WIDTH-1:0] src2_r              ;
    logic [                    VREG_ADDR_WIDTH-1:0] rdst_r              ;
    logic [                 VECTOR_TICKET_BITS-1:0] last_ticket_src1_r  ;
    logic [                 VECTOR_TICKET_BITS-1:0] last_ticket_src2_r  ;
    logic [$clog2(VECTOR_REGISTERS*VECTOR_LANES):0] instr_vl_r          ;
    logic [                    VREG_ADDR_WIDTH-1:0] current_exp_loop_r  ;
    logic [                    VREG_ADDR_WIDTH-1:0] max_expansion_r     ;
    logic [                   ELEMENT_ADDR_WIDTH:0] current_pointer_wb_r;
    logic [                         ADDR_WIDTH-1:0] current_addr_r      ;
    logic [                         ADDR_WIDTH-1:0] base_addr_r         ;
    logic [                         ADDR_WIDTH-1:0] stride_r            ;
    logic [                                    1:0] size_r              ;
    logic [                                    1:0] memory_op_r         ;
    logic [                         ADDR_WIDTH-1:0] start_addr_r        ;
    logic [                         ADDR_WIDTH-1:0] end_addr_r          ;
    //=======================================================
    // WIRES
    //=======================================================
    logic [                     REQ_DATA_WIDTH-1:0] data_selected               ;
    logic [$clog2(VECTOR_REGISTERS*VECTOR_LANES):0] total_remaining_elements    ;
    logic [$clog2(VECTOR_REGISTERS*VECTOR_LANES):0] nxt_total_remaining_elements;
    logic [                 $clog2(VECTOR_LANES):0] loop_remaining_elements     ;
    logic [    $clog2(VECTOR_LANES*DATA_WIDTH)-1:0] element_index               ;
    logic [                     REQ_DATA_WIDTH-1:0] data_selected_v             ;
    logic [                         DATA_WIDTH-1:0] data_selected_el            ;
    logic [                 ELEMENT_ADDR_WIDTH-1:0] nxt_elem                    ;
    logic [                   ELEMENT_ADDR_WIDTH:0] el_served_count             ;
    logic [                         VECTOR_LANES:0] current_pointer_oh          ;
    logic [                         VECTOR_LANES:0] current_served_th           ;
    logic [                         ADDR_WIDTH-1:0] nxt_base_addr               ;
    logic [                         ADDR_WIDTH-1:0] nxt_strided_addr            ;
    logic [                         ADDR_WIDTH-1:0] nxt_unit_strided_addr       ;
    logic [                         ADDR_WIDTH-1:0] current_addr                ;
    logic [                         ADDR_WIDTH-1:0] nxt_stride                  ;
    logic [                         ADDR_WIDTH-1:0] offset_read                 ;
    logic [                       VECTOR_LANES-1:0] nxt_pending_elem            ;
    logic [                       VECTOR_LANES-1:0] nxt_pending_elem_loop       ;
    logic [                                    1:0] nxt_memory_op               ;
    logic [                                    1:0] nxt_size                    ;
    logic                                           start_new_instruction       ;
    logic                                           maxvl_reached               ;
    logic                                           vl_reached                  ;
    logic                                           do_reconfigure              ;
    logic                                           current_finished            ;
    logic                                           currently_idle              ;
    logic                                           multi_valid                 ;
    logic                                           expansion_finished          ;
    logic                                           data_ready                  ;
    logic                                           addr_ready                  ;
    logic                                           start_new_loop              ;
    logic                                           new_transaction_en          ;
    logic                                           request_ready               ;
    // Create basic control flow
    //=======================================================
    assign ready_o             = currently_idle | current_finished;
    assign is_busy_o           = ~currently_idle;
    assign can_be_inteleaved_o = (memory_op_r !== `OP_INDEXED);
    //current instruction finished
    assign current_finished = expansion_finished & new_transaction_en & (~pending_elem[nxt_elem] | (loop_remaining_elements <= MAX_SERVED_COUNT));
    //currently no instructions are being served
    assign currently_idle = current_pointer_oh[0] & ~|pending_elem;

    assign expansion_finished = maxvl_reached | vl_reached;
    assign maxvl_reached      = (current_exp_loop_r === (max_expansion_r-1));
    assign vl_reached         = (((current_exp_loop_r+1) << $clog2(VECTOR_LANES)) >= instr_vl_r);

    assign start_new_instruction = valid_in & ready_o & ~instr_in.reconfigure;
    assign do_reconfigure        = valid_in & ready_o & instr_in.reconfigure;

    // Start from element 0 on the next destination vreg
    assign start_new_loop = ~expansion_finished & new_transaction_en &
                            ((~current_pointer_oh[0] & ~pending_elem[nxt_elem]) |
                             (loop_remaining_elements >= MAX_SERVED_COUNT));

    // Create the memory request control signals
    assign req_en_o      = request_ready;
    assign req_addr_o    = current_addr;
    assign req_data_o    = data_selected;
    assign req_microop_o = 5'b11111; //REVISIT will change based on instruction
    always_comb begin
        unique case (size_r)
            `SZ_8   : req_size_o = el_served_count;      //el_served_count * 1
            `SZ_16  : req_size_o = el_served_count << 1; //el_served_count * 2
            `SZ_32  : req_size_o = el_served_count << 2; //el_served_count * 4
            default : req_size_o = 'x;
        endcase
    end

    assign new_transaction_en = request_ready & grant_i;
    assign request_ready      = data_ready & addr_ready & pending_elem[current_pointer_wb_r];
    assign data_ready         = ~rd_pending_1_i;
    assign addr_ready         = (memory_op_r === `OP_INDEXED) ? ~rd_pending_2_i & ((rd_ticket_2_i === ticket_r) | (rd_ticket_2_i === last_ticket_src2_r)) : 1'b1;
    // Unlock register signals
    assign unlock_en_o     = start_new_loop | current_finished;
    assign unlock_reg_a_o  = src1_r;
    assign unlock_reg_b_o  = src2_r;
    assign unlock_ticket_o = ticket_r;

    // assign the rest of the outputs
    assign rd_addr_1_o  = src1_r;
    assign rd_addr_2_o  = src2_r;
    assign start_addr_o = start_addr_r;
    assign end_addr_o   = end_addr_r;
    //=======================================================
    // Address Generation
    //=======================================================
    assign multi_valid   = (memory_op_r === `OP_UNIT_STRIDED);
    assign element_index = current_pointer_wb_r << 5; //*32
    assign offset_read   = rd_data_2_i[element_index +: DATA_WIDTH];
    // Generate next non-multi consecutive address
    always_comb begin
        case (memory_op_r)
            `OP_UNIT_STRIDED : current_addr = current_addr_r;
            `OP_STRIDED      : current_addr = current_addr_r;
            `OP_INDEXED      : current_addr = base_addr_r + offset_read;
            default          : current_addr = 'X;
        endcase
    end

    assign nxt_base_addr    = instr_in.data1 + instr_in.immediate;
    assign nxt_strided_addr = current_addr_r + stride_r;
    always_comb begin
        unique case (size_r)
            `SZ_8   : nxt_unit_strided_addr = current_addr_r + el_served_count;
            `SZ_16  : nxt_unit_strided_addr = current_addr_r + (el_served_count << 1);
            `SZ_32  : nxt_unit_strided_addr = current_addr_r + (el_served_count << 2);
            default : nxt_unit_strided_addr = 'X;
        endcase
    end
    //Hold current address
    always_ff @(posedge clk) begin
        if(start_new_instruction) begin
            current_addr_r <= nxt_base_addr;
        end else if (new_transaction_en && memory_op_r == `OP_STRIDED) begin
            current_addr_r <= nxt_strided_addr;
        end else if(new_transaction_en && memory_op_r == `OP_UNIT_STRIDED) begin
            current_addr_r <= nxt_unit_strided_addr;
        end
    end
    //Hold base address
    always_ff @(posedge clk) begin
        if(start_new_instruction) begin
            base_addr_r <= nxt_base_addr;
        end
    end
    //Hold stride
    assign nxt_stride = instr_in.data2;
    always_ff @(posedge clk) begin
        if(start_new_instruction) stride_r <= nxt_stride;
    end
    //Hold mem op size
    assign nxt_size = instr_in.microop[`MEM_SZ_RANGE_HI:`MEM_SZ_RANGE_LO];
    always_ff @(posedge clk) begin
        if(start_new_instruction) size_r <= nxt_size;
    end
    //=======================================================
    // Data Generation
    //=======================================================
    // single-element data to be stored
    assign data_selected_el = rd_data_1_i[element_index +: DATA_WIDTH];
    // vector of data to be stored
    assign data_selected_v = rd_data_1_i >> (current_pointer_wb_r << 5); //bring the data to bit0

    // create the final data vector
    always_comb begin
        data_selected = '0;
        if(!multi_valid) begin
            data_selected[0+:32] = data_selected_el;
        end else begin
            for (int i = 0; i < MAX_SERVED_COUNT; i++) begin
                unique case (size_r)
                    `SZ_8   : data_selected[i*8 +: 8]   = data_selected_v[i*32 +:8];  //pick 8bits from each elem
                    `SZ_16  : data_selected[i*16 +: 16] = data_selected_v[i*32 +:16]; //pick 16bits from each elem
                    `SZ_32  : data_selected[i*32 +: 32] = data_selected_v[i*32 +:32]; //pick 32bits from each elem
                    default : data_selected[i*32 +: 32] = 'X;
                endcase
            end
        end
    end

    //=======================================================
    // Scoreboard maintenance
    //=======================================================
    always_comb begin : proc_loop_remaining_el
        loop_remaining_elements = 0;
        for (int i = 0; i < VECTOR_LANES; i++) begin
            if (pending_elem[i]) loop_remaining_elements = loop_remaining_elements +1;
        end
    end
    assign total_remaining_elements     = instr_vl_r - (current_exp_loop_r*VECTOR_LANES);
    assign nxt_total_remaining_elements = instr_vl_r - ((current_exp_loop_r+1)*VECTOR_LANES);
    always_comb begin : get_served_el_cnt
        if (memory_op_r !== `OP_UNIT_STRIDED) begin
            el_served_count = 'd1;
        end else if (loop_remaining_elements < MAX_SERVED_COUNT) begin
            el_served_count = loop_remaining_elements; // remaining < max_width
        end else begin
            el_served_count = MAX_SERVED_COUNT; // remaining > max_width
        end
    end
    // Maintain current pointer
    assign nxt_elem = multi_valid ? (current_pointer_wb_r + el_served_count) : (current_pointer_wb_r +1);
    always_ff @(posedge clk or negedge rst_n) begin : current_ptr
        if(~rst_n) begin
            current_pointer_wb_r <= 0;
        end else begin
            if(start_new_instruction) begin
                current_pointer_wb_r <= 0;
            end else if (start_new_loop) begin
                current_pointer_wb_r <= 0;
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
        if(instr_in.vl < VECTOR_LANES) begin
            nxt_pending_elem = ~('1 << instr_in.vl);
        end else begin
            nxt_pending_elem = '1;
        end
        // next pending state for new loop
        if(nxt_total_remaining_elements < VECTOR_LANES) begin
            nxt_pending_elem_loop = ~('1 << nxt_total_remaining_elements);
        end else begin
            nxt_pending_elem_loop = '1;
        end
    end
    // Store new pending states
    assign current_served_th  = (~('1 << el_served_count)) << current_pointer_wb_r;
    assign current_pointer_oh = 1 << current_pointer_wb_r;
    always_ff @(posedge clk or negedge rst_n) begin : pending_status
        if(~rst_n) begin
            pending_elem <= '0;
        end else begin
            for (int i = 0; i < VECTOR_LANES; i++) begin
                if(start_new_instruction) begin
                    pending_elem[i] <= nxt_pending_elem[i];
                end else if (start_new_loop) begin
                    pending_elem[i] <= nxt_pending_elem_loop[i];
                end else if(new_transaction_en && current_served_th[i] && multi_valid) begin // multi-request
                    pending_elem[i] <= 1'b0;
                end else if(new_transaction_en && current_pointer_oh[i] && !multi_valid) begin // single-request
                    pending_elem[i] <= 1'b0;
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
                src1_r             <= instr_in.src1;
                src2_r             <= instr_in.src2;
            end else if(start_new_loop) begin
                current_exp_loop_r <= current_exp_loop_r +1;
                src1_r             <= src1_r +1;
                src2_r             <= src2_r +1;
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
            ticket_r           <= instr_in.ticket;
            last_ticket_src1_r <= instr_in.last_ticket_src1;
            last_ticket_src2_r <= instr_in.last_ticket_src2;
        end
    end

    assign nxt_memory_op = instr_in.microop[`MEM_OP_RANGE_HI:`MEM_OP_RANGE_LO];
    always_ff @(posedge clk or negedge rst_n) begin : proc_memory_op_r
        if(~rst_n) begin
            memory_op_r <= '0;
        end else begin
            if(start_new_instruction) begin
                memory_op_r <= nxt_memory_op;
            end
        end
    end

    // calculate start-end addresses for the op
    // +- 4 to avoid conflicts due to data sizes
    always_ff @(posedge clk or negedge rst_n) begin
        if(~rst_n) begin
            start_addr_r <= '0;
            end_addr_r   <= '1;
        end else begin
            if(start_new_instruction) begin
                start_addr_r <= nxt_base_addr;
                if(instr_in.microop[`MEM_OP_RANGE_HI:`MEM_OP_RANGE_LO] !== `OP_INDEXED) begin
                    end_addr_r <= nxt_base_addr + ((instr_in.vl -1) * nxt_stride);
                end else begin
                    end_addr_r <= nxt_base_addr; // cannot calculate end address for `OP_INDEXED ops
                end
            end
        end
    end


`ifdef MODEL_TECH
    `include "vmu_st_eng_sva.sv"
`endif

endmodule