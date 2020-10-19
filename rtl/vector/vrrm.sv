/*
* @info Vector Register Remmaping
*
* @author VLSI Lab, EE dept., Democritus University of Thrace
*
*/
`ifdef MODEL_TECH
    `include "vstructs.sv"
`endif
module vrrm #(
    parameter int VECTOR_REGISTERS   = 32,
    parameter int VECTOR_LANES       = 8 ,
    parameter int VECTOR_TICKET_BITS = 4
) (
    input  logic                   clk        ,
    input  logic                   rst_n      ,
    output logic                   is_idle_o  ,
    //Instruction In
    input  logic                   valid_in   ,
    input  to_vector               instr_in   ,
    output logic                   pop_instr  ,
    //Instruction Out
    output logic                   valid_o    ,
    output remapped_v_instr        instr_out  ,
    input  logic                   ready_i    ,
    //Memory Instruction Out
    output logic                   m_valid_o  ,
    output memory_remapped_v_instr m_instr_out,
    input  logic                   m_ready_i
);

    localparam int ELEM_ADDR_WIDTH = $clog2(VECTOR_LANES*32);
    localparam int REGISTER_BITS   = $clog2(VECTOR_REGISTERS);

    logic [  VECTOR_REGISTERS-1:0][VECTOR_TICKET_BITS-1:0] last_producer      ;
    logic [     REGISTER_BITS-1:0]                         next_free_vreg     ;
    logic [     REGISTER_BITS-1:0]                         rdst_destination   ;
    logic [       REGISTER_BITS:0]                         vreg_hop           ;
    logic [     REGISTER_BITS-1:0]                         remapped_src1      ;
    logic [     REGISTER_BITS-1:0]                         remapped_src2      ;
    logic [VECTOR_TICKET_BITS-1:0]                         next_ticket        ;
    logic                                                  do_operation, do_remap, rdst_remapped;
    logic                                                  memory_instr       ;
    logic                                                  reconfig_instr     ;
    logic                                                  do_reconfigure     ;
    logic                                                  load_instr         ;
    logic                                                  toepl_instr        ;
    logic                                                  toepl_conf         ;
    logic                                                  last_producer_wr_en;

    //Check for special types of instructions
    assign reconfig_instr = instr_in.reconfigure;                          // general reconfiguration instr
    assign memory_instr   = instr_in.fu === `MEM_FU;                       // memory instr
    assign toepl_conf     = instr_in.microop === 7'b1110011;               // toeplitz prefetcher configuration
    assign toepl_instr    = instr_in.microop === 7'b1010011 & ~toepl_conf; // toeplitz prefetcher instr
    assign load_instr     = instr_in.microop[`LD_BIT] & ~toepl_instr;      // load instr
    //Push Pop Signals
    assign valid_o      = valid_in & do_operation;
    assign do_operation = (memory_instr | reconfig_instr) ? (valid_in & ready_i & m_ready_i) : (valid_in & ready_i);
    assign pop_instr    = do_operation;
    assign m_valid_o    = valid_in & (memory_instr | reconfig_instr) & do_operation;

    assign do_reconfigure = reconfig_instr & do_operation;

    // Instr Out Generation
    assign instr_out.vl          = instr_in.vl;
    assign instr_out.maxvl       = instr_in.maxvl;
    assign instr_out.valid       = instr_in.valid;
    assign instr_out.use_mask    = instr_in.use_mask;
    assign instr_out.immediate   = instr_in.immediate;
    assign instr_out.fu          = instr_in.fu;
    assign instr_out.microop     = instr_in.microop;
    assign instr_out.ticket      = next_ticket;
    assign instr_out.data1       = instr_in.data1;
    assign instr_out.data2       = instr_in.data2;
    assign instr_out.src1_iszero = 1'b0;
    assign instr_out.src2_iszero = 1'b0;
    assign instr_out.dst_iszero  = memory_instr & ((~load_instr & ~toepl_instr) | toepl_conf); // store instructions and toepl reconfig
                                                                                               // do not write anything
    assign instr_out.reconfigure = instr_in.reconfigure;
    // Pick the correct destination vreg
    assign instr_out.dst         = rdst_remapped ? rdst_destination :
                                   do_remap      ? next_free_vreg   :
                                                   instr_in.dst;

    // Pick the correct source vregs
    assign instr_out.src1 = (instr_in.src1 === instr_in.dst) ? instr_out.dst : remapped_src1;
    assign instr_out.src2 = (instr_in.src2 === instr_in.dst) ? instr_out.dst : remapped_src2;
    //Assign Locking Bits based on Instruction Type
    assign instr_out.lock = (memory_instr && !reconfig_instr && ~toepl_conf && toepl_instr) ? 2'b10 :
                            (memory_instr && !reconfig_instr && ~toepl_conf && load_instr ) ? 2'b11 :
                            (memory_instr && !reconfig_instr && ~toepl_conf && !load_instr) ? 2'b01 :
                                                                                              2'b00;
	//Memory Instr Out Generation
    assign m_instr_out.valid            = instr_out.valid;
    assign m_instr_out.dst              = instr_out.dst;
    assign m_instr_out.src1             = instr_out.src1;
    assign m_instr_out.src2             = instr_out.src2;
    assign m_instr_out.data1            = instr_out.data1;
    assign m_instr_out.data2            = instr_out.data2;
    assign m_instr_out.ticket           = instr_out.ticket;
    assign m_instr_out.immediate        = instr_out.immediate;
    assign m_instr_out.microop          = instr_in.microop;
    assign m_instr_out.reconfigure      = instr_in.reconfigure;
    assign m_instr_out.vl               = instr_in.vl;
    assign m_instr_out.maxvl            = instr_in.maxvl;
    assign m_instr_out.last_ticket_src1 = (last_producer[instr_in.src1] === 0) ? instr_out.ticket : last_producer[instr_in.src1];
    assign m_instr_out.last_ticket_src2 = (last_producer[instr_in.src2] === 0) ? instr_out.ticket : last_producer[instr_in.src2];

    // Do remap enablers
    assign do_remap = do_operation & ~rdst_remapped;
    always_ff @(posedge clk or negedge rst_n) begin : vregHOP
        if(~rst_n) begin
            vreg_hop <= 1;
        end else if (do_reconfigure) begin
            vreg_hop <= (instr_in.maxvl >> $clog2(VECTOR_LANES));
        end
    end

	// Next Free vreg (similar job as the FL)
    always_ff @(posedge clk or negedge rst_n) begin : FreeVreg
        if(~rst_n) begin
            next_free_vreg <= 'b0;
        end else begin
        	if (do_reconfigure) begin
        		next_free_vreg <= 'b0;
            end else if(do_remap) begin
                next_free_vreg <= next_free_vreg + vreg_hop;
            end
        end
    end

    //Next Free Ticket
    always_ff @(posedge clk or negedge rst_n) begin : NextTicket
        if(!rst_n) begin
            next_ticket <= 1;
        end else begin
            if(do_reconfigure) begin
                next_ticket <= 1;
            end else if(do_operation) begin
                next_ticket <= next_ticket +1;
                if (&next_ticket) next_ticket <= 1;
            end
        end
    end

    //RAT module - Keeps current Mappings
    vrat #(
        .TOTAL_ENTRIES(VECTOR_REGISTERS),
        .DATA_WIDTH   (REGISTER_BITS   )
    ) vrat (
        .clk        (clk               ),
        .rst_n      (rst_n             ),
        .reconfigure(do_reconfigure    ),
        //Write Port
        .write_addr (instr_in.dst      ),
        .write_data (next_free_vreg    ),
        .write_en   (do_remap          ),
        //Read Port #1
        .read_addr_1(instr_in.dst      ),
        .read_data_1(rdst_destination  ),
        .remapped_1 (rdst_remapped     ),
        //Read Port #2
        .read_addr_2(instr_in.src1     ),
        .read_data_2(remapped_src1     ),
        .remapped_2 (                  ),
        //Read Port #3
        .read_addr_3(instr_in.src2     ),
        .read_data_3(remapped_src2     ),
        .remapped_3 (                  ),
        //Mask Port (always v1)
        .mask_src   (instr_out.mask_src)
    );

    // Last producer Tracker (used for mem ops, stores do not udpate it)
    assign last_producer_wr_en = do_operation & (~memory_instr | load_instr | toepl_instr);
    always_ff @(posedge clk or negedge rst_n) begin
        if(~rst_n) begin
            last_producer <= '0;
        end else if(last_producer_wr_en) begin
            last_producer[instr_in.dst] <= next_ticket;
        end
    end

    assign is_idle_o = ~valid_in;

    //=======================================================
	// Tracking for Debugging Purposes
    //=======================================================
    logic [VECTOR_REGISTERS:0] current_remaps, max_remaps;
    always_ff @(posedge clk or negedge rst_n) begin : tracking_current_remaps
        if(~rst_n) begin
            current_remaps <= 0;
        end else begin
            if(do_reconfigure) begin
                current_remaps <= 0;
            end else if(do_remap) begin
                current_remaps <= current_remaps + 1;
            end
        end
    end

    always_ff @(posedge clk or negedge rst_n) begin : tracking_max_remaps
        if(~rst_n) begin
            max_remaps <= VECTOR_REGISTERS;
        end else begin
            if(do_reconfigure) begin
                max_remaps <= VECTOR_REGISTERS / (instr_in.maxvl >> $clog2(VECTOR_LANES));
            end
        end
    end


`ifdef MODEL_TECH
    `include "vrrm_sva.sv"
`endif

endmodule