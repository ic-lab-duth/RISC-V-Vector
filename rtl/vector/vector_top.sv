/*
* @info Vector Unit Datapath
*
* @author VLSI Lab, EE dept., Democritus University of Thrace
*
*/
`ifdef MODEL_TECH
	`include "vstructs.sv"
`endif
module vector_top #(
	parameter int VECTOR_REGISTERS   = 32 ,
	parameter int VECTOR_LANES       = 8  ,
	parameter int VECTOR_ACTIVE_LN   = 4  ,
	parameter int DATA_WIDTH         = 32 ,
	parameter int ADDR_WIDTH         = 32 ,
	parameter int MEM_MICROOP_WIDTH  = 7  ,
	parameter int MICROOP_WIDTH      = 5  ,
	parameter int VECTOR_TICKET_BITS = 4  ,
	parameter int VECTOR_REQ_WIDTH   = 256,
	parameter int FWD_POINT_A        = 1  ,
	parameter int FWD_POINT_B        = 3  ,
	parameter     VECTOR_FP_ALU      = 1  ,
	parameter     VECTOR_FXP_ALU     = 0  ,
	parameter     USE_HW_UNROLL      = 1
) (
	input  logic           clk             ,
	input  logic           rst_n           ,
	output logic           vector_idle_o   ,
	//Instruction In
	input  logic           valid_in        ,
	input  to_vector       instr_in        ,
	output logic           pop             ,
	//Cache Request Interface
	output logic           mem_req_valid_o ,
	output vector_mem_req  mem_req_o       ,
	input  logic           cache_ready_i   ,
	//Cache Response Interface
	input  logic           mem_resp_valid_i,
	input  vector_mem_resp mem_resp_i
);

	logic vrrm_idle, vis_idle, vex_idle, vmu_idle;

	assign vector_idle_o = vrrm_idle & vis_idle & vex_idle & vmu_idle & rst_n;
	//////////////////////////////////////////////////
	//                 vRRM STAGE                   //
	//////////////////////////////////////////////////
	logic                   [$clog2(VECTOR_REGISTERS*VECTOR_LANES):0] vl_remapped, maxvl_remapped;
	memory_remapped_v_instr                                           m_instr_out   ;
	remapped_v_instr                                                  instr_remapped;
	logic                                                             r_valid, m_valid, ready, m_ready_r;

	vrrm #(
		.VECTOR_REGISTERS  (VECTOR_REGISTERS  ),
		.VECTOR_LANES      (VECTOR_LANES      ),
		.VECTOR_TICKET_BITS(VECTOR_TICKET_BITS)
	) vrrm (
		.clk        (clk           ),
		.rst_n      (rst_n         ),
		.is_idle_o  (vrrm_idle     ),
		//Instruction in
		.valid_in   (valid_in      ),
		.instr_in   (instr_in      ),
		.pop_instr  (pop           ),
		//Instruction out
		.valid_o    (r_valid       ),
		.instr_out  (instr_remapped),
		.ready_i    (ready         ),
		//Memory Instruction Out
		.m_valid_o  (m_valid       ),
		.m_instr_out(m_instr_out   ),
		.m_ready_i  (m_ready_r     )
	);
	//////////////////////////////////////////////////
	//           vRR/vIS PIPELINE REGISTER          //
	//////////////////////////////////////////////////
	localparam int RENAMED_VINSTR_SIZE = $bits(instr_remapped);

	remapped_v_instr        instr_remapped_o;
	logic                   r_valid_o, i_ready;
	memory_remapped_v_instr m_instr_out_r   ;
	logic                   m_valid_r, m_r_ready;

	generate
	if (USE_HW_UNROLL) begin: g_hw_unroll
		eb_buff_generic #(
			.DW       (RENAMED_VINSTR_SIZE),
			.BUFF_TYPE(1                  ),
			.DEPTH    (                   )
		) vRR_vIS (
			.clk    (clk             ),
			.rst    (~rst_n          ),

			.data_i (instr_remapped  ),
			.valid_i(r_valid         ),
			.ready_o(ready           ),

			.data_o (instr_remapped_o),
			.valid_o(r_valid_o       ),
			.ready_i(i_ready         )
		);
		//////////////////////////////////////////////////
		//           vRR/vMU PIPELINE REGISTER          //
		//////////////////////////////////////////////////
		localparam int RENAMED_MVINSTR_SIZE = $bits(m_instr_out);

		eb_buff_generic #(
			.DW       (RENAMED_MVINSTR_SIZE),
			.BUFF_TYPE(1                  ),
			.DEPTH    (                   )
		) vRR_vMU (
			.clk    (clk          ),
			.rst    (~rst_n       ),

			.data_i (m_instr_out  ),
			.valid_i(m_valid      ),
			.ready_o(m_ready_r    ),

			.data_o (m_instr_out_r),
			.valid_o(m_valid_r    ),
			.ready_i(m_r_ready    )
		);
	end else begin: g_stubs

	// vRR/vIS PIPELINE REGISTER BYPASS

	assign instr_remapped_o = instr_remapped;
	assign r_valid_o        = r_valid;
	assign ready            = i_ready;
	// vRR/vMU PIPELINE REGISTER BYPASS
	assign m_instr_out_r = m_instr_out;
	assign m_valid_r     = m_valid;
	assign m_ready_r     = m_r_ready;

	end
	endgenerate
	//////////////////////////////////////////////////
	//                 MEMORY UNIT                  //
	//////////////////////////////////////////////////
	logic                                unlock_en        ;
	logic [$clog2(VECTOR_REGISTERS)-1:0] unlock_reg_a     ;
	logic [$clog2(VECTOR_REGISTERS)-1:0] unlock_reg_b     ;
	logic [      VECTOR_TICKET_BITS-1:0] unlock_ticket    ;
	logic [            VECTOR_LANES-1:0] mem_wrtbck_en    ;
	logic [$clog2(VECTOR_REGISTERS)-1:0] mem_wrtbck_reg   ;
	logic [ VECTOR_LANES*DATA_WIDTH-1:0] mem_wrtbck_data  ;
	logic [      VECTOR_TICKET_BITS-1:0] mem_wrtbck_ticket;
	logic [$clog2(VECTOR_REGISTERS)-1:0] mem_addr_0       ;
	logic [ VECTOR_LANES*DATA_WIDTH-1:0] mem_data_0       ;
	logic                                mem_pending_0    ;
	logic [      VECTOR_TICKET_BITS-1:0] mem_ticket_0     ;
	logic [$clog2(VECTOR_REGISTERS)-1:0] mem_addr_1       ;
	logic [ VECTOR_LANES*DATA_WIDTH-1:0] mem_data_1       ;
	logic                                mem_pending_1    ;
	logic [      VECTOR_TICKET_BITS-1:0] mem_ticket_1     ;
	logic [$clog2(VECTOR_REGISTERS)-1:0] mem_addr_2       ;
	logic [ VECTOR_LANES*DATA_WIDTH-1:0] mem_data_2       ;
	logic                                mem_pending_2    ;
	logic [      VECTOR_TICKET_BITS-1:0] mem_ticket_2     ;

	logic [3:0][$clog2(VECTOR_REGISTERS)-1:0] mem_prb_reg   ;
	logic [3:0]                               mem_prb_locked;
	logic [3:0][      VECTOR_TICKET_BITS-1:0] mem_prb_ticket;

	vmu #(
		.REQ_DATA_WIDTH    (VECTOR_REQ_WIDTH  ),
		.VECTOR_REGISTERS  (VECTOR_REGISTERS  ),
		.VECTOR_LANES      (VECTOR_LANES      ),
		.DATA_WIDTH        (DATA_WIDTH        ),
		.ADDR_WIDTH        (ADDR_WIDTH        ),
		.MICROOP_WIDTH     (MEM_MICROOP_WIDTH ),
		.VECTOR_TICKET_BITS(VECTOR_TICKET_BITS)
	) vmu (
		.clk                (clk              ),
		.rst_n              (rst_n            ),
		.vmu_idle_o         (vmu_idle         ),
		//Instruction Input Interface
		.valid_in           (m_valid_r        ),
		.instr_in           (m_instr_out_r    ),
		.ready_o            (m_r_ready        ),
		//Cache Interface (OUT)
		.mem_req_valid_o    (mem_req_valid_o  ),
		.mem_req_o          (mem_req_o        ),
		.cache_ready_i      (cache_ready_i    ),
		//Cache Interface (IN)
		.mem_resp_valid_i   (mem_resp_valid_i ),
		.mem_resp_i         (mem_resp_i       ),
		//RF Interface - Loads
		.rd_addr_0_o        (mem_addr_0       ),
		.rd_data_0_i        (mem_data_0       ),
		.rd_pending_0_i     (mem_pending_0    ),
		.rd_ticket_0_i      (mem_ticket_0     ),
		//RF Interface - Stores
		.rd_addr_1_o        (mem_addr_1       ),
		.rd_data_1_i        (mem_data_1       ),
		.rd_pending_1_i     (mem_pending_1    ),
		.rd_ticket_1_i      (mem_ticket_1     ),
		.rd_addr_2_o        (mem_addr_2       ),
		.rd_data_2_i        (mem_data_2       ),
		.rd_pending_2_i     (mem_pending_2    ),
		.rd_ticket_2_i      (mem_ticket_2     ),
		//RF Writeback Interface
		.wrtbck_en_o        (mem_wrtbck_en    ),
		.wrtbck_reg_o       (mem_wrtbck_reg   ),
		.wrtbck_data_o      (mem_wrtbck_data  ),
		.wrtbck_ticket_o    (mem_wrtbck_ticket),
		//RF Writeback Probing Interface
		.wrtbck_prb_reg_o   (mem_prb_reg      ),
		.wrtbck_prb_locked_i(mem_prb_locked   ),
		.wrtbck_prb_ticket_i(mem_prb_ticket   ),
		//Unlock Interface
		.unlock_en_o        (unlock_en        ),
		.unlock_reg_a_o     (unlock_reg_a     ),
		.unlock_reg_b_o     (unlock_reg_b     ),
		.unlock_ticket_o    (unlock_ticket    )
	);
	//////////////////////////////////////////////////
	//                 ISSUE STAGE                  //
	//////////////////////////////////////////////////
	logic [            VECTOR_LANES-1:0]                 frw_a_en     ;
	logic [$clog2(VECTOR_REGISTERS)-1:0]                 frw_a_addr   ;
	logic [            VECTOR_LANES-1:0][DATA_WIDTH-1:0] frw_a_data   ;
	logic [      VECTOR_TICKET_BITS-1:0]                 frw_a_ticket ;
	logic [            VECTOR_LANES-1:0]                 frw_b_en     ;
	logic [$clog2(VECTOR_REGISTERS)-1:0]                 frw_b_addr   ;
	logic [            VECTOR_LANES-1:0][DATA_WIDTH-1:0] frw_b_data   ;
	logic [      VECTOR_TICKET_BITS-1:0]                 frw_b_ticket ;
	logic [            VECTOR_LANES-1:0]                 wrtbck_en    ;
	logic [$clog2(VECTOR_REGISTERS)-1:0]                 wrtbck_addr  ;
	logic [            VECTOR_LANES-1:0][DATA_WIDTH-1:0] wrtbck_data  ;
	logic [      VECTOR_TICKET_BITS-1:0]                 wrtbck_ticket;
	logic                                                iss_valid    ;
	logic                                                iss_ex_ready ;
	to_vector_exec                    [VECTOR_LANES-1:0] iss_to_exec_data;
	to_vector_exec_info                                  iss_to_exec_info;


	vis #(
		.VECTOR_REGISTERS  (VECTOR_REGISTERS  ),
		.VECTOR_LANES      (VECTOR_LANES      ),
		.DATA_WIDTH        (DATA_WIDTH        ),
		.VECTOR_TICKET_BITS(VECTOR_TICKET_BITS)
	) vis (
		.clk             (clk              ),
		.rst_n           (rst_n            ),
		.is_idle_o       (vis_idle         ),
		//Instruction in
		.valid_in        (r_valid_o        ),
		.instr_in        (instr_remapped_o ),
		.ready_o         (i_ready          ),
		//Instruction out
		.valid_o         (iss_valid        ),
		.data_to_exec    (iss_to_exec_data ),
		.info_to_exec    (iss_to_exec_info ),
		.ready_i         (iss_ex_ready     ),
		//Memory Unit read port
		.mem_addr_0      (mem_addr_0       ),
		.mem_data_0      (mem_data_0       ),
		.mem_pending_0   (mem_pending_0    ),
		.mem_ticket_0    (mem_ticket_0     ),
		.mem_addr_1      (mem_addr_1       ),
		.mem_data_1      (mem_data_1       ),
		.mem_pending_1   (mem_pending_1    ),
		.mem_ticket_1    (mem_ticket_1     ),
		.mem_addr_2      (mem_addr_2       ),
		.mem_data_2      (mem_data_2       ),
		.mem_pending_2   (mem_pending_2    ),
		.mem_ticket_2    (mem_ticket_2     ),
		//Memory Unit Probing port
		.mem_prb_reg_i   (mem_prb_reg      ),
		.mem_prb_locked_o(mem_prb_locked   ),
		.mem_prb_ticket_o(mem_prb_ticket   ),
		//Memory Unit write port
		.mem_wr_en       (mem_wrtbck_en    ),
		.mem_wr_ticket   (mem_wrtbck_ticket),
		.mem_wr_addr     (mem_wrtbck_reg   ),
		.mem_wr_data     (mem_wrtbck_data  ),
		// Unlock Ports
		.unlock_en       (unlock_en        ),
		.unlock_reg_a    (unlock_reg_a     ),
		.unlock_reg_b    (unlock_reg_b     ),
		.unlock_ticket   (unlock_ticket    ),
		//Forward Point #1
		.frw_a_en        (frw_a_en         ),
		.frw_a_addr      (frw_a_addr       ),
		.frw_a_data      (frw_a_data       ),
		.frw_a_ticket    (frw_a_ticket     ),
		//Forward Point #2
		.frw_b_en        (frw_b_en         ),
		.frw_b_addr      (frw_b_addr       ),
		.frw_b_data      (frw_b_data       ),
		.frw_b_ticket    (frw_b_ticket     ),
		//Writeback (from EX)
		.wr_en           (wrtbck_en        ),
		.wr_addr         (wrtbck_addr      ),
		.wr_data         (wrtbck_data      ),
		.wr_ticket       (wrtbck_ticket    )
	);
	//////////////////////////////////////////////////
	//           vIS/vEX PIPELINE REGISTER          //
	//////////////////////////////////////////////////
	localparam int EX_VINSTR_DATA_SIZE = $bits(iss_to_exec_data);
	localparam int EX_VINSTR_INFO_SIZE = $bits(iss_to_exec_info);
	to_vector_exec [ VECTOR_LANES-1:0] exec_data_o;
	to_vector_exec_info                exec_info_o;
	logic exec_valid, exec_ready;

	eb_buff_generic #(
		.DW       (EX_VINSTR_DATA_SIZE),
		.BUFF_TYPE(1                  ),
		.DEPTH    (                   )
	) vIS_vEX_data (
		.clk    (clk             ),
		.rst    (~rst_n          ),

		.data_i (iss_to_exec_data),
		.valid_i(iss_valid       ),
		.ready_o(iss_ex_ready    ),

		.data_o (exec_data_o     ),
		.valid_o(exec_valid      ),
		.ready_i(exec_ready      )
	);
	eb_buff_generic #(
		.DW       (EX_VINSTR_INFO_SIZE),
		.BUFF_TYPE(1                  ),
		.DEPTH    (                   )
	) vIS_vEX_info (
		.clk    (clk             ),
		.rst    (~rst_n          ),

		.data_i (iss_to_exec_info),
		.valid_i(iss_valid       ),
		.ready_o(                ),

		.data_o (exec_info_o     ),
		.valid_o(                ),
		.ready_i(exec_ready      )
	);
	//////////////////////////////////////////////////
	//                   EX STAGE                   //
	//////////////////////////////////////////////////
	vex #(
		.VECTOR_REGISTERS  (VECTOR_REGISTERS  ),
		.VECTOR_LANES      (VECTOR_LANES      ),
		.ADDR_WIDTH        (ADDR_WIDTH        ),
		.DATA_WIDTH        (DATA_WIDTH        ),
		.MICROOP_WIDTH     (MICROOP_WIDTH     ),
		.VECTOR_TICKET_BITS(VECTOR_TICKET_BITS),
		.FWD_POINT_A       (FWD_POINT_A       ),
		.FWD_POINT_B       (FWD_POINT_B       ),
		.VECTOR_FP_ALU     (VECTOR_FP_ALU     ),
		.VECTOR_FXP_ALU    (VECTOR_FXP_ALU    )
	) vex (
		.clk         (clk          ),
		.rst_n       (rst_n        ),
		.vex_idle_o  (vex_idle     ),
		//Issue Interface
		.valid_i     (exec_valid   ),
		.exec_data_i (exec_data_o  ),
		.exec_info_i (exec_info_o  ),
		.ready_o     (exec_ready   ),
		//Forward Point #1
		.frw_a_en    (frw_a_en     ),
		.frw_a_addr  (frw_a_addr   ),
		.frw_a_data  (frw_a_data   ),
		.frw_a_ticket(frw_a_ticket ),
		//Forward Point #2
		.frw_b_en    (frw_b_en     ),
		.frw_b_addr  (frw_b_addr   ),
		.frw_b_data  (frw_b_data   ),
		.frw_b_ticket(frw_b_ticket ),
		//Writeback
		.wr_en       (wrtbck_en    ),
		.wr_addr     (wrtbck_addr  ),
		.wr_data     (wrtbck_data  ),
		.wr_ticket   (wrtbck_ticket)
	);

`ifdef MODEL_TECH
    `include "vector_top_sva.sv"
`endif

endmodule