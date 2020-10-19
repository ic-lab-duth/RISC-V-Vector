/*
*
* @author VLSI Lab, EE dept., Democritus University of Thrace
*
*/
`ifdef MODEL_TECH
    `include "vmacros.sv"
`endif
//============================================//
//         Scalar Pipe Parameters             //
//============================================//

//===============================
// TUNABLE PARAMETERS
//===============================

//Dual Issue Enabler
localparam int DUAL_ISSUE = 1;
//Logging Enabler
localparam int ENABLE_LOGGING = 0;

//-------------------------
//Memory System Parameters
//-------------------------
// instruction cache entries
localparam int IC_ENTRIES = 32;
// instruction cache line size
localparam int IC_DW = 256;
// instruction cache associativity
localparam int IC_ASC = 2;
// data cache entries
localparam int DC_ENTRIES = 32;
// data cache line size
localparam int DC_DW = 512;
// data cache associativity
localparam int DC_ASC = 4;
// L2 cache entries
localparam int L2_ENTRIES = 2048;
// L2 line size
localparam int L2_DW = 1024;
// Immitate a realistic memory system
localparam int REALISTIC = 1;
// Response Cycles for L2 (when realistic enabled)
localparam int DELAY_CYCLES = 10;

//---------------------------
//Branch Predictor Parameters
//---------------------------
localparam int RAS_DEPTH        = 8  ;
localparam int GSH_HISTORY_BITS = 2  ;
localparam int GSH_SIZE         = 256;
localparam int BTB_SIZE         = 256;

//===============================
// NOT !! TUNABLE PARAMETERS
//===============================

//---------------------------
//ROB Parameters
//---------------------------
localparam int ROB_ENTRIES  = 8                  ; //default: 8
localparam int ROB_TICKET_W = $clog2(ROB_ENTRIES); //default: DO NOT MODIFY

//---------------------------
//Other Parameters  (DO NOT MODIFY)
//---------------------------
localparam int ISTR_DW        = 32        ; //default: 32
localparam int ADDR_BITS      = 32        ; //default: 32
localparam int DATA_WIDTH     = 32        ; //default: 32
localparam int FETCH_WIDTH    = 64        ; //default: 64
localparam int R_WIDTH        = 6         ; //default: 6
localparam int MICROOP_W      = 5         ; //default: 5

//---------------------------
//CSR Parameters        (DO NOT MODIFY)
localparam int CSR_DEPTH = 64;

//============================================//
//         Vector Pipe Parameters             //
//============================================//
//===============================
// TUNABLE PARAMETERS
//===============================
// Enables the vector pipeline
localparam int VECTOR_ENABLED = 1;
// number of vector lanes/elements (currently max 16)
localparam int VECTOR_LANES = 8; //must also change dummy param in vstructs
// execution stage the forwardwing point will be connected to :
// EX1   1
// EX2   2
// EX2_F 20 (flopped)
// EX3   3
// EX3_F 30 (flopped)
// EX4   4
// EX4_F 40 (flopped)
localparam int VECTOR_FWD_POINT_A = `EX1;
localparam int VECTOR_FWD_POINT_B = `EX4_F;
// Enable dynamic RF allocation and hw loop unrolling
localparam     USE_HW_UNROLL      = 1;
//===============================
// NOT !! TUNABLE PARAMETERS
//===============================
//Floating Point ALU present
localparam     VECTOR_FP_ALU      = 1;
//Fixed Point ALU not present yet
localparam     VECTOR_FXP_ALU     = 0;
localparam int VECTOR_REGISTERS         = 32 ; //default: 32
localparam int VECTOR_MEM_MICROOP_WIDTH = 7  ; //default: 7
localparam int VECTOR_MICROOP_WIDTH     = 7  ; //default: 7
localparam int VECTOR_TICKET_BITS       = 5  ; //default: 5
localparam int VECTOR_MAX_REQ_WIDTH     = 512; //default: 256