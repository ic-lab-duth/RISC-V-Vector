/*
*
* @author VLSI Lab, EE dept., Democritus University of Thrace
*
*/
`ifdef MODEL_TECH
    `include "vmacros.sv"
`endif
localparam DUMMY_VECTOR_LANES   = 8;
localparam DUMMY_REQ_DATA_WIDTH = 512;
//---------------------------------------------------------------------------------------
//to Vector Pipeline
typedef struct packed {
    logic                                   valid      ;

    logic [                            4:0] dst        ;
    logic [                            4:0] src1       ;
    logic [                            4:0] src2       ;

    logic [                           31:0] data1      ;
    logic [                           31:0] data2      ;

    logic                                   reconfigure;
    logic [                           31:0] immediate  ;
    logic [                            1:0] fu         ;
    logic [                            6:0] microop    ;
    logic [                            1:0] use_mask   ;

    // [$clog2(VECTOR_REGISTERS*VECTOR_LANES):0]
    logic [$clog2(32*DUMMY_VECTOR_LANES):0] maxvl      ;
    logic [$clog2(32*DUMMY_VECTOR_LANES):0] vl         ;
} to_vector;
//--------------------------------------
//Remapped Vector Instruction
typedef struct packed {
    logic                                   valid      ;

    logic [                            4:0] dst        ;
    logic                                   dst_iszero ;
    logic [                            4:0] src1       ;
    logic                                   src1_iszero;
    logic [                            4:0] src2       ;
    logic                                   src2_iszero;
    logic [                            4:0] mask_src   ;

    logic [                           31:0] data1      ;
    logic [                           31:0] data2      ;

    logic                                   reconfigure;
    logic [                            4:0] ticket     ;
    logic [                           31:0] immediate  ;
    logic [                            1:0] fu         ;
    logic [                            6:0] microop    ;
    logic                                   use_mask   ;
    logic [                            1:0] lock       ;

    // [$clog2(VECTOR_REGISTERS*VECTOR_LANES):0]
    logic [$clog2(32*DUMMY_VECTOR_LANES):0] maxvl      ;
    logic [$clog2(32*DUMMY_VECTOR_LANES):0] vl         ;
} remapped_v_instr;
//--------------------------------------
//Remapped Memory Vector Instruction
typedef struct packed {
    logic                                   valid           ;

    logic [                            4:0] dst             ;
    // logic                  dst_iszero ;
    logic [                            4:0] src1            ;
    // logic                  src1_iszero;
    logic [                            4:0] src2            ;
    // logic                  src2_iszero;

    logic [                           31:0] data1           ;
    logic [                           31:0] data2           ;

    logic [                            4:0] ticket          ;
    logic [                            4:0] last_ticket_src1;
    logic [                            4:0] last_ticket_src2;
    logic [                           31:0] immediate       ;
    logic [                            6:0] microop         ;
    logic                                   reconfigure     ;

    // [$clog2(VECTOR_REGISTERS*VECTOR_LANES):0]
    logic [$clog2(32*DUMMY_VECTOR_LANES):0] maxvl           ;
    logic [$clog2(32*DUMMY_VECTOR_LANES):0] vl              ;
} memory_remapped_v_instr;
//--------------------------------------
//to_Execution Stage
typedef struct packed {
    logic        valid    ;
    logic        mask     ;

    logic [31:0] data1    ;
    logic [31:0] data2    ;
    logic [31:0] immediate;
}to_vector_exec;
typedef struct packed {
    logic [                            4:0] dst     ;
    logic [                            4:0] ticket  ;
    logic [                            1:0] fu      ;
    logic [                            6:0] microop ;
    logic [$clog2(32*DUMMY_VECTOR_LANES):0] vl      ;
    logic                                   head_uop;
    logic                                   end_uop ;
}to_vector_exec_info;
//--------------------------------------
//Vector memory Request
typedef struct packed {
    logic [                            31:0]   address;
    logic [                             6:0]   microop;
    logic [$clog2(DUMMY_REQ_DATA_WIDTH/8):0]   size   ;
    logic [        DUMMY_REQ_DATA_WIDTH-1:0]   data   ;
    logic [    $clog2(DUMMY_VECTOR_LANES):0]   ticket ; //$clog2(VECTOR_LANES)
}vector_mem_req;
//--------------------------------------
//Vector memory response
typedef struct packed {
    logic [    $clog2(DUMMY_VECTOR_LANES):0]   ticket; //$clog2(VECTOR_LANES)
    logic [$clog2(DUMMY_REQ_DATA_WIDTH/8):0]   size  ; //$clog2(REQ_DATA_WIDTH/8)
    logic [        DUMMY_REQ_DATA_WIDTH-1:0]   data  ; //REQ_DATA_WIDTH
}vector_mem_resp;
//--------------------------------------
//Int Operation Enumaration
typedef enum logic [7-1:0] {
    VADD    = 7'b0000001,
    VADDI   = 7'b0000010,
    VADDW   = 7'b0000011,
    VADDIW  = 7'b0000100,
    VSUB    = 7'b0000101,
    VSUBW   = 7'b0000110,
    VMUL    = 7'b0000111,
    VMULH   = 7'b0001000,
    VMULHSU = 7'b0001001,
    VMULHU  = 7'b0001010,
    VMULWDN = 7'b0001011,
    VDIV    = 7'b0001100,
    VDIVU   = 7'b0001101,
    VREM    = 7'b0001110,
    VREMU   = 7'b0001111,
    VSLL    = 7'b0010000,
    VSLLI   = 7'b0010001,
    VSRA    = 7'b0010010,
    VSRAI   = 7'b0010011,
    VSRL    = 7'b0010100,
    VSRLI   = 7'b0010101,
    VAND    = 7'b0010110,
    VANDI   = 7'b0010111,
    VOR     = 7'b0011000,
    VORI    = 7'b0011001,
    VXOR    = 7'b0011010,
    VXORI   = 7'b0011011,
    VSEQ    = 7'b0011100,
    VSLT    = 7'b0011101,
    VSLTU   = 7'b0011110
} v_int_op_t;