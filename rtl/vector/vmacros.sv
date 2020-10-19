/*
*
* @author VLSI Lab, EE dept., Democritus University of Thrace
*
*/
// FU code definitions
`define MEM_FU 2'b00
`define FP_FU  2'b01
`define INT_FU 2'b10
`define FXP_FU 2'b11

// Memory Unit definitions
`define LD_BIT           6

`define MEM_OP_RANGE_HI  5
`define MEM_OP_RANGE_LO  4

`define MEM_SZ_RANGE_HI  3
`define MEM_SZ_RANGE_LO  2

`define OP_UNIT_STRIDED  2'b00
`define OP_STRIDED       2'b10
`define OP_INDEXED       2'b11

`define SZ_8  1
`define SZ_16 2
`define SZ_32 0

`define RDC_OP_W 2
`define RDC_ADD  2'b00
`define RDC_AND  2'b10
`define RDC_OR   2'b11
`define RDC_XOR  2'b11

// Forwarding Point definitions
// _F stands for flopped
// non-flopped hurt freq
`define EX1   1
`define EX2   2
`define EX2_F 20
`define EX3   3
`define EX3_F 30
`define EX4   4
`define EX4_F 40