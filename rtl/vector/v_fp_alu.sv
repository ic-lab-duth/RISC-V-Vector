/*
* @info Vector Floating Point Unit
*
* @author VLSI Lab, EE dept., Democritus University of Thrace
*
*/
`ifdef MODEL_TECH
    `include "vstructs.sv"
`endif
module v_fp_alu #(
    parameter int DATA_WIDTH         = 32 ,
    parameter int MICROOP_WIDTH      = 5  ,
    parameter int VECTOR_TICKET_BITS = 5  ,
    parameter int VECTOR_LANE_NUM    = 1  ,
    parameter int EX1_W              = 160,
    parameter int EX2_W              = 96 ,
    parameter int EX3_W              = 96 ,
    parameter int EX4_W              = 32
) (
    input  logic                     clk            ,
    input  logic                     rst_n          ,
    input  logic                     valid_i        ,
    input  logic [   DATA_WIDTH-1:0] data_a_ex1_i   ,
    input  logic [   DATA_WIDTH-1:0] data_b_ex1_i   ,
    input  logic [   DATA_WIDTH-1:0] imm_ex1_i      ,
    input  logic [MICROOP_WIDTH-1:0] microop_i      ,
    input  logic                     mask_i         ,
    // Result Ex1 Out
    output logic                     ready_res_ex1_o,
    output logic [        EX1_W-1:0] result_ex1_o   ,
    // EX2 Data In
    input  logic [        EX1_W-1:0] data_ex2_i     ,
    input  logic                     mask_ex2_i     ,
    // Result EX2 Out
    output logic                     ready_res_ex2_o,
    output logic [        EX2_W-1:0] result_ex2_o   ,
    // EX3 Data In
    input  logic [        EX2_W-1:0] data_ex3_i     ,
    input  logic                     mask_ex3_i     ,
    // Result EX3 Out
    output logic                     ready_res_ex3_o,
    output logic [        EX3_W-1:0] result_ex3_o   ,
    // EX4 Data In
    input  logic [        EX3_W-1:0] data_ex4_i     ,
    input  logic                     mask_ex4_i     ,
    // Result EX4 Out
    output logic                     ready_res_ex4_o,
    output logic [        EX4_W-1:0] result_ex4_o
);
    logic [MICROOP_WIDTH-1:0] microop_fp_ex2;
    logic [   DATA_WIDTH-1:0] lut_res_tan   ;
    logic [   DATA_WIDTH-1:0] lut_res_sig   ;
    logic [   DATA_WIDTH-1:0] lut_res_cos   ;
    logic [        EX1_W-1:0] result_fp_ex1 ;
    logic [        EX2_W-1:0] result_fp_ex2 ;
    logic [        EX3_W-1:0] result_fp_ex3 ;
    logic [        EX4_W-1:0] result_fp_ex4 ;
    logic                     valid_fp_ex1  ;
    logic                     valid_fp_ex2  ;
    logic                     valid_fp_ex3  ;
    logic                     valid_fp_ex4  ;

    assign lut_res_tan = '0;
    assign lut_res_sig = '0;
    assign lut_res_cos = '0;
    always_comb begin
        case (microop_i)
            7'b0100000 : begin
                // VTAN
                result_fp_ex1 = lut_res_tan;
                valid_fp_ex1  = valid_i;
            end
            7'b0100001 : begin
                // VSIN
                result_fp_ex1 = lut_res_sig;
                valid_fp_ex1  = valid_i;
            end
            7'b0100010 : begin
                // VCOS
                result_fp_ex1 = lut_res_cos;
                valid_fp_ex1  = valid_i;
            end
            default : begin
                result_fp_ex1 = 'x;
                valid_fp_ex1  = 1'b0;
            end
        endcase
    end
    always_ff @(posedge clk) begin
        if (valid_fp_ex1) begin
            microop_fp_ex2 <= microop_i;
        end
    end
    always_ff @(posedge clk or negedge rst_n) begin
        if(~rst_n) begin
            valid_fp_ex2 <= 0;
        end else begin
            valid_fp_ex2 <= valid_fp_ex1;
        end
    end
    //-----------------------------------------------
    //EX2
    //-----------------------------------------------
    always_comb begin
        case (microop_fp_ex2)
            7'b0100000 : begin
                // VTAN
                result_fp_ex2 = data_ex2_i + data_ex2_i;
            end
            7'b0100001 : begin
                // VSIN
                result_fp_ex2 = data_ex2_i - data_ex2_i;
            end
            7'b0100010 : begin
                // VCOS
                result_fp_ex2 = data_ex2_i + data_ex2_i;
            end
            default : begin
                result_fp_ex2 = 'x;
            end
        endcase
    end

    assign valid_fp_ex3 = 1'b0;
    assign valid_fp_ex4 = 1'b0;
    //================================================
    // Outputs
    //================================================
    // EX1 Out
    assign ready_res_ex1_o = 1'b0;                          //no fp finishes in 1 cycle
    assign result_ex1_o    = {EX1_W{mask_i}} & result_fp_ex1;
    // EX2 Out
    assign ready_res_ex2_o = valid_fp_ex2;                 //indicate ready data
    assign result_ex2_o    = {EX2_W{mask_ex2_i}} & result_fp_ex2;
    // EX3 Out
    assign ready_res_ex3_o = valid_fp_ex3;                 //indicate ready data
    assign result_ex3_o    = {EX3_W{mask_ex3_i}} & result_fp_ex3;
    // EX4 Out
    assign ready_res_ex4_o = valid_fp_ex4;                 //indicate ready data
    assign result_ex4_o    = {EX4_W{mask_ex4_i}} & result_fp_ex4;

endmodule // v_fp_alu