/*
* @info Vector Integer Unit
*
* @author VLSI Lab, EE dept., Democritus University of Thrace
*
*/
`ifdef MODEL_TECH
    `include "vstructs.sv"
`endif
module v_int_alu #(
    parameter int DATA_WIDTH         = 32 ,
    parameter int MICROOP_WIDTH      = 5  ,
    parameter int VECTOR_TICKET_BITS = 5  ,
    parameter int VECTOR_REGISTERS   = 32 ,
    parameter int VECTOR_LANES       = 8  ,
    parameter int VECTOR_LANE_NUM    = 1  ,
    parameter int EX1_W              = 160,
    parameter int EX2_W              = 96 ,
    parameter int EX3_W              = 96 ,
    parameter int EX4_W              = 32
) (
    input  logic                                           clk            ,
    input  logic                                           rst_n          ,
    input  logic                                           valid_i        ,
    input  logic [                         DATA_WIDTH-1:0] data_a_ex1_i   ,
    input  logic [                         DATA_WIDTH-1:0] data_b_ex1_i   ,
    input  logic [                         DATA_WIDTH-1:0] imm_ex1_i      ,
    input  logic [                      MICROOP_WIDTH-1:0] microop_i      ,
    input  logic                                           mask_i         ,
    input  logic [$clog2(VECTOR_REGISTERS*VECTOR_LANES):0] vl_i           ,
    // Reduction Tree Inputs
    input  logic [                         DATA_WIDTH-1:0] rdc_data_ex1_i ,
    input  logic [                         DATA_WIDTH-1:0] rdc_data_ex2_i ,
    input  logic [                         DATA_WIDTH-1:0] rdc_data_ex3_i ,
    input  logic [                         DATA_WIDTH-1:0] rdc_data_ex4_i ,
    // Result Ex1 Out
    output logic                                           ready_res_ex1_o,
    output logic [                              EX1_W-1:0] result_ex1_o   ,
    // EX2 Data In
    input  logic [                              EX1_W-1:0] data_ex2_i     ,
    input  logic                                           mask_ex2_i     ,
    // Result EX2 Out
    output logic                                           ready_res_ex2_o,
    output logic [                              EX2_W-1:0] result_ex2_o   ,
    // EX3 Data In
    input  logic [                              EX2_W-1:0] data_ex3_i     ,
    input  logic                                           mask_ex3_i     ,
    // Result EX3 Out
    output logic                                           ready_res_ex3_o,
    output logic [                              EX3_W-1:0] result_ex3_o   ,
    // EX4 Data In
    input  logic [                              EX3_W-1:0] data_ex4_i     ,
    input  logic                                           mask_ex4_i     ,
    // Result EX4 Out
    output logic [                          `RDC_OP_W-1:0] rdc_op_ex4_o   ,
    output logic                                           ready_res_ex4_o,
    output logic [                              EX4_W-1:0] result_ex4_o
);

    localparam int PARTIAL_SUM_W   = DATA_WIDTH +8             ;
    localparam int DIV_CALC_CYCLES = 4                         ;
    localparam int DIV_BIT_GROUPS  = DATA_WIDTH/DIV_CALC_CYCLES;

    logic [DATA_WIDTH-1:0] data_a_u_ex1 ;
    logic [DATA_WIDTH-1:0] data_b_u_ex1 ;
    logic [DATA_WIDTH-1:0] imm_u_ex1    ;
    logic [DATA_WIDTH-1:0] data_a_s_ex1 ;
    logic [DATA_WIDTH-1:0] data_b_s_ex1 ;
    logic [DATA_WIDTH-1:0] imm_s_ex1    ;
    logic [DATA_WIDTH-1:0] data_a_wu_ex1;
    logic [DATA_WIDTH-1:0] data_b_wu_ex1;
    logic [DATA_WIDTH-1:0] imm_wu_ex1   ;

    logic valid_int_ex1;
    logic valid_mul_ex1;
    logic valid_mul_ex2;
    logic valid_mul_ex3;
    logic valid_div_ex1;
    logic valid_div_ex2;
    logic valid_div_ex3;
    logic valid_div_ex4;

    logic [EX1_W-1:0] result_int_ex1;

    logic [EX1_W-1:0] result_mul_ex1;
    logic [EX2_W-1:0] result_mul_ex2;
    logic [EX3_W-1:0] result_mul_ex3;

    logic [EX1_W-1:0] result_div_ex1;
    logic [EX2_W-1:0] result_div_ex2;
    logic [EX3_W-1:0] result_div_ex3;
    logic [EX4_W-1:0] result_div_ex4;

    logic [EX1_W-1:0] result_rdc_ex1;
    logic [EX2_W-1:0] result_rdc_ex2;
    logic [EX3_W-1:0] result_rdc_ex3;
    logic [EX4_W-1:0] result_rdc_ex4;

    assign data_a_u_ex1 = $unsigned(data_a_ex1_i);
    assign data_b_u_ex1 = $unsigned(data_b_ex1_i);
    assign imm_u_ex1    = $unsigned(imm_ex1_i);

    assign data_a_s_ex1 = $signed(data_a_ex1_i);
    assign data_b_s_ex1 = $signed(data_b_ex1_i);
    assign imm_s_ex1    = $signed(imm_ex1_i);

    assign data_a_wu_ex1 = {{16{1'b0}},data_a_u_ex1[15:0]};
    assign data_b_wu_ex1 = {{16{1'b0}},data_b_u_ex1[15:0]};
    assign imm_wu_ex1    = {{16{1'b0}},imm_u_ex1[15:0]};

    //================================================
    // INT Section (no mul/div)
    //================================================
    logic [DATA_WIDTH-1:0] result_int;
    always_comb begin
        case (microop_i)
            7'b0000001 : begin
                // VADD
                result_int    = data_a_u_ex1 + data_b_u_ex1;
                valid_int_ex1 = valid_i;
            end
            7'b0000010 : begin
                // VADDI
                result_int    = data_a_u_ex1 + imm_u_ex1;
                valid_int_ex1 = valid_i;
            end
            7'b0000011 : begin
                // VADDW
                result_int    = data_a_wu_ex1 + data_b_wu_ex1;
                valid_int_ex1 = valid_i;
            end
            7'b0000100 : begin
                // VADDIW
                result_int    = data_a_wu_ex1 + imm_wu_ex1;
                valid_int_ex1 = valid_i;
            end
            7'b0000101 : begin
                // VSUB
                result_int    = data_a_u_ex1 - data_b_u_ex1;
                valid_int_ex1 = valid_i;
            end
            7'b0000110 : begin
                // VSUBW
                result_int    = data_a_wu_ex1 - data_b_wu_ex1;
                valid_int_ex1 = valid_i;
            end
            7'b0010000 : begin
                // VSLL
                result_int    = data_a_u_ex1 << data_b_u_ex1[4:0];
                valid_int_ex1 = valid_i;
            end
            7'b0010001 : begin
                // VSLLI
                result_int    = data_a_s_ex1 << imm_u_ex1[4:0];
                valid_int_ex1 = valid_i;
            end
            7'b0010010 : begin
                // VSRA
                result_int    = data_a_u_ex1 >>> data_b_u_ex1[4:0];
                valid_int_ex1 = valid_i;
            end
            7'b0010011 : begin
                // VSRAI
                result_int    = data_a_s_ex1 >>> imm_u_ex1[4:0];
                valid_int_ex1 = valid_i;
            end
            7'b0010100 : begin
                // VSRL
                result_int    = data_a_u_ex1 >> data_b_u_ex1[4:0];
                valid_int_ex1 = valid_i;
            end
            7'b0010101 : begin
                // VSRLI
                result_int    = data_a_s_ex1 >> imm_u_ex1[4:0];
                valid_int_ex1 = valid_i;
            end
            7'b0010110 : begin
                // VAND
                result_int    = data_a_u_ex1 & data_b_u_ex1;
                valid_int_ex1 = valid_i;
            end
            7'b0010111 : begin
                // VANDI
                result_int    = data_a_u_ex1 & imm_u_ex1;
                valid_int_ex1 = valid_i;
            end
            7'b0011000 : begin
                // VOR
                result_int    = data_a_u_ex1 | data_b_u_ex1;
                valid_int_ex1 = valid_i;
            end
            7'b0011001 : begin
                // VORI
                result_int    = data_a_u_ex1 | imm_u_ex1;
                valid_int_ex1 = valid_i;
            end
            7'b0011010 : begin
                // VXOR
                result_int    = data_a_u_ex1 ^ data_b_u_ex1;
                valid_int_ex1 = valid_i;
            end
            7'b0011011 : begin
                // VXORI
                result_int    = data_a_u_ex1 ^ imm_u_ex1;
                valid_int_ex1 = valid_i;
            end
            7'b0011100 : begin
                // VSEQ
                result_int    = (data_a_ex1_i === data_b_ex1_i);
                valid_int_ex1 = valid_i;
            end
            7'b0011101 : begin
                // VSLT
                result_int    = (data_a_ex1_i < data_b_ex1_i);
                valid_int_ex1 = valid_i;
            end
            7'b0011110 : begin
                // VSLTU
                result_int    = (data_a_u_ex1 < data_b_u_ex1);
                valid_int_ex1 = valid_i;
            end
            7'b0100000 : begin
                // VRELU
                result_int    = (data_a_s_ex1 > 0) ? data_a_u_ex1 : '0;
                valid_int_ex1 = valid_i;
            end
            7'b0100001 : begin
                // VSTEP
                result_int    = (data_a_s_ex1 >= 0) ? 'd1 : 'd0;
                valid_int_ex1 = valid_i;
            end
            7'b0100010 : begin
                // VBRELU
                if (~data_a_s_ex1[0]) begin //imod2==0 -> relu
                    result_int = (data_a_s_ex1 > 0) ? data_a_u_ex1 : '0;
                end else begin              //imod2!=0 -> inverse relu
                    result_int = (data_a_s_ex1 > 0) ? '0           : ~data_a_ex1_i +1 ;
                end
                valid_int_ex1 = valid_i;
            end
            7'b0100011 : begin
                // VPRELU
                result_int    = data_a_ex1_i;
                valid_int_ex1 = valid_i & (data_a_s_ex1 >= 0);
            end
            default : begin
                result_int    = 'x;
                valid_int_ex1 = 1'b0;
            end
        endcase
    end
    assign result_int_ex1 = {{EX1_W-DATA_WIDTH{1'b0}},result_int};
    //================================================
    // MUL Section
    //================================================
    logic                    diff_type      ;
    logic                    upper_part     ;
    logic                    upper_part_ex2 ;
    logic                    upper_part_ex3 ;
    logic                    sign_mul_ex1   ;
    logic                    sign_ex2       ;
    logic                    sign_ex3       ;

    always_comb begin
        case (microop_i)
            7'b0000111 : begin
                // VMUL
                sign_mul_ex1  = 1'b1;
                valid_mul_ex1 = valid_i;
                diff_type     = 1'b0;
                upper_part    = 1'b0;
            end
            7'b0001000 : begin
                // VMULH
                sign_mul_ex1  = 1'b1;
                valid_mul_ex1 = valid_i;
                diff_type     = 1'b0;
                upper_part    = 1'b1;
            end
            7'b0001001 : begin
                // VMULHSU
                sign_mul_ex1  = 1'b0;
                valid_mul_ex1 = valid_i;
                diff_type     = 1'b1;
                upper_part    = 1'b1;
            end
            7'b0001010 : begin
                // VMULHU
                sign_mul_ex1  = 1'b0;
                valid_mul_ex1 = valid_i;
                diff_type     = 1'b0;
                upper_part    = 1'b1;
            end
            7'b0001011 : begin
                // VMULWDN
                sign_mul_ex1  = 1'b1;
                valid_mul_ex1 = valid_i;
                diff_type     = 1'b0;
                upper_part    = 1'b0;
            end
            7'b0100100 : begin
                // VPRELU
                sign_mul_ex1  = 1'b1;
                valid_mul_ex1 = valid_i & (data_a_s_ex1 < 0);
                diff_type     = 1'b0;
                upper_part    = 1'b0;
            end
            default : begin
                sign_mul_ex1  = 1'bx;
                valid_mul_ex1 = 1'b0;
                diff_type     = 1'bx;
                upper_part    = 1'bx;
            end
        endcase
    end
    //-----------------------------------------------
    //MUL:EX1
    //-----------------------------------------------
    logic [DATA_WIDTH-1+8:0] part_1, part_2, part_3, part_4;
    logic [  DATA_WIDTH-1:0] data_a, data_b;

    assign data_a         = (!sign_mul_ex1 || !data_a_ex1_i[31]) ?  data_a_ex1_i : ~data_a_ex1_i + 1'b1;
    assign data_b         = (!sign_mul_ex1 || !data_b_ex1_i[31]) ?  data_b_ex1_i : ~data_b_ex1_i + 1'b1;
    //Create Partial Products
    assign part_1         = data_a * data_b[7:0];
    assign part_2         = data_a * data_b[15:8];
    assign part_3         = data_a * data_b[23:16];
    assign part_4         = data_a * data_b[31:24];
    assign result_mul_ex1 = {part_4,part_3,part_2,part_1};
    always_ff @(posedge clk) begin
        if (valid_mul_ex1) begin
            sign_ex2       <= diff_type ? data_a_ex1_i[31] : sign_mul_ex1 && data_a_ex1_i[31]^data_b_ex1_i[31];
            upper_part_ex2 <= upper_part;
        end
    end
    always_ff @(posedge clk or negedge rst_n) begin
        if(~rst_n) begin
            valid_mul_ex2 <= 0;
        end else begin
            valid_mul_ex2 <= valid_mul_ex1;
        end
    end
    //-----------------------------------------------
    //MUL:EX2
    //-----------------------------------------------
    logic [2*DATA_WIDTH-1:0] extended_1,extended_2,extended_3,extended_4;
    logic [DATA_WIDTH-1+8:0] part_1_ex2, part_2_ex2, part_3_ex2, part_4_ex2;
    logic [2*DATA_WIDTH-1:0] extended_sum;

    assign part_1_ex2     = data_ex2_i[0               +: PARTIAL_SUM_W];
    assign part_2_ex2     = data_ex2_i[PARTIAL_SUM_W   +: PARTIAL_SUM_W];
    assign part_3_ex2     = data_ex2_i[2*PARTIAL_SUM_W +: PARTIAL_SUM_W];
    assign part_4_ex2     = data_ex2_i[3*PARTIAL_SUM_W +: PARTIAL_SUM_W];
    assign extended_1     = {24*{1'b0},part_1_ex2};
    assign extended_2     = {16*{1'b0},part_2_ex2,8*{1'b0}};
    assign extended_3     = {8*{1'b0},part_3_ex2,16*{1'b0}};
    assign extended_4     = {part_4_ex2,24*{1'b0}};
    assign extended_sum   = extended_1+extended_2+extended_3+extended_4;

    assign result_mul_ex2 = {{EX2_W-2*DATA_WIDTH{1'b0}},extended_sum};

    always_ff @(posedge clk) begin
        if (valid_mul_ex2) begin
            sign_ex3       <= sign_ex2;
            upper_part_ex3 <= upper_part_ex2;
        end
    end
    always_ff @(posedge clk or negedge rst_n) begin
        if(~rst_n) begin
            valid_mul_ex3 <= 0;
        end else begin
            valid_mul_ex3 <= valid_mul_ex2;
        end
    end
    //-----------------------------------------------
    //MUL:EX3
    //-----------------------------------------------
    logic [2*DATA_WIDTH-1:0] result_ex3_temp;
    logic [2*DATA_WIDTH-1:0] result_mul_wide;

    assign result_ex3_temp = data_ex3_i[0 +: 2*DATA_WIDTH];
    assign result_mul_wide = !sign_ex3 ? result_ex3_temp : ~result_ex3_temp + 1'b1;
    assign result_mul_ex3  = upper_part_ex3 ? {{EX3_W-DATA_WIDTH{1'b0}},result_mul_wide[DATA_WIDTH +: DATA_WIDTH]} :
                                              {{EX3_W-DATA_WIDTH{1'b0}},result_mul_wide[0          +: DATA_WIDTH]};
    //================================================
    // DIV Section
    //================================================
    logic sign_div_ex1, is_rem_ex1;
    logic sign_div_ex2, sign_res_div_ex2, is_rem_ex2;
    logic sign_div_ex3, sign_res_div_ex3, is_rem_ex3;
    logic sign_div_ex4, sign_res_div_ex4, is_rem_ex4;

    always_comb begin
        case (microop_i)
            7'b0001100 : begin
                // VDIV
                valid_div_ex1 = valid_i;
                sign_div_ex1  = 1'b1;
                is_rem_ex1    = 1'b0;
            end
            7'b0001101 : begin
                // VDIVU
                valid_div_ex1 = valid_i;
                sign_div_ex1  = 1'b0;
                is_rem_ex1    = 1'b0;
            end
            7'b0001110 : begin
                // VREM
                valid_div_ex1 = valid_i;
                sign_div_ex1  = 1'b1;
                is_rem_ex1    = 1'b1;
            end
            7'b0001111 : begin
                // VREMU
                valid_div_ex1 = valid_i;
                sign_div_ex1  = 1'b0;
                is_rem_ex1    = 1'b1;
            end
            default : begin
                valid_div_ex1 = 1'b0;
                sign_div_ex1  = 1'bx;
                is_rem_ex1    = 1'bx;
            end
        endcase
    end

    //-----------------------------------------------
    //DIV:EX1
    //-----------------------------------------------
    logic [DATA_WIDTH-1:0] dividend, divider;
    logic [DATA_WIDTH-1:0] remainder_init_ex1, quotient_init_ex1, divider_init_ex1;
    logic [DATA_WIDTH-1:0] remainder_ex1, quotient_ex1;
    logic [  DATA_WIDTH:0] diff_ex1          ;

    assign dividend           = data_a_ex1_i;
    assign divider            = data_b_ex1_i;

    assign quotient_init_ex1  = (!sign_div_ex1 || !dividend[31]) ? dividend : ~dividend + 1'b1;
    assign remainder_init_ex1 = '0;
    assign divider_init_ex1   = (!sign_div_ex1 || !divider[31])  ? divider : ~divider + 1'b1;

    always_comb begin : division_ex1
        remainder_ex1 = {remainder_init_ex1[DATA_WIDTH-2:0],quotient_init_ex1[DATA_WIDTH-1]};
        quotient_ex1  = quotient_init_ex1 << 1 ;
        diff_ex1      = remainder_ex1 - divider_init_ex1;
        if(diff_ex1[DATA_WIDTH] == 1) begin
            quotient_ex1[0] = 0;
        end else begin
            quotient_ex1[0] = 1;
            remainder_ex1   = remainder_ex1 - divider_init_ex1;
        end
        for(int i = 0; i < DIV_BIT_GROUPS-1; i++)    begin
            remainder_ex1 = {remainder_ex1[DATA_WIDTH-2:0],quotient_ex1[DATA_WIDTH-1]};
            quotient_ex1  = quotient_ex1 << 1 ;
            diff_ex1      = remainder_ex1 - divider_init_ex1;
            if(diff_ex1[DATA_WIDTH] == 1) begin
                quotient_ex1[0] = 0;
            end else begin
                quotient_ex1[0] = 1;
                remainder_ex1   = remainder_ex1 - divider_init_ex1;
            end
        end
    end

    assign result_div_ex1 = {{EX1_W-3*DATA_WIDTH{1'b0}},quotient_ex1,remainder_ex1,divider_init_ex1};

    always_ff @(posedge clk) begin
        if (valid_div_ex1) begin
            sign_div_ex2     <= sign_div_ex1 & dividend[31];
            sign_res_div_ex2 <= sign_div_ex1 & dividend[31]^divider[31];
            is_rem_ex2       <= is_rem_ex1;
        end
    end
    always_ff @(posedge clk or negedge rst_n) begin
        if(~rst_n) begin
            valid_div_ex2 <= 0;
        end else begin
            valid_div_ex2 <= valid_div_ex1;
        end
    end
    //-----------------------------------------------
    //DIV:EX2
    //-----------------------------------------------
    logic [DATA_WIDTH-1:0] remainder_init_ex2, quotient_init_ex2, divider_init_ex2;
    logic [DATA_WIDTH-1:0] remainder_ex2, quotient_ex2;
    logic [  DATA_WIDTH:0] diff_ex2;

    assign divider_init_ex2   = data_ex2_i[0            +: DATA_WIDTH];
    assign remainder_init_ex2 = data_ex2_i[DATA_WIDTH   +: DATA_WIDTH];
    assign quotient_init_ex2  = data_ex2_i[2*DATA_WIDTH +: DATA_WIDTH];

    always_comb begin : division_ex2
        remainder_ex2 = {remainder_init_ex2[DATA_WIDTH-2:0],quotient_init_ex2[DATA_WIDTH-1]};
        quotient_ex2  = quotient_init_ex2 << 1 ;
        diff_ex2      = remainder_ex2 - divider_init_ex2;
        if(diff_ex2[DATA_WIDTH] == 1) begin
            quotient_ex2[0] = 0;
        end else begin
            quotient_ex2[0] = 1;
            remainder_ex2   = remainder_ex2 - divider_init_ex2;
        end
        for(int i = 0; i < DIV_BIT_GROUPS-1; i++)    begin
            remainder_ex2 = {remainder_ex2[DATA_WIDTH-2:0],quotient_ex2[DATA_WIDTH-1]};
            quotient_ex2  = quotient_ex2 << 1 ;
            diff_ex2      = remainder_ex2 - divider_init_ex2;
            if(diff_ex2[DATA_WIDTH] == 1) begin
                quotient_ex2[0] = 0;
            end else begin
                quotient_ex2[0] = 1;
                remainder_ex2   = remainder_ex2 - divider_init_ex2;
            end
        end
    end

    assign result_div_ex2 = {{EX2_W-3*DATA_WIDTH{1'b0}},quotient_ex2,remainder_ex2,divider_init_ex2};

    always_ff @(posedge clk) begin
        if (valid_div_ex2) begin
            sign_div_ex3     <= sign_div_ex2;
            sign_res_div_ex3 <= sign_res_div_ex2;
            is_rem_ex3       <= is_rem_ex2;
        end
    end
    always_ff @(posedge clk or negedge rst_n) begin
        if(~rst_n) begin
            valid_div_ex3 <= 0;
        end else begin
            valid_div_ex3 <= valid_div_ex2;
        end
    end
    //-----------------------------------------------
    //DIV:EX3
    //-----------------------------------------------
    logic [DATA_WIDTH-1:0] remainder_init_ex3, quotient_init_ex3, divider_init_ex3;
    logic [DATA_WIDTH-1:0] remainder_ex3, quotient_ex3;
    logic [  DATA_WIDTH:0] diff_ex3;

    assign divider_init_ex3   = data_ex3_i[0            +: DATA_WIDTH];
    assign remainder_init_ex3 = data_ex3_i[DATA_WIDTH   +: DATA_WIDTH];
    assign quotient_init_ex3  = data_ex3_i[2*DATA_WIDTH +: DATA_WIDTH];

    always_comb begin : division_ex3
        remainder_ex3 = {remainder_init_ex3[DATA_WIDTH-2:0],quotient_init_ex3[DATA_WIDTH-1]};
        quotient_ex3  = quotient_init_ex3 << 1 ;
        diff_ex3      = remainder_ex3 - divider_init_ex3;
        if(diff_ex3[DATA_WIDTH] == 1) begin
            quotient_ex3[0] = 0;
        end else begin
            quotient_ex3[0] = 1;
            remainder_ex3   = remainder_ex3 - divider_init_ex3;
        end
        for(int i = 0; i < DIV_BIT_GROUPS-1; i++)    begin
            remainder_ex3 = {remainder_ex3[DATA_WIDTH-2:0],quotient_ex3[DATA_WIDTH-1]};
            quotient_ex3  = quotient_ex3 << 1 ;
            diff_ex3      = remainder_ex3-divider_init_ex3;
            if(diff_ex3[DATA_WIDTH] == 1) begin
                quotient_ex3[0] = 0;
            end else begin
                quotient_ex3[0] = 1;
                remainder_ex3   = remainder_ex3 - divider_init_ex3;
            end
        end
    end

    assign result_div_ex3 = {{EX3_W-3*DATA_WIDTH{1'b0}},quotient_ex3,remainder_ex3,divider_init_ex3};

    always_ff @(posedge clk) begin
        if (valid_div_ex3) begin
            sign_div_ex4     <= sign_div_ex3;
            sign_res_div_ex4 <= sign_res_div_ex3;
            is_rem_ex4       <= is_rem_ex3;
        end
    end
    always_ff @(posedge clk or negedge rst_n) begin
        if(~rst_n) begin
            valid_div_ex4 <= 0;
        end else begin
            valid_div_ex4 <= valid_div_ex3;
        end
    end
    //-----------------------------------------------
    //DIV:EX4
    //-----------------------------------------------
    logic [DATA_WIDTH-1:0] remainder_init_ex4, quotient_init_ex4, divider_init_ex4;
    logic [DATA_WIDTH-1:0] remainder_ex4, quotient_ex4;
    logic [DATA_WIDTH-1:0] remainder_final, result_final;
    logic [  DATA_WIDTH:0] diff_ex4;

    assign divider_init_ex4   = data_ex4_i[0            +: DATA_WIDTH];
    assign remainder_init_ex4 = data_ex4_i[DATA_WIDTH   +: DATA_WIDTH];
    assign quotient_init_ex4  = data_ex4_i[2*DATA_WIDTH +: DATA_WIDTH];

    always_comb begin : division_ex4
        remainder_ex4 = {remainder_init_ex4[DATA_WIDTH-2:0],quotient_init_ex4[DATA_WIDTH-1]};
        quotient_ex4  = quotient_init_ex4 << 1 ;
        diff_ex4      = remainder_ex4 - divider_init_ex4;
        if(diff_ex4[DATA_WIDTH] == 1) begin
            quotient_ex4[0] = 0;
        end else begin
            quotient_ex4[0] = 1;
            remainder_ex4   = remainder_ex4 - divider_init_ex4;
        end
        for(int i = 0; i < DIV_BIT_GROUPS-1; i++)    begin
            remainder_ex4 = {remainder_ex4[DATA_WIDTH-2:0],quotient_ex4[DATA_WIDTH-1]};
            quotient_ex4  = quotient_ex4 << 1 ;
            diff_ex4      = remainder_ex4 - divider_init_ex4;
            if(diff_ex4[DATA_WIDTH] == 1) begin
                quotient_ex4[0] = 0;
            end else begin
                quotient_ex4[0] = 1;
                remainder_ex4   = remainder_ex4 - divider_init_ex4;
            end
        end
    end

    assign remainder_final = (!sign_div_ex4)     ? remainder_ex4   : ~remainder_ex4 + 1'b1;
    assign result_final    = (!sign_res_div_ex4) ? quotient_ex4    : ~quotient_ex4 + 1'b1;
    assign result_div_ex4  = is_rem_ex4          ? {{EX4_W-DATA_WIDTH{1'b0}},remainder_final} :
                                                   {{EX4_W-DATA_WIDTH{1'b0}},result_final};


    //================================================
    // Reduction Tree Section
    //================================================
    //-----------------------------------------------
    //RDC:EX1
    //-----------------------------------------------
    logic [$clog2(VECTOR_REGISTERS*VECTOR_LANES):0] vl_ex2, vl_ex3, vl_ex4;
    logic [                         DATA_WIDTH-1:0] tree_result_ex1, tree_result_ex2;
    logic [                         DATA_WIDTH-1:0] tree_result_ex3, tree_result_ex4;
    logic [                          `RDC_OP_W-1:0] rdc_op_ex1, rdc_op_ex2, rdc_op_ex3, rdc_op_ex4;

    logic active_rdc_ex1, active_rdc_ex2, active_rdc_ex3, active_rdc_ex4;
    logic valid_rdc_ex1, valid_rdc_ex2, valid_rdc_ex3, valid_rdc_ex4;

    generate if (!VECTOR_LANE_NUM[0]) begin: g_rdc_ex1
        logic odd_rdc_override;
        assign odd_rdc_override = ((vl_i -1) == VECTOR_LANE_NUM);
        always_comb begin
            case (microop_i)
                7'b1000000 : begin
                    // VRADD
                    tree_result_ex1 = odd_rdc_override ? data_a_ex1_i : (data_a_ex1_i + rdc_data_ex1_i);
                    active_rdc_ex1  = valid_i;
                    valid_rdc_ex1   = valid_i & ((vl_i <= 'd2) | (vl_i > 'd2 & VECTOR_LANES == 2));
                    rdc_op_ex1      = `RDC_ADD;
                end
                7'b1000001 : begin
                    // VRAND
                    tree_result_ex1 = odd_rdc_override ? data_a_ex1_i : (data_a_ex1_i & rdc_data_ex1_i);
                    active_rdc_ex1  = valid_i;
                    valid_rdc_ex1   = valid_i & ((vl_i <= 'd2) | (vl_i > 'd2 & VECTOR_LANES == 2));
                    rdc_op_ex1      = `RDC_AND;
                end
                7'b1000010 : begin
                    // VROR
                    tree_result_ex1 = odd_rdc_override ? data_a_ex1_i : (data_a_ex1_i | rdc_data_ex1_i);
                    active_rdc_ex1  = valid_i;
                    valid_rdc_ex1   = valid_i & ((vl_i <= 'd2) | (vl_i > 'd2 & VECTOR_LANES == 2));
                    rdc_op_ex1      = `RDC_OR;
                end
                7'b1000011 : begin
                    // VRXOR
                    tree_result_ex1 = odd_rdc_override ? data_a_ex1_i : (data_a_ex1_i ^ rdc_data_ex1_i);
                    active_rdc_ex1  = valid_i;
                    valid_rdc_ex1   = valid_i & ((vl_i <= 'd2) | (vl_i > 'd2 & VECTOR_LANES == 2));
                    rdc_op_ex1      = `RDC_XOR;
                end
                default : begin
                    tree_result_ex1 = 'x;
                    active_rdc_ex1  = 1'b0;
                    valid_rdc_ex1   = 1'b0;
                    rdc_op_ex1      = 'x;
                end
            endcase
        end

        assign result_rdc_ex1 = {{EX1_W-DATA_WIDTH{1'b0}},tree_result_ex1};
        always_ff @(posedge clk) begin
            if (active_rdc_ex1) begin
                rdc_op_ex2 <= rdc_op_ex1;
            end
        end

    end else begin: g_rdc_ex1_stubs
        assign active_rdc_ex1 = 1'b0;
        assign valid_rdc_ex1  = 1'b0;
    end endgenerate
    //-----------------------------------------------
    //RDC:EX2
    //-----------------------------------------------
    generate if (VECTOR_LANES > 2 & VECTOR_LANE_NUM[1:0] == 2'b00) begin: g_rdc_ex2
        always_ff @(posedge clk or negedge rst_n) begin
            if(~rst_n) begin
                active_rdc_ex2 <= 1'b0;
            end else begin
                active_rdc_ex2 <= active_rdc_ex1;
                vl_ex2         <= vl_i;
            end
        end

        assign valid_rdc_ex2  = active_rdc_ex2 & (
                                (vl_ex2 <= 'd4)  |
                                (vl_ex2 > 'd4 & VECTOR_LANES == 4)) ;
        // EX2 outputs
        always_comb begin
            case (rdc_op_ex2)
                `RDC_ADD : begin
                    // VRADD
                    tree_result_ex2 = data_ex2_i[0 +: DATA_WIDTH] + rdc_data_ex2_i;
                end
                `RDC_AND : begin
                    // VRAND
                    tree_result_ex2 = data_ex2_i[0 +: DATA_WIDTH] & rdc_data_ex2_i;
                end
                `RDC_OR : begin
                    // VROR
                    tree_result_ex2 = data_ex2_i[0 +: DATA_WIDTH] | rdc_data_ex2_i;
                end
                `RDC_XOR : begin
                    // VRXOR
                    tree_result_ex2 = data_ex2_i[0 +: DATA_WIDTH] ^ rdc_data_ex2_i;
                end
                default : begin
                    tree_result_ex2 = 'x;
                end
            endcase
        end

        assign result_rdc_ex2 = {{EX2_W-DATA_WIDTH{1'b0}},tree_result_ex2};

        always_ff @(posedge clk) begin
            if (active_rdc_ex2) begin
                rdc_op_ex3 <= rdc_op_ex2;
            end
        end

    end else begin: g_rdc_ex2_stubs
        assign active_rdc_ex2 = 1'b0;
        assign valid_rdc_ex2  = 1'b0;
    end endgenerate
    //-----------------------------------------------
    //RDC:EX3
    //-----------------------------------------------
    generate if (VECTOR_LANES > 4 & VECTOR_LANE_NUM[2:0] == 3'b000) begin: g_rdc_ex3
        always_ff @(posedge clk or negedge rst_n) begin
            if(~rst_n) begin
                active_rdc_ex3 <= 0;
            end else begin
                active_rdc_ex3 <= active_rdc_ex2;
                vl_ex3         <= vl_ex2;
            end
        end

        assign valid_rdc_ex3  = active_rdc_ex3 & (
                                (vl_ex3 <= 'd8)  |
                                (vl_ex3 > 'd8 & VECTOR_LANES == 8)) ;
        // EX3 outputs
        always_comb begin
            case (rdc_op_ex3)
                `RDC_ADD: begin
                    // VRADD
                    tree_result_ex3 = data_ex3_i[0 +: DATA_WIDTH] + rdc_data_ex3_i;
                end
                `RDC_AND: begin
                    // VRAND
                    tree_result_ex3 = data_ex3_i[0 +: DATA_WIDTH] & rdc_data_ex3_i;
                end
                `RDC_OR: begin
                    // VROR
                    tree_result_ex3 = data_ex3_i[0 +: DATA_WIDTH] | rdc_data_ex3_i;
                end
                `RDC_XOR: begin
                    // VRXOR
                    tree_result_ex3 = data_ex3_i[0 +: DATA_WIDTH] ^ rdc_data_ex3_i;
                end
                default : begin
                    tree_result_ex3 = 'x;
                end
            endcase
        end

        assign result_rdc_ex3 = {{EX3_W-DATA_WIDTH{1'b0}},tree_result_ex3};

        always_ff @(posedge clk) begin
            if (active_rdc_ex3) begin
                rdc_op_ex4 <= rdc_op_ex3;
            end
        end

    end else begin: g_rdc_ex3_stubs
        assign active_rdc_ex3 = 1'b0;
        assign valid_rdc_ex3  = 1'b0;
    end endgenerate
    //-----------------------------------------------
    //RDC:EX4
    //-----------------------------------------------
    generate if (VECTOR_LANES > 8 & VECTOR_LANE_NUM[3:0] == 4'b0000) begin: g_rdc_ex4
        always_ff @(posedge clk or negedge rst_n) begin
            if(~rst_n) begin
                active_rdc_ex4 <= 0;
            end else begin
                active_rdc_ex4 <= active_rdc_ex3;
                vl_ex4         <= vl_ex3;
            end
        end
        // EX4 outputs
        assign valid_rdc_ex4  = active_rdc_ex4 & (
                                (vl_ex4 <= 'd16)  |
                                (vl_ex4 > 'd16 & VECTOR_LANES == 16)) ;

        always_comb begin
            case (rdc_op_ex4)
                `RDC_ADD : begin
                    // VRADD
                    tree_result_ex4 = data_ex4_i[0 +: DATA_WIDTH] + rdc_data_ex4_i;
                end
                `RDC_AND : begin
                    // VRAND
                    tree_result_ex4 = data_ex4_i[0 +: DATA_WIDTH] & rdc_data_ex4_i;
                end
                `RDC_OR : begin
                    // VROR
                    tree_result_ex4 = data_ex4_i[0 +: DATA_WIDTH] | rdc_data_ex4_i;
                end
                `RDC_XOR : begin
                    // VRXOR
                    tree_result_ex4 = data_ex4_i[0 +: DATA_WIDTH] ^ rdc_data_ex4_i;
                end
                default : begin
                    tree_result_ex4 = 'x;
                end
            endcase
        end
        assign result_rdc_ex4 = {{EX4_W-DATA_WIDTH{1'b0}},tree_result_ex4};

    end else begin: g_rdc_ex4_stubs
        assign active_rdc_ex4 = 1'b0;
    end endgenerate


    //================================================
    // Outputs
    //================================================

    // EX1 Out
    assign ready_res_ex1_o = valid_int_ex1  | valid_rdc_ex1;   //indicate ready result
    assign result_ex1_o    = active_rdc_ex1 ? result_rdc_ex1 :
                             ~mask_i        ? '0             :
                             valid_int_ex1  ? result_int_ex1 :
                             valid_mul_ex1  ? result_mul_ex1 :
                             valid_div_ex1  ? result_div_ex1 : 'x;
    // EX2 Out
    assign ready_res_ex2_o = valid_rdc_ex2;                   //indicate ready result
    assign result_ex2_o    = active_rdc_ex2 ? result_rdc_ex2 :
                             ~mask_ex2_i    ? '0             :
                             valid_mul_ex2  ? result_mul_ex2 :
                             valid_div_ex2  ? result_div_ex2 : 'x;
    // EX3 Out
    assign ready_res_ex3_o = valid_mul_ex3  | valid_rdc_ex3;   //indicate ready result
    assign result_ex3_o    = active_rdc_ex3 ? result_rdc_ex3 :
                             ~mask_ex3_i    ? '0             :
                             valid_mul_ex3  ? result_mul_ex3 :
                             valid_div_ex3  ? result_div_ex3 :'x;
    // EX4 Out
    assign rdc_op_ex4_o    = rdc_op_ex4;
    assign ready_res_ex4_o = valid_div_ex4  | valid_rdc_ex4;   //indicate ready result
    assign result_ex4_o    = active_rdc_ex4 ? result_rdc_ex4 :
                             ~mask_ex4_i    ? '0             : result_div_ex4;

endmodule // v_int_alu