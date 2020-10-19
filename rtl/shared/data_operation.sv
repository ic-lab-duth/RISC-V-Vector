/*
* @info Data Operation Sub-Module
*
* @author VLSI Lab, EE dept., Democritus University of Thrace
*
* @brief Used in the Data Cache, a provided microop picks the operation that will be used
*
* @param ADDR_W    : # of Address Bits
* @param DATA_W    : # of Data Bits
* @param MICROOP   : # of Microoperation Bits
* @param BLOCK_W   : # of Cache Block Bits
* @param LOAD_ONLY : Instatiates the block only with the load operations
*/
module data_operation #(
    parameter ADDR_W    = 5  ,
    parameter DATA_W    = 32 ,
    parameter MICROOP   = 5  ,
    parameter BLOCK_W   = 256,
    parameter LOAD_ONLY = 0
) (
    //Inputs
    input  logic [ ADDR_W-1:0] input_address,
    input  logic [BLOCK_W-1:0] input_block  ,
    input  logic [ DATA_W-1:0] input_data   ,
    input  logic [MICROOP-1:0] microop      ,
    //Outputs
    output logic               valid_exc    ,
    output logic [        3:0] exception    ,
    output logic [BLOCK_W-1:0] output_block ,
    output logic [ DATA_W-1:0] output_vector
);	 

    // #Internal Signals#
    logic [  DATA_W-1:0] data_loaded_32;
    logic [DATA_W/2-1:0] data_loaded_16;
    logic [DATA_W/4-1:0] data_loaded_8 ;
    logic [  ADDR_W+3:0] selector      ;
    
    generate
        //Used for Load Instructions Only
        if(LOAD_ONLY) begin
            assign selector       = 0;
            assign data_loaded_32 = input_block[selector +: DATA_W];
            assign data_loaded_16 = input_block[selector +: DATA_W/2];
            assign data_loaded_8  = input_block[selector +: DATA_W/4];
            always_comb begin : OutputVector
                case (microop)
                    5'b00001: begin
                        //LW/FLW/C.LWSP/C.FLWSP/C.LW/C.FLW
                        valid_exc = 0;
                        exception = 0;
                        output_vector = data_loaded_32;
                    end
                    5'b00010: begin
                        //LH
                        valid_exc = 0;
                        exception = 0;
                        output_vector = {{16{data_loaded_16[15]}},data_loaded_16};
                    end
                    5'b00011: begin
                        //LHU
                        valid_exc = 0;
                        exception = 0;
                        output_vector = {16'b0,data_loaded_16};
                    end
                    5'b00100: begin
                        //LB
                        valid_exc = 0;
                        exception = 0;
                        output_vector = {{24{data_loaded_8[7]}},data_loaded_8};
                    end
                    5'b00101: begin
                        //LBU
                        valid_exc = 0;
                        exception = 0;
                        output_vector = {24'b0,data_loaded_8};
                    end
                    default : begin
                        valid_exc = 1;
                        exception = 2;
                        output_vector = input_data;
                    end
                endcase
            end
            assign output_block = input_block;
        end else begin
            //Used for both Load/Store Instructions
            assign selector       = input_address << 3;
            assign data_loaded_32 = input_block[selector +: DATA_W];
            assign data_loaded_16 = input_block[selector +: DATA_W/2];
            assign data_loaded_8  = input_block[selector +: DATA_W/4];
            //Create the new load/store vector with the modified data
            always_comb begin : OutputVector
                case (microop)
                    5'b00001: begin
                        //LW/FLW/C.LWSP/C.FLWSP/C.LW/C.FLW
                        valid_exc = 0;
                        exception = 0;
                        output_vector = data_loaded_32;
                    end
                    5'b00010: begin
                        //LH
                        valid_exc = 0;
                        exception = 0;
                        output_vector = {{16{data_loaded_16[15]}},data_loaded_16};
                    end
                    5'b00011: begin
                        //LHU
                        valid_exc = 0;
                        exception = 0;
                        output_vector = {16'b0,data_loaded_16};
                    end
                    5'b00100: begin
                        //LB
                        valid_exc = 0;
                        exception = 0;
                        output_vector = {{24{data_loaded_8[7]}},data_loaded_8};
                    end
                    5'b00101: begin
                        //LBU
                        valid_exc = 0;
                        exception = 0;
                        output_vector = {24'b0,data_loaded_8};
                    end
                    5'b00110: begin
                        //SW/FSW/C.SWSP/C.FSWSP/C.SW/C.FSW
                        valid_exc = 0;
                        exception = 0;
                        output_vector = input_data;
                    end
                    5'b00111: begin
                        //SH
                        valid_exc = 0;
                        exception = 0;
                        output_vector = {data_loaded_32[DATA_W-1:16],input_data[15:0]};
                    end
                    5'b01000: begin
                        //SB
                        valid_exc = 0;
                        exception = 0;
                        output_vector = {data_loaded_32[DATA_W-1:8],input_data[7:0]};
                    end
                    //FLOATING POINT CURRENTLY DISABLED
                    /*
                    5'b01001: begin
                        //FCVT.S.W
                        valid_exc = 0;
                        exception = 0;
                    end
                    5'b01010: begin
                        //FCVT.S.WU
                        valid_exc = 0;
                        exception = 0;
                    end
                    5'b01011: begin
                        //FCVT.W.S
                        valid_exc = 0;
                        exception = 0;
                    end
                    5'b01100: begin
                        //FCVT.WU.S
                        valid_exc = 0;
                        exception = 0;
                    end
                    */
                    default : begin
                        valid_exc = 1;
                        exception = 2;
                        output_vector = input_data;
                    end
                endcase
            end

            //Create the new modified Block to be stored
            always_comb begin : OutputBlock
                output_block = input_block;
                output_block[selector +: DATA_W] = output_vector;
            end
        end        
    endgenerate
    
endmodule
