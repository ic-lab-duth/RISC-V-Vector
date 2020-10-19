/*
* @info Data Operation Sub-Module
*
* @author VLSI Lab, EE dept., Democritus University of Thrace
*
* @brief Used in the Data Cache, a provided microop picks the operation that will be used
*
* @param ADDR_W    : # of Address Bits
* @param DATA_W    : # of Data Bits
* @param MICROOP_W : # of Microoperation Bits
* @param BLOCK_W   : # of Cache Block Bits
* @param LOAD_ONLY : Instatiates the block only with the load operations
*/
module vdata_operation #(
    parameter ADDR_W    = 5  ,
    parameter DATA_W    = 256,
    parameter MICROOP_W = 7  ,
    parameter SIZE_W    = 6  ,
    parameter BLOCK_W   = 256
) (
    input  logic                 clk          ,
    input  logic                 valid_i      ,
    //Inputs
    input  logic [   ADDR_W-1:0] input_address,
    input  logic [2*BLOCK_W-1:0] input_block  ,
    input  logic [   DATA_W-1:0] input_data   ,
    input  logic [MICROOP_W-1:0] microop      ,
    input  logic [   SIZE_W-1:0] size         ,
    //Outputs
    output logic                 valid_exc    ,
    output logic [          3:0] exception    ,
    output logic [2*BLOCK_W-1:0] output_block ,
    output logic [   DATA_W-1:0] output_vector
);

    // #Internal Signals#
    logic [   ADDR_W+3:0] offset_ammount  ;
    logic [   SIZE_W+2:0] size_in_bits    ;
    logic [2*BLOCK_W-1:0] shifted_data    ;
    logic [   DATA_W-1:0] load_output_mask;
    logic [2*BLOCK_W-1:0] lower_mask      ;
    logic [2*BLOCK_W-1:0] upper_mask      ;
    logic [2*BLOCK_W-1:0] store_mask      ;
    logic [2*BLOCK_W-1:0] new_data        ;
    logic [2*BLOCK_W-1:0] new_block       ;

    assign valid_exc = 1'b0;
    assign exception = '0;
    //=======================================================
    // Mask for output data (LOADS)
    //=======================================================
    // Shift the input block to align the data to position 0
    assign offset_ammount = input_address << 3;
    assign shifted_data   = input_block >> offset_ammount;

    // Convert the size to number of bits
    assign size_in_bits  = size << 3; //convert bytes to bits

    // Mask for output data (LOADS)
    assign load_output_mask = ~('1 << size_in_bits);
    assign output_vector    = load_output_mask & shifted_data[DATA_W-1:0];


    //=======================================================
    // Mask for new memory block (STORES)
    //=======================================================
    assign lower_mask   = ~('1 << offset_ammount);
    assign upper_mask   = lower_mask << size_in_bits;
    assign store_mask   = upper_mask & lower_mask;
    // shift the data to the correct position inside the block
    assign new_data     = (input_data << offset_ammount) & store_mask;
    // zero-out the old data inside the input block
    assign new_block    = input_block & (~store_mask);
    // merge the old block with the new data
    assign output_block = new_block | new_data;


    //=======================================================
    // Maximum supported transaction size is equal/smaller than the configured cache line
    assert property (@(posedge clk) valid_i |-> (size_in_bits <= BLOCK_W)) else $warning("FATAL:vdata_operation: unsupported configuration");
    assert property (@(posedge clk) valid_i |-> ~$isunknown(|output_vector)) else $error("x-check:vdata_operation: output_vector");

endmodule
