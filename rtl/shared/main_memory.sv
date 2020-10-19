/*
* @info Main Memory Controller
*
* @author VLSI Lab, EE dept., Democritus University of Thrace
*
* @param L2_BLOCK_DW    : # of L2 Cache Block Bits (default 512 bits)
* @param L2_ENTRIES     : # of L2 Entries (default 512 entries)
* @param ADDRESS_BITS   : # of Address Bits (default 32 bits)
* @param ICACHE_BLOCK_DW: # of ICache Block Bits (default 256 bits)
* @param DCACHE_BLOCK_DW: # of DCache Block Bits (default 256 bits)
* @param FILE_NAME      : File Name containing the memory contents
*/
typedef struct packed {
    logic           read_icache ;
    logic           read_dcache ;
    logic           write_dcache;
    logic [ 32-1:0] address     ;
    logic [256-1:0] data        ;
} SavedEntry;
//DEFAULT: 512 blocks * 512 bits/block = 32KB Cache size
module main_memory #(
    parameter L2_BLOCK_DW     = 128 ,
    parameter L2_ENTRIES      = 2048,
    parameter ADDRESS_BITS    = 32  ,
    parameter ICACHE_BLOCK_DW = 256 ,
    parameter DCACHE_BLOCK_DW = 256 ,
    parameter REALISTIC       = 1   ,
    parameter DELAY_CYCLES    = 50  ,
    parameter FILE_NAME       = "memory.txt"
) (
    input  logic                       clk              ,
    input  logic                       rst_n            ,
    //Read Request Input from ICache
    input  logic                       icache_valid_i   ,
    input  logic [               31:0] icache_address_i ,
    //Read Request Input from DCache
    input  logic                       dcache_valid_i   ,
    input  logic [               31:0] dcache_address_i ,
    //Write Request Input from DCache
    input  logic                       dcache_valid_wr  ,
    input  logic [               31:0] dcache_address_wr,
    input  logic [DCACHE_BLOCK_DW-1:0] dcache_data_wr   ,
    //Output to ICache
    output logic                       icache_valid_o   ,
    output logic [ICACHE_BLOCK_DW-1:0] icache_data_o    ,
    //Output to DCache
    output logic                       dcache_valid_o   ,
    output logic [               31:0] dcache_address_o ,
    output logic [DCACHE_BLOCK_DW-1:0] dcache_data_o
);
//-------------------------------------------------------------------------------------
    localparam OFFSET_BITS   = $clog2(L2_BLOCK_DW/8);
    localparam INDEX_BITS    = $clog2(L2_ENTRIES);
    localparam TAG_BITS      = ADDRESS_BITS-OFFSET_BITS-INDEX_BITS;
    localparam DBLOCK_OFFSET = $clog2(L2_BLOCK_DW/DCACHE_BLOCK_DW);
    localparam IBLOCK_OFFSET = $clog2(L2_BLOCK_DW/ICACHE_BLOCK_DW);
    // #Internal Signals#
    logic      [    L2_BLOCK_DW-1:0] ram               [L2_ENTRIES-1:0];
    logic      [ICACHE_BLOCK_DW-1:0] data_picked_icache                ;
    logic      [DCACHE_BLOCK_DW-1:0] data_picked_dcache                ;
    SavedEntry                       input_entry_1, input_entry_2, output_entry;
    logic                            push_1, push_2, ready_1, ready_2, valid, pop, counter_active;
    logic      [   DELAY_CYCLES-1:0] delay_counter                     ;
    logic      [     INDEX_BITS-1:0] line_selector                     ;
    logic      [  DBLOCK_OFFSET-1:0] dblock_offset                     ;
    logic      [  IBLOCK_OFFSET-1:0] iblock_offset                     ;
    logic      [    L2_BLOCK_DW-1:0] block_selected, starting_bit_ic, starting_bit_dc;
    logic                            delayed_valid                     ;
    initial begin
        //Open the File
        $readmemh(FILE_NAME,ram);
        $display("first inst: %h",ram[0][31:0]);
        $display("sec inst: %h",ram[0][63:32]);
    end
    //Create the New Inputs
    assign input_entry_1.data = dcache_data_wr;
    assign input_entry_2.data = dcache_data_wr;
    always_comb begin : CreateNewEntries
        if(icache_valid_i) begin
            push_1 = 1;
            input_entry_1.read_icache = 1;
            input_entry_1.read_dcache = 0;
            input_entry_1.write_dcache = 0;
            input_entry_1.address = icache_address_i;
            if(dcache_valid_i) begin
                push_2 = 1;
                input_entry_2.read_icache = 0;
                input_entry_2.read_dcache = 1;
                input_entry_2.write_dcache = 0;
                input_entry_2.address = dcache_address_i;
            end else if(dcache_valid_wr) begin
                push_2 = 1;
                input_entry_2.read_icache = 0;
                input_entry_2.read_dcache = 0;
                input_entry_2.write_dcache = 1;
                input_entry_2.address = dcache_address_wr;
            end else begin
                push_2 = 0;
                input_entry_2.read_icache = 0;
                input_entry_2.read_dcache = 0;
                input_entry_2.write_dcache = 0;
                input_entry_2.address = dcache_address_wr;
            end
        end else begin
            //No ICache Request
            push_2 = 0;
            input_entry_2.read_icache = 0;
            input_entry_2.read_dcache = 0;
            input_entry_2.write_dcache = 0;
            input_entry_2.address = dcache_address_wr;
            if(dcache_valid_i) begin
                push_1 = 1;
                input_entry_1.read_icache = 0;
                input_entry_1.read_dcache = 1;
                input_entry_1.write_dcache = 0;
                input_entry_1.address = dcache_address_i;
            end else if(dcache_valid_wr) begin
                push_1 = 1;
                input_entry_1.read_icache = 0;
                input_entry_1.read_dcache = 0;
                input_entry_1.write_dcache = 1;
                input_entry_1.address = dcache_address_wr;
            end else begin
                push_1 = 0;
                input_entry_1.read_icache = 0;
                input_entry_1.read_dcache = 0;
                input_entry_1.write_dcache = 0;
                input_entry_1.address = dcache_address_wr;
            end
        end
    end
    //FiFo to store the Requests
    fifo_dual_ported #(
        .DW         ($bits(input_entry_1)),
        .DEPTH      (8)
        )
    instruction_queue  (
        .clk            (clk),
        .rst            (~rst_n),

        .valid_flush    (1'b0),             //No Flush Functionality            

        .push_1         (push_1),
        .ready_1        (ready_1),
        .push_data_1    (input_entry_1),
 
        .push_2         (push_2),
        .ready_2        (ready_2),
        .push_data_2    (input_entry_2),

        .pop_data_1     (output_entry),
        .valid_1        (valid),
        .pop_1          (pop),

        .pop_data_2     (),             //NC         
        .valid_2        (),             //NC
        .pop_2          (1'b0)          //Single Serve each Cycle
    );
    //Input Some Delay to immitate a more realistic L2
    always_ff @(posedge clk or negedge rst_n) begin : delay
        if(!rst_n) begin
            delay_counter  <= 1;
            counter_active <= 1'b0;
        end else begin
            case (counter_active)
                1'b1 : if(~|delay_counter) begin
                    counter_active <= 1'b0;
                end else begin
                    delay_counter <= delay_counter << 1;
                end
                1'b0 : if(valid) begin
                    counter_active <= 1'b1;
                    delay_counter  <= 1;
                end
            endcase
        end
    end
    //Choose Memory Model (perfect <> 50 cycles access delay)
    generate
        if(REALISTIC) begin
            assign delayed_valid = counter_active & ~|delay_counter;
        end else begin
            assign delayed_valid = valid;
        end
    endgenerate
    //Create the Output Signals
    assign pop              = delayed_valid;
    assign icache_valid_o   = delayed_valid & output_entry.read_icache;
    assign icache_data_o    = data_picked_icache;
    assign dcache_valid_o   = delayed_valid & output_entry.read_dcache;
    assign dcache_address_o = output_entry.address;
    assign dcache_data_o    = data_picked_dcache;

    assign line_selector    = output_entry.address[OFFSET_BITS+INDEX_BITS-1 : OFFSET_BITS];
    assign block_selected   = ram[line_selector];

    assign iblock_offset      = output_entry.address[OFFSET_BITS-1:OFFSET_BITS-IBLOCK_OFFSET];
    assign dblock_offset      = output_entry.address[OFFSET_BITS-1:OFFSET_BITS-DBLOCK_OFFSET];
    assign starting_bit_ic    = iblock_offset << $clog2(ICACHE_BLOCK_DW);
    assign starting_bit_dc    = dblock_offset << $clog2(DCACHE_BLOCK_DW);
    assign data_picked_icache = block_selected[starting_bit_ic +: ICACHE_BLOCK_DW];
    assign data_picked_dcache = block_selected[starting_bit_dc +: DCACHE_BLOCK_DW];

    always_ff @(posedge clk) begin : RamManagement
        if(delayed_valid & output_entry.write_dcache) begin
            ram[line_selector][starting_bit_dc +: DCACHE_BLOCK_DW] <= output_entry.data;
        end
    end

endmodule