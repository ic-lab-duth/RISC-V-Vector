/*
* @info Vector Register Aliasing Table
*
* @author VLSI Lab, EE dept., Democritus University of Thrace
*
*/
module vrat #(
    parameter int TOTAL_ENTRIES = 32,
    parameter int DATA_WIDTH    = 4
) (
    input  logic                             clk        ,
    input  logic                             rst_n      ,
    input  logic                             reconfigure,
    //Write Port
    input  logic [$clog2(TOTAL_ENTRIES)-1:0] write_addr ,
    input  logic [           DATA_WIDTH-1:0] write_data ,
    input  logic                             write_en   ,
    //Read Port #1
    input  logic [$clog2(TOTAL_ENTRIES)-1:0] read_addr_1,
    output logic [           DATA_WIDTH-1:0] read_data_1,
    output logic                             remapped_1 ,
    //Read Port #2
    input  logic [$clog2(TOTAL_ENTRIES)-1:0] read_addr_2,
    output logic [           DATA_WIDTH-1:0] read_data_2,
    output logic                             remapped_2 ,
    //Read Port #3
    input  logic [$clog2(TOTAL_ENTRIES)-1:0] read_addr_3,
    output logic [           DATA_WIDTH-1:0] read_data_3,
    output logic                             remapped_3 ,
    //Mask Port
    output logic [           DATA_WIDTH-1:0] mask_src
);
    localparam ADDR_WIDTH = $clog2(TOTAL_ENTRIES);

    logic [TOTAL_ENTRIES-1:0][DATA_WIDTH-1 : 0] ratMem;
    logic [TOTAL_ENTRIES-1:0] remapped;

    //RAT memory storage
    always_ff @(posedge clk or negedge rst_n) begin : mem
        if(~rst_n) begin
            for (int i = 0; i < TOTAL_ENTRIES; i++) begin
                ratMem[i] <= i;
            end
        end else begin
            if (reconfigure) begin
                ratMem <= 'b0;
            end else if(write_en) begin
                ratMem[write_addr] <= write_data;
            end
        end
    end
    //Register Status Storage (remapped y/n)
    always_ff @(posedge clk or negedge rst_n) begin : remap
        if(~rst_n) begin
            remapped <= 'b1;
        end else begin
            if (reconfigure) begin
                remapped <= 'b0;
            end else if(write_en) begin
                remapped[write_addr] <= 1'b1;
            end
        end
    end
    //Push Data Out
    assign read_data_1 = ratMem[read_addr_1];
    assign remapped_1  = remapped[read_addr_1];
    assign read_data_2 = ratMem[read_addr_2];
    assign remapped_2  = remapped[read_addr_2];
    assign read_data_3 = ratMem[read_addr_3];
    assign remapped_3  = remapped[read_addr_3];

    assign mask_src   = ratMem['d1];


endmodule