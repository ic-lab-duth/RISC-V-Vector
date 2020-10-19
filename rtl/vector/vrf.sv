/*
* @info Vector Register File
*
* @author VLSI Lab, EE dept., Democritus University of Thrace
*
*/
module vrf #(
    parameter int VREGS      = 32,
    parameter int ELEMENTS   = 4 ,
    parameter int DATA_WIDTH = 32
) (
    input  logic                                           clk         ,
    input  logic                                           reset       ,
    //Element Read Ports
    input  logic [      $clog2(VREGS)-1:0]                 rd_addr_1   ,
    output logic [           ELEMENTS-1:0][DATA_WIDTH-1:0] data_out_1  ,
    input  logic [      $clog2(VREGS)-1:0]                 rd_addr_2   ,
    output logic [           ELEMENTS-1:0][DATA_WIDTH-1:0] data_out_2  ,
    input  logic [      $clog2(VREGS)-1:0]                 mask_src    ,
    output logic [           ELEMENTS-1:0]                 mask        ,
    //Element Write Ports
    input  logic [           ELEMENTS-1:0]                 el_wr_en    ,
    input  logic [      $clog2(VREGS)-1:0]                 el_wr_addr  ,
    input  logic [           ELEMENTS-1:0][DATA_WIDTH-1:0] el_wr_data  ,
    //Register Read Port
    input  logic [      $clog2(VREGS)-1:0]                 v_rd_addr_0 ,
    output logic [ELEMENTS*DATA_WIDTH-1:0]                 v_data_out_0,
    input  logic [      $clog2(VREGS)-1:0]                 v_rd_addr_1 ,
    output logic [ELEMENTS*DATA_WIDTH-1:0]                 v_data_out_1,
    input  logic [      $clog2(VREGS)-1:0]                 v_rd_addr_2 ,
    output logic [ELEMENTS*DATA_WIDTH-1:0]                 v_data_out_2,
    //Register Write Port
    input  logic [           ELEMENTS-1:0]                 v_wr_en     ,
    input  logic [      $clog2(VREGS)-1:0]                 v_wr_addr   ,
    input  logic [ELEMENTS*DATA_WIDTH-1:0]                 v_wr_data
);

    //Internal Signals
    logic [VREGS-1:0][ELEMENTS-1:0][DATA_WIDTH-1:0] memory      ;
    logic [VREGS-1:0]                               wr_addr_oh  ;
    logic [VREGS-1:0]                               v_wr_addr_oh;
    // Convert to one-hot
    assign v_wr_addr_oh = (1 << v_wr_addr);
    assign wr_addr_oh   = (1 << el_wr_addr);
    //Store new Data
    always_ff @(posedge clk) begin : memManage
        if(reset) begin
            for (int k = 0; k < ELEMENTS; k++) begin
                for (int i = 0; i < VREGS; i++) begin
                    memory[i][k] <= 'h0;
                end
            end
        end else begin
            for (int k = 0; k < ELEMENTS; k++) begin
                for (int i = 0; i < VREGS; i++) begin
                    if(v_wr_addr_oh[i] && v_wr_en[k]) begin
                        memory[i][k] <= v_wr_data[k*DATA_WIDTH +: DATA_WIDTH];
                    end else if(wr_addr_oh[i] && el_wr_en[k]) begin
                        memory[i][k] <= el_wr_data[k];
                    end
                end
            end
        end
    end
    // Pick the Data and push them to the Output
    assign v_data_out_0 = memory[v_rd_addr_0];
    assign v_data_out_1 = memory[v_rd_addr_1];
    assign v_data_out_2 = memory[v_rd_addr_2];
    always_comb begin : DataOut
        for (int i = 0; i < ELEMENTS; i++) begin
            data_out_1[i] = memory[rd_addr_1][i];
            data_out_2[i] = memory[rd_addr_2][i];
            mask[i]       = memory[mask_src][i][0];
        end
    end

endmodule