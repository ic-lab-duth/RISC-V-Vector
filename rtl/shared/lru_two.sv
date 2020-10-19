/*
 * @info LRU Sub Module
 * @info Top-Module: lru.sv
 *
 * @author VLSI Lab, EE dept., Democritus University of Thrace
 *
 * @param ENTRIES      : The total addressable entries.
 * @param INDEX_BITS   : The address width
 */
module lru_two #(ENTRIES=256,INDEX_BITS=8) (
	input  logic                  clk           ,
	input  logic                  rst_n         ,
	//Read Port
	input  logic [INDEX_BITS-1:0] line_selector ,
	output logic                  lru_way       ,
	//Update Port
	input  logic                  lru_update    ,
	input  logic                  referenced_set
);
	// #Internal Signals#
 	logic [ENTRIES-1 : 0] Stored_Stats;

 	// Push the Output
	assign lru_way = Stored_Stats[line_selector];

	//Update the bookkeeping
	always_ff @(posedge clk or negedge rst_n) begin : Update
		if(!rst_n) begin
			Stored_Stats <= 'b0;
		end else begin
			if(lru_update) begin
				Stored_Stats[line_selector] <= ~referenced_set;
			end
		end
	end

endmodule