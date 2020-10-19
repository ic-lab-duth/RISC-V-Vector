`include "vstructs.sv"
module vector_driver #(
    parameter int DEPTH            = 4 ,
    parameter int DATA_WIDTH       = 32,
    parameter int VECTOR_REGISTERS = 32,
    parameter int VECTOR_LANES     = 8 ,
    parameter int MICROOP_WIDTH    = 32
) (
    input  logic     clk    ,
    input  logic     rst_n  ,
    // input side
    output logic     valid_o,
    output to_vector instr_o,
    input  logic     pop_i
);

    logic [$clog2(DEPTH+1)-1:0] head;
    // Memory Initialized with the generator outputs
    logic                                reconfiguration_list[DEPTH-1:0];
    logic [              DATA_WIDTH-1:0] data1_list          [DEPTH-1:0];
    logic [              DATA_WIDTH-1:0] data2_list          [DEPTH-1:0];
    logic [              DATA_WIDTH-1:0] immediate_list      [DEPTH-1:0];
    logic [$clog2(VECTOR_REGISTERS)-1:0] destination_list    [DEPTH-1:0];
    logic [$clog2(VECTOR_REGISTERS)-1:0] operand_a_list      [DEPTH-1:0];
    logic [$clog2(VECTOR_REGISTERS)-1:0] operand_b_list      [DEPTH-1:0];
    logic [$clog2(VECTOR_REGISTERS)-1:0] operand_c_list      [DEPTH-1:0];
    logic [           MICROOP_WIDTH-1:0] microop_list        [DEPTH-1:0];
    logic [                         1:0] fu_list             [DEPTH-1:0];
    logic [                      32-1:0] maxvl_list          [DEPTH-1:0];
    logic [                      32-1:0] vl_list             [DEPTH-1:0];

    // Load the Memories
    initial begin
        $readmemb("../vector_simulator/decoder_results/instrs/data1_output.txt",data1_list);
        $readmemb("../vector_simulator/decoder_results/instrs/data2_output.txt",data2_list);
        $readmemb("../vector_simulator/decoder_results/instrs/immediate_output.txt",immediate_list);
        $readmemb("../vector_simulator/decoder_results/instrs/destination_output.txt",destination_list);
        $readmemb("../vector_simulator/decoder_results/instrs/operand_a_output.txt",operand_a_list);
        $readmemb("../vector_simulator/decoder_results/instrs/operand_b_output.txt",operand_b_list);
        $readmemb("../vector_simulator/decoder_results/instrs/operand_c_output.txt",operand_c_list);
        $readmemb("../vector_simulator/decoder_results/instrs/microop_output.txt",microop_list);
        $readmemb("../vector_simulator/decoder_results/instrs/fu_output.txt",fu_list);
        $readmemb("../vector_simulator/decoder_results/instrs/reconfigure_output.txt",reconfiguration_list);
        $readmemb("../vector_simulator/decoder_results/instrs/maxvl_output.txt",maxvl_list);
        $readmemb("../vector_simulator/decoder_results/instrs/vl_output.txt",vl_list);
    end

    logic instr_is_dummy;
    // A dummy instruction is a NOP that will be poped from the list but not issued
    // Used to emulate cycles where the scalar core decodes scalar instructions (e.g. control instrs)
    assign instr_is_dummy = reconfiguration_list[head] & &fu_list[head] & microop_list[head] & ~|vl_list[head] & ~|maxvl_list[head];

    // Manage the list head pointer
    always_ff @(posedge clk or negedge rst_n) begin
        if(~rst_n) begin
            head <= 0;
        end else begin
            if (pop_i | instr_is_dummy) head <= head +1;
        end
    end

    // Create the Outputs
    assign valid_o = (head < DEPTH) & rst_n & ~instr_is_dummy;

    assign instr_o.valid       = valid_o;
    assign instr_o.dst         = destination_list[head];
    assign instr_o.src1        = operand_a_list[head];
    assign instr_o.src2        = operand_b_list[head];
    assign instr_o.data1       = data1_list[head];
    assign instr_o.data2       = data2_list[head];
    assign instr_o.reconfigure = reconfiguration_list[head];
    assign instr_o.immediate   = immediate_list[head];
    assign instr_o.fu          = fu_list[head];
    assign instr_o.microop     = microop_list[head];
    assign instr_o.maxvl       = maxvl_list[head][$clog2(VECTOR_REGISTERS*VECTOR_LANES):0];
    assign instr_o.vl          = vl_list[head][$clog2(VECTOR_REGISTERS*VECTOR_LANES):0];
    assign instr_o.use_mask    = '0;

endmodule
