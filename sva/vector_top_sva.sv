//=======================================================
// X Checks
//=======================================================
assert property (@(posedge clk) disable iff(!rst_n) ~$isunknown(valid_in))
    else $error("x-check:TOP: valid_in");

assert property (@(posedge clk) disable iff(!rst_n) valid_in |-> ~$isunknown(|instr_in))
    else $error("x-check:TOP: instr_in");

assert property (@(posedge clk) disable iff(!rst_n) ~$isunknown(pop))
    else $error("x-check:TOP: pop");
//=======================================================
// Properties
//=======================================================
assert property (@(posedge clk) disable iff(!rst_n) (valid_in & ~instr_in.reconfigure & instr_in.fu == `MEM_FU)  |->
    instr_in.microop inside {
                     7'b0000000,
                     7'b0000000,
                     7'b0000100,
                     7'b0001000,
                     7'b0100000,
                     7'b0100000,
                     7'b0100100,
                     7'b0101000,
                     7'b0110000,
                     7'b0110000,
                     7'b0110000,
                     7'b0110000,
                     7'b0110100,
                     7'b0110100,
                     7'b0111000,
                     7'b0111000,
                     7'b1000000,
                     7'b1000000,
                     7'b1000001,
                     7'b1000001,
                     7'b1000010,
                     7'b1000100,
                     7'b1000110,
                     7'b1001000,
                     7'b1001001,
                     7'b1001010,
                     7'b1010011,
                     7'b1100000,
                     7'b1100000,
                     7'b1100001,
                     7'b1100001,
                     7'b1100010,
                     7'b1100100,
                     7'b1100110,
                     7'b1101000,
                     7'b1101001,
                     7'b1101010,
                     7'b1110000,
                     7'b1110000,
                     7'b1110001,
                     7'b1110001,
                     7'b1110010,
                     7'b1110011,
                     7'b1110100,
                     7'b1110110,
                     7'b1111000,
                     7'b1111001,
                     7'b1111010
    }
) else $error("Assertion:TOP: invalid microop for MEM_FU");

// Only a sample of pseudo FPU instructions are present, mainly used for performance evaluations
assert property (@(posedge clk) disable iff(!rst_n) (valid_in & ~instr_in.reconfigure & instr_in.fu == `FP_FU)  |->
    instr_in.microop inside {7'b0000001, 7'b0000010, 7'b0000011}
) else $error("Assertion:TOP: invalid microop for FP_FU");

assert property (@(posedge clk) disable iff(!rst_n) (valid_in & ~instr_in.reconfigure & instr_in.fu == `INT_FU)  |->
    instr_in.microop inside {
                     7'b0000001,
                     7'b0000010,
                     7'b0000011,
                     7'b0000100,
                     7'b0000101,
                     7'b0000110,
                     7'b0000111,
                     7'b0001000,
                     7'b0001001,
                     7'b0001010,
                     7'b0001011,
                     7'b0001100,
                     7'b0001101,
                     7'b0001110,
                     7'b0001111,
                     7'b0010000,
                     7'b0010001,
                     7'b0010010,
                     7'b0010011,
                     7'b0010100,
                     7'b0010101,
                     7'b0010110,
                     7'b0010111,
                     7'b0011000,
                     7'b0011001,
                     7'b0011010,
                     7'b0011011,
                     7'b0011100,
                     7'b0011101,
                     7'b0011110,
                     7'b0100000,
                     7'b0100001,
                     7'b0100010,
                     7'b0100011,
                     7'b1000000,
                     7'b1000001,
                     7'b1000010,
                     7'b1000011
    }
) else $error("Assertion:TOP: invalid microop for INT_FU");

assert property (@(posedge clk) disable iff(!rst_n) valid_in |-> (instr_in.fu != `FXP_FU)
) else $error("Assertion:TOP: Fixed Point is current not supported");

assert property (@(posedge clk) disable iff(!rst_n) (valid_in & (instr_in.fu == `FXP_FU)) |-> (instr_in.microop != 7'b1111111)
) else $error("Assertion:TOP: Illegal encoding: This is used to denote a bubble cycle in the simulator, should not have reached the datapath");