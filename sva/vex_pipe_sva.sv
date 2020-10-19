//=======================================================
// X Checks
//=======================================================
assert property (@(posedge clk) disable iff(!rst_n) ~$isunknown(valid_i))
    else $error("x-check:vex_pipe: valid_i");
assert property (@(posedge clk) disable iff(!rst_n) valid_i |-> ~$isunknown(mask_i))
    else $error("x-check:vex_pipe: mask_i");
assert property (@(posedge clk) disable iff(!rst_n) valid_i |-> ~$isunknown(microop_i))
    else $error("x-check:vex_pipe: microop_i");
assert property (@(posedge clk) disable iff(!rst_n) valid_i |-> ~$isunknown(fu_i))
    else $error("x-check:vex_pipe: fu_i");
assert property (@(posedge clk) disable iff(!rst_n) ~$isunknown(frw_a_en_o))
    else $error("x-check:vex_pipe: frw_a_en_o");
assert property (@(posedge clk) disable iff(!rst_n) ~$isunknown(frw_b_en_o))
    else $error("x-check:vex_pipe: frw_b_en_o");
assert property (@(posedge clk) disable iff(!rst_n) ~$isunknown(wr_en_o))
    else $error("x-check:vex_pipe: wr_en_o");
//=======================================================
// Properties
//=======================================================
