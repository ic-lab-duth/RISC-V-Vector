//=======================================================
// X Checks
//=======================================================
assert property (@(posedge clk) disable iff(!rst_n) ~$isunknown(valid_in))
    else $error("x-check:vmu_st_eng: valid_in");

assert property (@(posedge clk) disable iff(!rst_n) ~$isunknown(unlock_en_o))
    else $error("x-check:vmu_st_eng: unlock_en_o");

assert property (@(posedge clk) disable iff(!rst_n) ~$isunknown(grant_i))
    else $error("x-check:vmu_st_eng: grant_i");
//=======================================================
// Properties
//=======================================================
assert property (@(posedge clk) disable iff(!rst_n) DATA_WIDTH == 32)
    else $error("vmu_st_eng: Designed only for 32bit data width");

assert property (@(posedge clk) disable iff(!rst_n) valid_in |-> nxt_memory_op inside {0, 2, 3})
    else $error("vmu_st_eng: Illegal memory op");

assert property (@(posedge clk) disable iff(!rst_n) valid_in |-> nxt_size inside {0, 1, 2})
    else $error("vmu_st_eng: Illegal memory size");