//=======================================================
// X Checks
//=======================================================
assert property (@(posedge clk) disable iff(!rst_n) ~$isunknown(valid_in))
    else $error("x-check:vmu_ld_eng: valid_in");

assert property (@(posedge clk) disable iff(!rst_n) ~$isunknown(wrtbck_en_o))
    else $error("x-check:vmu_ld_eng: wrtbck_en_o");

assert property (@(posedge clk) disable iff(!rst_n) ~$isunknown(grant_i))
    else $error("x-check:vmu_ld_eng: grant_i");

assert property (@(posedge clk) disable iff(!rst_n) ~$isunknown(wrtbck_req_o))
    else $error("x-check:vmu_ld_eng: wrtbck_req_o");

assert property (@(posedge clk) disable iff(!rst_n) ~$isunknown(wrtbck_grant_i))
    else $error("x-check:vmu_ld_eng: wrtbck_grant_i");

assert property (@(posedge clk) disable iff(!rst_n) ~$isunknown(resp_valid_i))
    else $error("x-check:vmu_ld_eng: resp_valid_i");

assert property (@(posedge clk) disable iff(!rst_n) ~$isunknown(unlock_en_o))
    else $error("x-check:vmu_ld_eng: unlock_en_o");

//=======================================================
// Properties
//=======================================================
logic flag_illegal;
always_comb begin
    flag_illegal = 0;
    for (int i = 0; i < VECTOR_LANES; i++) begin
        if(pending_elem[0][i] && !active_elem[0][i]) flag_illegal = 1;
        if(pending_elem[1][i] && !active_elem[1][i]) flag_illegal = 1;
    end
end

assert property (@(posedge clk) disable iff(!rst_n) DATA_WIDTH == 32)
    else $error("vmu_ld_eng: Designed only for 32bit data width");

assert property (@(posedge clk) disable iff(!rst_n) valid_in |-> nxt_memory_op inside {0, 2, 3})
    else $error("vmu_ld_eng: Illegal memory op");

assert property (@(posedge clk) disable iff(!rst_n) valid_in |-> nxt_size inside {0, 1, 2})
    else $error("vmu_ld_eng: Illegal memory size");

assert property (@(posedge clk) disable iff(!rst_n) !flag_illegal)
    else $error("vmu_ld_eng: Illegal state in the tracking");