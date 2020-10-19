//=======================================================
// X Checks
//=======================================================
assert property (@(posedge clk) disable iff(!rst_n) ~$isunknown(valid_in))
    else $fatal("x-check:vmu_tp_eng: valid_in");

assert property (@(posedge clk) disable iff(!rst_n) ~$isunknown(wrtbck_en_o))
    else $fatal("x-check:vmu_tp_eng: wrtbck_en_o");

assert property (@(posedge clk) disable iff(!rst_n) ~$isunknown(grant_i))
    else $fatal("x-check:vmu_tp_eng: grant_i");

assert property (@(posedge clk) disable iff(!rst_n) ~$isunknown(wrtbck_req_o))
    else $fatal("x-check:vmu_tp_eng: wrtbck_req_o");

assert property (@(posedge clk) disable iff(!rst_n) ~$isunknown(wrtbck_grant_i))
    else $fatal("x-check:vmu_tp_eng: wrtbck_grant_i");

assert property (@(posedge clk) disable iff(!rst_n) ~$isunknown(req_en_o))
    else $fatal("x-check:vmu_tp_eng: req_en_o");

assert property (@(posedge clk) disable iff(!rst_n) ~$isunknown(resp_valid_i))
    else $fatal("x-check:vmu_tp_eng: resp_valid_i");

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

assert property (@(posedge clk) disable iff(!rst_n) !flag_illegal)
    else $fatal("vmu_tp_eng: Illegal state in the tracking");

assert property (@(posedge clk) disable iff(!rst_n) DATA_WIDTH == 32)
    else $fatal("vmu_tp_eng: Designed only for 32bit data width");

assert property (@(posedge clk) disable iff(!rst_n) valid_in |-> nxt_size inside {0, 1, 2})
    else $fatal("vmu_tp_eng: Illegal memory size");

assert property (@(posedge clk) disable iff(!rst_n) new_transaction_en |-> (nxt_win_col_num <= kernel_size_r))
    else $fatal("vmu_tp_eng: Illegal Scenario");