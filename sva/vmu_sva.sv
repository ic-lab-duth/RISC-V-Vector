//=======================================================
// X Checks
//=======================================================
assert property (@(posedge clk) disable iff(!rst_n) ~$isunknown(valid_in))
    else $fatal("x-check:vmu: valid_in");

assert property (@(posedge clk) disable iff(!rst_n) ~$isunknown(cache_ready_i))
    else $fatal("x-check:vmu: cache_ready_i");

assert property (@(posedge clk) disable iff(!rst_n) ~$isunknown(mem_resp_valid_i))
    else $fatal("x-check:vmu: mem_resp_valid_i");

assert property (@(posedge clk) disable iff(!rst_n) ~$isunknown(wrtbck_en_o))
    else $fatal("x-check:vmu: wrtbck_en_o");

assert property (@(posedge clk) disable iff(!rst_n) wrtbck_en_o |-> ~$isunknown(wrtbck_reg_o))
    else $fatal("x-check:vmu: wrtbck_reg_o");

assert property (@(posedge clk) disable iff(!rst_n) wrtbck_en_o |-> ~$isunknown(wrtbck_data_o))
    else $fatal("x-check:vmu: wrtbck_data_o");

assert property (@(posedge clk) disable iff(!rst_n) wrtbck_en_o |-> ~$isunknown(wrtbck_ticket_o))
    else $fatal("x-check:vmu: wrtbck_ticket_o");

assert property (@(posedge clk) disable iff(!rst_n) ~$isunknown(unlock_en_o))
    else $fatal("x-check:vmu: unlock_en_o");

assert property (@(posedge clk) disable iff(!rst_n) unlock_en_o |-> ~$isunknown(unlock_reg_a_o))
    else $fatal("x-check:vmu: unlock_reg_a_o");

assert property (@(posedge clk) disable iff(!rst_n) unlock_en_o |-> ~$isunknown(unlock_reg_b_o))
    else $fatal("x-check:vmu: unlock_reg_b_o");

assert property (@(posedge clk) disable iff(!rst_n) unlock_en_o |-> ~$isunknown(unlock_ticket_o))
    else $fatal("x-check:vmu: unlock_ticket_o");

assert property (@(posedge clk) disable iff(!rst_n) ~$isunknown(push_load))
    else $fatal("x-check:vmu: push_load");

assert property (@(posedge clk) disable iff(!rst_n) ~$isunknown(push_store))
    else $fatal("x-check:vmu: push_store");

assert property (@(posedge clk) disable iff(!rst_n) ~$isunknown(push_toepl))
    else $fatal("x-check:vmu: push_store");

assert property (@(posedge clk) disable iff(!rst_n) ~$isunknown(any_grant))
    else $fatal("x-check:vmu: any_grant");

assert property (@(posedge clk) disable iff(!rst_n) ~$isunknown(ready_o))
    else $fatal("x-check:vmu: ready_o");


// generate if (ADVANCED_ARBITR) begin
//     assert property (@(posedge clk) disable iff(!rst_n) ~$isunknown(|active))
//     else $fatal("x-check:vmu: active");

//     assert property (@(posedge clk) disable iff(!rst_n) ~$isunknown(|tail))
//     else $fatal("x-check:vmu: tail");

//     assert property (@(posedge clk) disable iff(!rst_n) ~$isunknown(|activity_array))
//         else $fatal("x-check:vmu: activity_array");
// end endgenerate
//=======================================================
// Properties
//=======================================================
assert property (@(posedge clk) disable iff(!rst_n) !(load_unlock_en & store_unlock_en))
    else $fatal("vmu: unsupported scenario yet");

// assert property (@(posedge clk) disable iff(!rst_n) any_request & cache_ready_i |-> any_grant)
//     else $fatal("vmu: no memory grant was given");

assert property (@(posedge clk) disable iff(!rst_n) |wb_request |-> |wb_grant)
    else $fatal("vmu: no writeback grant was given");

assert property (@(posedge clk) disable iff(!rst_n) !fifo_ready |-> !ready_o)
    else $fatal("vmu: no new instr can be processed when activity matrix is full");

// generate if (ADVANCED_ARBITR) begin
//     assert property (@(posedge clk) disable iff(!rst_n) tail == 0 |=> ~&tail)
//         else $fatal("vmu: tail can not underflow");
// end endgenerate