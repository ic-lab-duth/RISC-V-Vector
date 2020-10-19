//=======================================================
// X Checks
//=======================================================
assert property (@(posedge clk) disable iff(!rst_n) ~$isunknown(valid_in))
    else $error("x-check:vis: valid_in");

assert property (@(posedge clk) disable iff(!rst_n) ~$isunknown(ready_o))
    else $error("x-check:vis: ready_o");

assert property (@(posedge clk) disable iff(!rst_n) ~$isunknown(valid_o))
    else $error("x-check:vis: valid_o");

assert property (@(posedge clk) disable iff(!rst_n) ~$isunknown(ready_i))
    else $error("x-check:vis: ready_i");

assert property (@(posedge clk) disable iff(!rst_n) ~$isunknown(|mem_wr_en))
    else $error("x-check:vis: mem_wr_en");

assert property (@(posedge clk) disable iff(!rst_n) ~$isunknown(unlock_en))
    else $error("x-check:vis: unlock_en");

assert property (@(posedge clk) disable iff(!rst_n) ~$isunknown(|frw_a_en))
    else $error("x-check:vis: frw_a_en");

assert property (@(posedge clk) disable iff(!rst_n) ~$isunknown(|frw_b_en))
    else $error("x-check:vis: frw_b_en");

assert property (@(posedge clk) disable iff(!rst_n) ~$isunknown(|wr_en))
    else $error("x-check:vis: wr_en");

assert property (@(posedge clk) disable iff(!rst_n) valid_in |-> ~$isunknown(memory_instr))
    else $error("x-check:vis: memory_instr");

assert property (@(posedge clk) disable iff(!rst_n) ~$isunknown(do_reconfigure))
    else $error("x-check:vis: do_reconfigure");

assert property (@(posedge clk) disable iff(!rst_n) ~$isunknown(pop))
    else $error("x-check:vis: pop");

assert property (@(posedge clk) disable iff(!rst_n) ~$isunknown(do_issue))
    else $error("x-check:vis: do_issue");

assert property (@(posedge clk) disable iff(!rst_n) ~$isunknown(|wr_en_masked))
    else $error("x-check:vis: wr_en_masked");

assert property (@(posedge clk) disable iff(!rst_n) ~$isunknown(|mem_wr_en))
    else $error("x-check:vis: mem_wr_en");

assert property (@(posedge clk) disable iff(!rst_n) ~$isunknown(|pending))
    else $error("x-check:vis: pending");

assert property (@(posedge clk) disable iff(!rst_n) ~$isunknown(|locked))
    else $error("x-check:vis: locked");

assert property (@(posedge clk) disable iff(!rst_n) |wr_en |-> ~$isunknown(|wr_addr))
    else $error("x-check:vis: Address must not be X when a valid writeback is indicated");

assert property (@(posedge clk) disable iff(!rst_n) |wr_en |-> ~$isunknown(|wr_ticket))
    else $error("x-check:vis: Ticket must not be X when a valid writeback is indicated");

generate for (genvar k = 0; k < VECTOR_LANES; k++) begin: g_vis_sva_writeback
    assert property (@(posedge clk) disable iff(!rst_n) wr_en[k] |-> ~$isunknown(|wr_data[k]))
        else $error("x-check:vis: writeback data must not be X for active pipes");
end endgenerate

assert property (@(posedge clk) disable iff(!rst_n) |mem_wr_en |-> ~$isunknown(|mem_wr_addr))
    else $error("x-check:vis: Address must not be X when a valid memory writeback is indicated");

assert property (@(posedge clk) disable iff(!rst_n) |mem_wr_en |-> ~$isunknown(|mem_wr_ticket))
    else $error("x-check:vis: Ticket must not be X when a valid memory writeback is indicated");
//=======================================================
// Properties
//=======================================================
assert property (@(posedge clk) disable iff(!rst_n) valid_in & !ready_o |=> valid_in)
    else $error("Assertion:vis: valid_in must stay stable");

assert property (@(posedge clk) disable iff(!rst_n) valid_in & !ready_o |=> $stable(instr_in))
    else $error("Assertion:vis: input data must remain stable");

