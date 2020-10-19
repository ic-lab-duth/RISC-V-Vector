//=======================================================
// X Checks
//=======================================================
assert property (@(posedge clk) disable iff(!rst_n) ~$isunknown(valid_in))
    else $error("x-check:vrrm: valid_in");

assert property (@(posedge clk) disable iff(!rst_n) ~$isunknown(pop_instr))
    else $error("x-check:vrrm: pop_instr");

assert property (@(posedge clk) disable iff(!rst_n) ~$isunknown(valid_o))
    else $error("x-check:vrrm: valid_o");

assert property (@(posedge clk) disable iff(!rst_n) ~$isunknown(ready_i))
    else $error("x-check:vrrm: ready_i");

assert property (@(posedge clk) disable iff(!rst_n) ~$isunknown(m_valid_o))
    else $error("x-check:vrrm: m_valid_o");

assert property (@(posedge clk) disable iff(!rst_n) ~$isunknown(m_ready_i))
    else $error("x-check:vrrm: m_ready_i");

assert property (@(posedge clk) disable iff(!rst_n) ~$isunknown(do_remap))
    else $error("x-check:vrrm: do_remap");

assert property (@(posedge clk) disable iff(!rst_n) ~$isunknown(do_operation))
    else $error("x-check:vrrm: do_operation");

assert property (@(posedge clk) disable iff(!rst_n) ~$isunknown(do_reconfigure))
    else $error("x-check:vrrm: do_reconfigure");

assert property (@(posedge clk) disable iff(!rst_n | ~valid_in) ~$isunknown(memory_instr))
    else $error("x-check:vrrm: memory_instr");
//=======================================================
// Properties
//=======================================================
//In the future, an exception could be used to capture this violation. For now assume illegal
assert property (@(posedge clk) disable iff(~rst_n) do_remap |-> (current_remaps < max_remaps))
    else $fatal("Did more remaps than the Max allowed. Use less rdsts or reconfigure");