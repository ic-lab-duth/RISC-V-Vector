//=======================================================
// X Checks
//=======================================================
assert property (@(posedge clk) disable iff(!rst_n) ~$isunknown(valid_i))
    else $error("x-check:vex: valid_i");
assert property (@(posedge clk) disable iff(!rst_n) ~$isunknown(|frw_a_en))
    else $error("x-check:vex: frw_a_en");
assert property (@(posedge clk) disable iff(!rst_n) ~$isunknown(|frw_b_en))
    else $error("x-check:vex: frw_b_en");
assert property (@(posedge clk) disable iff(!rst_n) ~$isunknown(|wr_en))
    else $error("x-check:vex: wr_en");

generate
    for (genvar k = 0; k < VECTOR_LANES; k++) begin
        assert property (@(posedge clk) disable iff(!rst_n) frw_a_en[k] |-> ~$isunknown(|frw_a_addr))
            else $error("x-check:vex: frw_a_addr");
        assert property (@(posedge clk) disable iff(!rst_n) frw_a_en[k] |-> ~$isunknown(|frw_a_ticket))
            else $error("x-check:vex: frw_a_ticket");
        assert property (@(posedge clk) disable iff(!rst_n) frw_b_en[k] |-> ~$isunknown(|frw_b_addr))
            else $error("x-check:vex: frw_b_addr");
        assert property (@(posedge clk) disable iff(!rst_n) frw_b_en[k] |-> ~$isunknown(|frw_b_ticket))
            else $error("x-check:vex: frw_b_ticket");
        assert property (@(posedge clk) disable iff(!rst_n) wr_en[k] |-> ~$isunknown(|wr_addr))
            else $error("x-check:vex: wr_addr");
        assert property (@(posedge clk) disable iff(!rst_n) wr_en[k] |-> ~$isunknown(|wr_ticket))
            else $error("x-check:vex: wr_ticket");
    end
endgenerate
//=======================================================
// Properties
//=======================================================
