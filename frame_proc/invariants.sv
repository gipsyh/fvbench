module invariants ();
    P0 :
    assert property (@(posedge frame_proc.clk) disable iff (!frame_proc.rst_n) frame_proc.u_rpt_fifo.count != 10);
endmodule

bind frame_proc invariants invariants ();
