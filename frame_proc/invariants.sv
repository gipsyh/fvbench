module invariants (
    input logic clk,
    input logic rst_n
);
    P0 :
    assert property (@(posedge clk) disable iff (!rst_n) frame_proc.u_main_fifo.count != 5);
endmodule

bind frame_proc invariants invariants (.*);
