module invariants (
    input logic clk,
    input logic rst_n
);
// To use a signal from frame_proc, reference it as frame_proc.XXX.

localparam h_MAIN_FIFO_DEPTH = 8;
localparam h_RPT_FIFO_DEPTH = 16;
localparam h_MAIN_FIFO_WIDTH = 283;
localparam h_RPT_FIFO_WIDTH = 26;

wire [15:0] h_main_span = frame_proc.cnt_in - frame_proc.cnt_out_main;
wire [15:0] h_rpt_span = frame_proc.cnt_out_main - frame_proc.cnt_out_rpt;
wire [15:0] h_main_target_off = frame_proc.fv_target_id - frame_proc.cnt_out_main;
wire [15:0] h_rpt_target_off = frame_proc.fv_target_id - frame_proc.cnt_out_rpt;

wire [2:0] h_main_wptr_expected = frame_proc.u_main_fifo.r_ptr + frame_proc.u_main_fifo.count[2:0];
wire [3:0] h_rpt_wptr_expected = frame_proc.u_rpt_fifo.r_ptr + frame_proc.u_rpt_fifo.count[3:0];

wire h_main_target_live = frame_proc.target_valid && (h_main_target_off < h_main_span);
wire h_rpt_target_live = frame_proc.target_valid && (h_rpt_target_off < h_rpt_span);

wire [2:0] h_main_target_idx = frame_proc.u_main_fifo.r_ptr + h_main_target_off[2:0];
wire [3:0] h_rpt_target_idx = frame_proc.u_rpt_fifo.r_ptr + h_rpt_target_off[3:0];

wire [h_MAIN_FIFO_WIDTH-1:0] h_main_target_word = frame_proc.u_main_fifo.mem[h_main_target_idx];
wire [h_RPT_FIFO_WIDTH-1:0] h_rpt_target_word = frame_proc.u_rpt_fifo.mem[h_rpt_target_idx];

always @(posedge clk) begin
    if (rst_n) begin
        h_main_fifo_count_bound: assert(frame_proc.u_main_fifo.count <= h_MAIN_FIFO_DEPTH);
        h_rpt_fifo_count_bound: assert(frame_proc.u_rpt_fifo.count <= h_RPT_FIFO_DEPTH);

        h_main_fifo_ptr_count: assert(frame_proc.u_main_fifo.w_ptr == h_main_wptr_expected);
        h_rpt_fifo_ptr_count: assert(frame_proc.u_rpt_fifo.w_ptr == h_rpt_wptr_expected);

        h_main_counter_span: assert(h_main_span == {12'd0, frame_proc.u_main_fifo.count});
        h_rpt_counter_span: assert(h_rpt_span == {11'd0, frame_proc.u_rpt_fifo.count});

        h_main_state_valid: assert(frame_proc.state_cur != 2'd3);
        h_rpt_state_valid: assert(frame_proc.r_state_cur != 2'd3);

        if (frame_proc.state_cur != 2'd0) begin
            h_main_active_has_data: assert(frame_proc.u_main_fifo.count != 4'd0);
        end

        if (frame_proc.r_state_cur != 2'd0) begin
            h_rpt_active_has_data: assert(frame_proc.u_rpt_fifo.count != 5'd0);
        end

        if (frame_proc.state_cur == 2'd0) begin
            h_main_idle_delay_zero: assert(frame_proc.delay_cnt == 3'd0);
        end

        if (frame_proc.state_cur == 2'd1) begin
            h_main_process_delay_bound: assert(frame_proc.delay_cnt < frame_proc.target_delay);
        end

        if (frame_proc.r_state_cur == 2'd0) begin
            h_rpt_idle_delay_zero: assert(frame_proc.r_delay_cnt == 3'd0);
        end

        if (frame_proc.r_state_cur == 2'd1) begin
            h_rpt_process_delay_bound: assert(frame_proc.r_delay_cnt < 3'd4);
        end

        h_ref_correct_match: assert(frame_proc.ref_is_correct == frame_proc.frame_is_correct);

        if (!frame_proc.target_valid) begin
            h_uncaptured_not_in_main: assert(h_main_target_off >= h_main_span);
            h_uncaptured_not_in_rpt: assert(h_rpt_target_off >= h_rpt_span);
        end

        if (h_main_target_live) begin
            h_main_target_correct: assert(h_main_target_word[282] == frame_proc.saved_is_correct);
            h_main_target_psn: assert(h_main_target_word[279:256] == frame_proc.saved_psn);
            h_main_target_data: assert(h_main_target_word[255:0] == frame_proc.saved_expected_data);
        end

        if (h_rpt_target_live) begin
            h_rpt_target_psn: assert(h_rpt_target_word[25:2] == frame_proc.saved_psn);
        end
    end
end
endmodule

bind frame_proc invariants invariants (.*);
