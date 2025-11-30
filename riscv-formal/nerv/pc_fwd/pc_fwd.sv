// Copyright (C) 2017  Claire Xenia Wolf <claire@yosyshq.com>
//
// Permission to use, copy, modify, and/or distribute this software for any
// purpose with or without fee is hereby granted, provided that the above
// copyright notice and this permission notice appear in all copies.
//
// THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
// WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
// MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
// ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
// WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
// ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
// OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.

`include "defines.sv"
`include "rvfi_channel.sv"

module rvfi_testbench (
	`ifdef RISCV_FORMAL_UNBOUNDED
	`ifdef RISCV_FORMAL_TRIG_CYCLE
		input trig,
	`endif
	`ifdef RISCV_FORMAL_CHECK_CYCLE
		input check,
	`endif
	`endif
	input clock, reset
);
	`RVFI_WIRES
	`RVFI_BUS_WIRES

	always_comb assume (reset == $initstate);

	reg [7:0] cycle_reg = 0;
	wire [7:0] cycle = reset ? 8'd 0 : cycle_reg;

	always @(posedge clock) begin
		cycle_reg <= reset ? 8'd 1 : cycle_reg + (cycle_reg != 8'h ff);
	end

	rvfi_wrapper wrapper (
		.clock (clock),
		.reset (reset),
		`RVFI_CONN
		`RVFI_BUS_CONN
	);

`ifdef FORMAL
	`rvformal_rand_const_reg [63:0] insn_order;
	reg [`RISCV_FORMAL_XLEN-1:0] expect_pc;
	reg expect_pc_valid = 0;

	wire [`RISCV_FORMAL_XLEN-1:0] pc_rdata = rvfi_pc_rdata[`RISCV_FORMAL_CHANNEL_IDX*`RISCV_FORMAL_XLEN +: `RISCV_FORMAL_XLEN];

	always @(posedge clock) begin
		if (reset) begin
			expect_pc_valid = 0;
		end else begin
			if (check) begin
				assume(rvfi_valid[`RISCV_FORMAL_CHANNEL_IDX]);
				assume(insn_order == rvfi_order);
				if (expect_pc_valid && !rvfi_intr[`RISCV_FORMAL_CHANNEL_IDX]) begin
					assert(`rvformal_addr_eq(expect_pc, pc_rdata));
				end
			end else begin
				if (rvfi_valid && rvfi_order == insn_order-1) begin
					assert(expect_pc_valid == 0);
					expect_pc = rvfi_pc_wdata;
					expect_pc_valid = 1;
				end
			end
		end
	end
`endif

endmodule
