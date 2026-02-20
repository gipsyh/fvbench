module pipe #(
    parameter W = 16
) (
    input clk,
    rst_n,
    stall,
    input [W-1:0] a,
    b,
    c
);
    reg [W-1:0] r1, r2, r3, r4, d1, d2;
    initial r1 = 0;
    always @(posedge clk) begin
        if (!rst_n) begin
            {r1, r2, r3, r4, d1, d2} <= 0;
        end else begin
            if (!stall) begin
                r1 <= a + b;
                r2 <= c;
                r3 <= a + c;
                r4 <= b;
                d1 <= r1 + r2;
                d2 <= r3 + r4;
            end
            // h_1: assert (r1 + r2 == r3 + r4);
            o_1 : assert (d1 == d2);
        end
    end
endmodule
