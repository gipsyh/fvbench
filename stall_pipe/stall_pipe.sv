module stall_pipe (
    input clk,
    input rst_n,
    input stall,
    input wire [15:0] a,
    input wire [15:0] b,
    input wire [15:0] c,
    output reg [15:0] d1,
    output reg [15:0] d2
);
    reg [15:0] r1, r2, r3, r4;
    always_comb assume (!rst_n == $initstate);
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            r1 <= 0;
            r2 <= 0;
            r3 <= 0;
            r4 <= 0;
            d1 <= 0;
            d2 <= 0;
        end else begin
            if (!stall) begin
                r1 <= a + b;
                r2 <= c;
                r3 <= a + c;
                r4 <= b;
                d1 <= r1 + r2;
                d2 <= r3 + r4;
            end
        end
    end
    assert property (d1 == d2);
endmodule
