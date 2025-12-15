module fifo #(
    parameter DATA_WIDTH = 8,
    parameter DEPTH = 16
) (
    input wire clk,
    input wire rst_n,
    input wire wr_en,
    input wire [DATA_WIDTH-1:0] wdata,
    input wire rd_en,
    output reg [DATA_WIDTH-1:0] rdata,
    output wire full,
    output wire empty
);

    localparam ADDR_WIDTH = $clog2(DEPTH);

    reg [DATA_WIDTH-1:0] mem[0:DEPTH-1];
    reg [ADDR_WIDTH-1:0] w_ptr;
    reg [ADDR_WIDTH-1:0] r_ptr;
    reg [ADDR_WIDTH:0] count;

    assign full  = (count == DEPTH);
    assign empty = (count == 0);

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            w_ptr <= 0;
        end else if (wr_en && !full) begin
            mem[w_ptr] <= wdata;
            w_ptr <= (w_ptr == DEPTH - 1) ? 0 : w_ptr + 1;
        end
    end

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            r_ptr <= 0;
            rdata <= 0;
        end else if (rd_en && !empty) begin
            rdata <= mem[r_ptr];
            r_ptr <= (r_ptr == DEPTH - 1) ? 0 : r_ptr + 1;
        end
    end

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            count <= 0;
        end else begin
            case ({
                wr_en && !full, rd_en && !empty
            })
                2'b10:   count <= count + 1;
                2'b01:   count <= count - 1;
                default: count <= count;
            endcase
        end
    end

    always_comb assume (!rst_n == $initstate);

    reg [DATA_WIDTH-1:0] first_data;
    reg first_push;
    reg first_pop;
    reg [DATA_WIDTH-1:0] second_data;
    reg second_push;
    reg second_pop;

    always @(posedge clk) begin
        if (!rst_n) begin
            first_push  <= 0;
            first_pop   <= 0;
            second_push <= 0;
            second_pop  <= 0;
        end else begin
            first_data  <= first_data;
            second_data <= second_data;
            assert ($stable(first_data));
            assert ($stable(second_data));

            if (wr_en && !full) begin
                if (!first_push && first_data == wdata) begin
                    first_push <= 1;
                end else if (first_push && second_data == wdata) begin
                    second_push <= 1;
                end
            end

            if (rd_en && !empty) begin
                if (first_push && first_data == mem[r_ptr]) begin
                    first_pop <= 1;
                end
                if (first_pop && second_push && second_data == mem[r_ptr]) begin
                    second_pop <= 1;
                end
            end

            assert (s_eventually(second_pop));

        end
    end
endmodule
