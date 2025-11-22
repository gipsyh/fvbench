module sync_fifo #(
    parameter int DATA_WIDTH = 8,
    parameter int DEPTH = 16
) (
    input logic clk,
    input logic rst_n,
    input logic wr_en,
    input logic [DATA_WIDTH-1:0] wdata,
    input logic rd_en,
    output logic [DATA_WIDTH-1:0] rdata,
    output logic full,
    output logic empty
);

    localparam int ADDR_WIDTH = $clog2(DEPTH);

    logic [DATA_WIDTH-1:0] mem[0:DEPTH-1];
    logic [ADDR_WIDTH-1:0] w_ptr;
    logic [ADDR_WIDTH-1:0] r_ptr;
    logic [ADDR_WIDTH:0] count;

    assign full  = (count == DEPTH);
    assign empty = (count == 0);

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            w_ptr <= '0;
        end else if (wr_en && !full) begin
            mem[w_ptr] <= wdata;
            w_ptr      <= (w_ptr == DEPTH - 1) ? '0 : w_ptr + 1;
        end
    end

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            r_ptr <= '0;
            rdata <= '0;
        end else if (rd_en && !empty) begin
            rdata <= mem[r_ptr];
            r_ptr <= (r_ptr == DEPTH - 1) ? '0 : r_ptr + 1;
        end
    end

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            count <= '0;
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
endmodule
