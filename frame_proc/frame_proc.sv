/*
你是一个成熟的芯片设计工程师，擅长使用verilog去编写代码，请你帮我写一个module，要求如下：

1、接口i_valid_1 o_ready_1为数据流的开始，其握手成功代表dut接受到了一个帧，i_frame_type是一个2bit信号，在i_valid_1拉高时有效，若i_frame_type==0，代表帧头；若i_frame_type==1，代表帧身；若i_frame_type==2，代表帧尾；若i_frame_type==3，代表帧错误；i_frame_psn是24bit信号，在i_valid_1拉高时有效，每个无误帧的psn是递增+1的。i_frame_data是256bit的数据。在i_valid_1拉高时有效。

note：什么是正确帧？1、头在帧尾前或者同时收到；2、psn相较于上一个正确帧的psn+1；3、i_frame_type！=3。若收到错误帧，则该帧不作数，下一个正确帧的格式不变

2、如果帧正确，则dut会对此帧的i_frame_data做处理，处理2~10个周期不等。最终会从o_valid_2接口上输出，i_ready_2是o_valid_2的握手信号。随路信号包括o_frame_psn_2，o_frame_type_2，这两个信号与该帧输入时的i_frame_psn，i_frame_type完全一样

3、若帧错误，则dut会对此帧的i_frame_data做处理全等于0，处理2~10个周期不等。最终会从o_valid_3接口上输出，i_ready_3是o_valid_3的握手信号。随路信号包括o_frame_psn_3，o_frame_type_3，这两个信号与该帧输入时的i_frame_psn，i_frame_type完全一样。

4、不论是正确帧还是错误帧，在o_valid_2获o_valid_3接口输出后，都会在2~10周期内，在o_valid_4接口输出，i_ready_4是o_valid_4的握手信号。随路信号包括o_frame_psn_4，o_frame_type_4，这两个信号与该帧输入时的i_frame_psn，i_frame_type完全一样
*/
module frame_processor_dut (
    input logic clk,
    input logic rst_n,

    // Interface 1: Input (RX)
    input  logic         i_valid_1,
    output logic         o_ready_1,
    input  logic [  1:0] i_frame_type,  // 0:Head, 1:Body, 2:Tail, 3:Err
    input  logic [ 23:0] i_frame_psn,
    input  logic [255:0] i_frame_data,

    // Interface 2: Correct Frame Output (TX Correct)
    output logic         o_valid_2,
    input  logic         i_ready_2,
    output logic [ 23:0] o_frame_psn_2,
    output logic [  1:0] o_frame_type_2,
    output logic [255:0] o_frame_data_2,

    // Interface 3: Error Frame Output (TX Error)
    output logic         o_valid_3,
    input  logic         i_ready_3,
    output logic [ 23:0] o_frame_psn_3,
    output logic [  1:0] o_frame_type_3,
    output logic [255:0] o_frame_data_3,

    // Interface 4: Report Output (TX Report)
    output logic        o_valid_4,
    input  logic        i_ready_4,
    output logic [23:0] o_frame_psn_4,
    output logic [ 1:0] o_frame_type_4
);

    //==============================================================
    // Local Parameters & Types
    //==============================================================
    localparam TYPE_HEAD = 2'd0;
    localparam TYPE_BODY = 2'd1;
    localparam TYPE_TAIL = 2'd2;
    localparam TYPE_ERR = 2'd3;

    // Main FSM States
    typedef enum logic [1:0] {
        S_IDLE,
        S_PROCESS,
        S_OUTPUT
    } state_t;

    // Report FSM States
    typedef enum logic [1:0] {
        R_IDLE,
        R_WAIT,
        R_OUTPUT
    } rpt_state_t;

    //==============================================================
    // Signal Declarations
    //==============================================================

    // --- Validation Logic Signals ---
    logic [23:0] exp_psn_r;  // Expected PSN register
    logic        inside_frame_r;  // Context state: Are we inside a packet?
    logic        chk_seq_valid;  // Rule 1 check
    logic        chk_psn_valid;  // Rule 2 check
    logic        chk_type_valid;  // Rule 3 check
    logic        frame_is_good;  // Combined result

    // --- Main Pipeline Signals ---
    state_t state_cur, state_next;
    logic [  3:0] delay_cnt;
    logic [  3:0] target_delay;

    // Data latched from Interface 1
    logic [255:0] lat_data;
    logic [ 23:0] lat_psn;
    logic [  1:0] lat_type;
    logic         lat_is_good;

    // --- Report FIFO Signals (Decoupling IF4) ---
    // A small FIFO to store completed frames waiting for IF4 report
    // Structure: {psn, type}
    logic         fifo_wr_en;
    logic         fifo_rd_en;
    logic         fifo_full;
    logic         fifo_empty;
    logic [ 25:0] fifo_din;
    logic [ 25:0] fifo_dout;

    // --- Report FSM Signals ---
    rpt_state_t rpt_state_cur, rpt_state_next;
    logic [3:0] rpt_delay_cnt;
    logic [3:0] rpt_target_delay;


    //==============================================================
    // 1. Input Logic & Validation (Interface 1)
    //==============================================================

    // Rule 1: Sequence Check (Head before Tail)
    // We track if we have seen a Head but not yet a Tail.
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            inside_frame_r <= 1'b0;
        end else if (i_valid_1 && o_ready_1) begin
            if (i_frame_type == TYPE_HEAD) inside_frame_r <= 1'b1;
            else if (i_frame_type == TYPE_TAIL) inside_frame_r <= 1'b0;
        end
    end

    // Judgment Logic:
    // If Type is HEAD: Always valid sequence start (assuming nested heads imply restart).
    // If Type is BODY/TAIL: Must be inside_frame to be valid.
    assign chk_seq_valid  = (i_frame_type == TYPE_HEAD) || inside_frame_r;

    // Rule 2: PSN Check
    assign chk_psn_valid  = (i_frame_psn == exp_psn_r);

    // Rule 3: Type Check
    assign chk_type_valid = (i_frame_type != TYPE_ERR);

    // Global Valid Flag
    assign frame_is_good  = chk_seq_valid && chk_psn_valid && chk_type_valid;

    // Expected PSN Maintenance
    // "每个无误帧的psn是递增+1的... 若收到错误帧... 下一个正确帧的格式不变"
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            exp_psn_r <= 24'd0;
        end else if (i_valid_1 && o_ready_1 && frame_is_good) begin
            exp_psn_r <= exp_psn_r + 1'b1;
        end
    end

    //==============================================================
    // 2. Main Processing FSM (Handling IF1 -> IF2/IF3)
    //==============================================================

    // Handshake: Ready if IDLE and Report FIFO isn't full (backpressure propagation)
    assign o_ready_1 = (state_cur == S_IDLE) && !fifo_full;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state_cur    <= S_IDLE;
            delay_cnt    <= 4'd0;
            lat_data     <= '0;
            lat_psn      <= '0;
            lat_type     <= '0;
            lat_is_good  <= 1'b0;
            target_delay <= 4'd2;
        end else begin
            state_cur <= state_next;

            // Latching Logic
            if (state_cur == S_IDLE && i_valid_1 && o_ready_1) begin
                lat_data     <= i_frame_data;
                lat_psn      <= i_frame_psn;
                lat_type     <= i_frame_type;
                lat_is_good  <= frame_is_good;

                // Generate deterministic delay [2, 10]
                // Logic: Take lowest 3 bits of PSN, map 0->2, 7->9. Valid range 2-9.
                target_delay <= (i_frame_psn[2:0]) + 4'd2;
                delay_cnt    <= 4'd0;
            end  // Counting Logic
            else if (state_cur == S_PROCESS) begin
                delay_cnt <= delay_cnt + 1'b1;
            end
        end
    end

    always_comb begin
        state_next = state_cur;
        case (state_cur)
            S_IDLE: begin
                if (i_valid_1 && o_ready_1) state_next = S_PROCESS;
            end
            S_PROCESS: begin
                // Wait for delay cycles
                if (delay_cnt >= target_delay - 1) state_next = S_OUTPUT;
            end
            S_OUTPUT: begin
                // Check which interface we are driving
                if (lat_is_good) begin
                    if (i_ready_2) state_next = S_IDLE;
                end else begin
                    if (i_ready_3) state_next = S_IDLE;
                end
            end
        endcase
    end

    // Output Logic for IF2 (Correct)
    assign o_valid_2      = (state_cur == S_OUTPUT) && lat_is_good;
    assign o_frame_psn_2  = lat_psn;
    assign o_frame_type_2 = lat_type;
    assign o_frame_data_2 = lat_data;  // Processing logic (Pass-through for now)

    // Output Logic for IF3 (Error)
    assign o_valid_3      = (state_cur == S_OUTPUT) && !lat_is_good;
    assign o_frame_psn_3  = lat_psn;
    assign o_frame_type_3 = lat_type;
    assign o_frame_data_3 = 256'd0;  // Requirement: Data all 0

    //==============================================================
    // 3. Reporting Trigger (Bridge between Main FSM and Report FSM)
    //==============================================================

    // When main FSM finishes output handshake, push info to FIFO
    wire main_tx_done = (state_cur == S_OUTPUT) && 
                        ((lat_is_good && i_ready_2) || (!lat_is_good && i_ready_3));

    assign fifo_wr_en = main_tx_done;
    assign fifo_din   = {lat_psn, lat_type};

    // Instantiate a small synchronous FIFO here
    // For this code to be self-contained, I implement a lightweight RTL FIFO
    // Depth 4 is usually sufficient to cover the gap between processing times

    logic [25:0] mem[3:0];
    logic [1:0] wptr, rptr;
    logic [2:0] count;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            wptr  <= 0;
            rptr  <= 0;
            count <= 0;
        end else begin
            if (fifo_wr_en && !fifo_full) begin
                mem[wptr] <= fifo_din;
                wptr <= wptr + 1'b1;
                if (!fifo_rd_en) count <= count + 1'b1;
            end
            if (fifo_rd_en && !fifo_empty) begin
                rptr <= rptr + 1'b1;
                if (!fifo_wr_en) count <= count - 1'b1;
            end
        end
    end

    assign fifo_full  = (count == 3'd4);
    assign fifo_empty = (count == 3'd0);
    assign fifo_dout  = mem[rptr];

    //==============================================================
    // 4. Report Processing FSM (Handling IF4)
    //==============================================================

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            rpt_state_cur    <= R_IDLE;
            rpt_delay_cnt    <= 0;
            rpt_target_delay <= 4'd2;
            o_valid_4        <= 1'b0;
            o_frame_psn_4    <= '0;
            o_frame_type_4   <= '0;
            fifo_rd_en       <= 1'b0;
        end else begin
            // Default pulse reset
            fifo_rd_en <= 1'b0;
            rpt_state_cur <= rpt_state_next;

            // State Logic
            case (rpt_state_cur)
                R_IDLE: begin
                    if (!fifo_empty) begin
                        // Pop from FIFO
                        fifo_rd_en       <= 1'b1;
                        // Capture data for report
                        o_frame_psn_4    <= fifo_dout[25:2];
                        o_frame_type_4   <= fifo_dout[1:0];
                        // Generate delay based on Type (just for variety)
                        rpt_target_delay <= {2'b0, fifo_dout[1:0]} + 4'd3;
                        rpt_delay_cnt    <= 0;
                        rpt_state_cur    <= R_WAIT;
                    end
                end

                R_WAIT: begin
                    rpt_delay_cnt <= rpt_delay_cnt + 1'b1;
                    if (rpt_delay_cnt >= rpt_target_delay - 1) begin
                        rpt_state_cur <= R_OUTPUT;
                    end
                end

                R_OUTPUT: begin
                    if (i_ready_4) begin
                        rpt_state_cur <= R_IDLE;
                    end
                end
            endcase
        end
    end

    // Output Logic for IF4
    // Note: FSM registers above already drive data lines
    assign o_valid_4 = (rpt_state_cur == R_OUTPUT);

    // FSM Next Logic (Combinational part for R_IDLE/WAIT transitions done in FF for compactness)
    // But we need combinational helper for next state to ensure clean logic
    always_comb begin
        rpt_state_next = rpt_state_cur;
        case (rpt_state_cur)
            R_IDLE:   if (!fifo_empty) rpt_state_next = R_WAIT;
            R_WAIT:   if (rpt_delay_cnt >= rpt_target_delay - 1) rpt_state_next = R_OUTPUT;
            R_OUTPUT: if (i_ready_4) rpt_state_next = R_IDLE;
        endcase
    end





    //==============================================================
    // 1. 辅助建模 (Auxiliary Modeling)
    //    Formal的核心：在验证环境中重建“黄金模型”来比对DUT行为
    //==============================================================

    // 1.1 重建“正确帧”判断逻辑
    // 需要完全复刻 spec 中的判断逻辑，或者如果相信 RTL 的判断逻辑可以简化，
    // 但作为 Formal，最好是独立写一套逻辑来 Cross Check

    logic [23:0] model_exp_psn;
    logic        model_inside_frame;

    // 模拟 PSN 预期值
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) model_exp_psn <= 24'd0;
        else if (i_valid_1 && o_ready_1 && is_frame_correct_model) begin
            model_exp_psn <= model_exp_psn + 1'b1;
        end
    end

    // 模拟帧序 (Head/Tail)
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) model_inside_frame <= 1'b0;
        else if (i_valid_1 && o_ready_1) begin
            if (i_frame_type == 2'd0) model_inside_frame <= 1'b1;  // Head
            else if (i_frame_type == 2'd2) model_inside_frame <= 1'b0;  // Tail
        end
    end

    // 组合逻辑判断当前输入是否正确
    logic is_seq_ok, is_psn_ok, is_type_ok, is_frame_correct_model;
    assign is_seq_ok = (i_frame_type == 2'd0) || model_inside_frame;
    assign is_psn_ok = (i_frame_psn == model_exp_psn);
    assign is_type_ok = (i_frame_type != 2'd3);
    assign is_frame_correct_model = is_seq_ok && is_psn_ok && is_type_ok;

    //==============================================================
    // 2. 约束 (Assumptions)
    //    限制输入环境的行为，防止 False Fail
    //==============================================================

    // 约束：复位时 Valid 为低 (Basic)
    asm_rst :
    assume property (@(posedge clk) !rst_n |-> !i_valid_1 && !i_ready_2 && !i_ready_3 && !i_ready_4);

    // 约束：下游的反压信号 i_ready 应该是合理的
    // 这里我们假设下游总是会最终 ready（Liveness assumption），
    // 或者简单地假设下游随机 ready。Formal 工具默认会遍历所有 ready 组合。
    // 如果要证明 Liveness (最终能发出去)，需要加公平性约束:
    // assume property (@(posedge clk) s_eventually i_ready_2);

    //==============================================================
    // 3. 断言 (Assertions)
    //==============================================================

    //--------------------------------------------------------------
    // 3.1 协议检查 (Protocol Stability)
    //--------------------------------------------------------------
    // 举例：当 o_valid_2 拉高但 i_ready_2 为低时，数据必须保持稳定
    property p_stable_output(valid, ready, data, psn, type_sig);
        @(posedge clk) disable iff (!rst_n) (valid && !ready) |=> $stable(
            {data, psn, type_sig}
        ) && valid;
    endproperty

    a_stable_if2 :
    assert property (p_stable_output(
        o_valid_2, i_ready_2, o_frame_data_2, o_frame_psn_2, o_frame_type_2
    ));
    a_stable_if3 :
    assert property (p_stable_output(
        o_valid_3, i_ready_3, o_frame_data_3, o_frame_psn_3, o_frame_type_3
    ));
    a_stable_if4 :
    assert property (p_stable_output(
        o_valid_4, i_ready_4, 26'd0, o_frame_psn_4, o_frame_type_4
    ));  // Data dummy for if4

    //--------------------------------------------------------------
    // 3.2 核心功能：正确帧的处理 (Correct Frame Path)
    //--------------------------------------------------------------
    property p_correct_frame_processing;
        // 定义局部变量来捕获进入时刻的数据
        logic [23:0] v_psn
        ;
        logic [255:0] v_data
        ;
        logic [1:0] v_type;
        @(posedge clk) disable iff (!rst_n)
        // 前提：输入有效，握手成功，且根据模型判断是正确帧
        (i_valid_1 && o_ready_1 && is_frame_correct_model,
        v_psn = i_frame_psn
        ,
        v_data = i_frame_data
        ,
        v_type = i_frame_type
        ) |->
        // 结果：在2到10个周期内，接口2有输出，且数据匹配
        ##[2:10] (o_valid_2 && 
                  o_frame_psn_2 == v_psn && 
                  o_frame_data_2 == v_data && 
                  o_frame_type_2 == v_type);
    endproperty

    a_core_correct_path :
    assert property (p_correct_frame_processing);

    //--------------------------------------------------------------
    // 3.3 核心功能：错误帧的处理 (Error Frame Path)
    //--------------------------------------------------------------
    property p_error_frame_processing;
        logic [23:0] v_psn
        ;
        logic [1:0] v_type;
        @(posedge clk) disable iff (!rst_n) (i_valid_1 && o_ready_1 && !is_frame_correct_model,
        v_psn = i_frame_psn
        ,
        v_type = i_frame_type
        ) |-> ##[2:10] (o_valid_3 && o_frame_psn_3 == v_psn &&
                        o_frame_data_3 == 256'd0 &&  // 关键检查：数据全0
        o_frame_type_3 == v_type);
    endproperty

    a_core_error_path :
    assert property (p_error_frame_processing);

    //--------------------------------------------------------------
    // 3.4 核心功能：汇报逻辑 (Report Path)
    //    这是级联检查：IF2/3 完成 -> IF4 输出
    //--------------------------------------------------------------

    // 定义一个事件：任一输出接口完成握手
    sequence s_tx_done; (o_valid_2 && i_ready_2) || (o_valid_3 && i_ready_3); endsequence

    property p_report_generation;
        logic [23:0] v_psn
        ;
        logic [1:0] v_type;
        @(posedge clk) disable iff (!rst_n)
        // 当接口2或接口3完成握手时，捕获当时的 PSN 和 Type (注意：需捕获正在输出的值)
        // 这里需要细心：握手发生时，o_frame_psn_X 还是有效的
        ((o_valid_2 && i_ready_2,
        v_psn = o_frame_psn_2
        ,
        v_type = o_frame_type_2
        ) or(o_valid_3 && i_ready_3,
        v_psn = o_frame_psn_3
        ,
        v_type = o_frame_type_3
        )) |->
        // 结果：2到10个周期后，接口4输出同样的 PSN/Type
        ##[2:10] (o_valid_4 && o_frame_psn_4 == v_psn && o_frame_type_4 == v_type);
    endproperty

    a_core_report_path :
    assert property (p_report_generation);

    //--------------------------------------------------------------
    // 3.5 状态机互斥检查 (Safety)
    //--------------------------------------------------------------
    // 任何时刻，o_valid_2 和 o_valid_3 不能同时有效
    a_mutex_output :
    assert property (@(posedge clk) !(o_valid_2 && o_valid_3));
endmodule

