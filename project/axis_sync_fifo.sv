module AXIS_SYNC_FIFO #(
    parameter DEPTH = 16,
    parameter WIDTH = 8
) (
    input clk,
    input rstn,

    input [WIDTH-1:0] s_axis_tdata,
    input s_axis_tvalid,
    output logic s_axis_tready,

    output logic [WIDTH-1:0] m_axis_tdata,
    output logic m_axis_tvalid,
    input m_axis_tready
);

    logic full, empty;

    SYNC_FIFO #(DEPTH, WIDTH) sync_fifo (
        .clk(clk),
        .rstn(rstn),
        .wdata(s_axis_tdata),
        .wen(s_axis_tvalid),
        .full(full),
        .rdata(m_axis_tdata),
        .ren(m_axis_tready),
        .empty(empty)
    );
    
    assign s_axis_tready = !full;
    assign m_axis_tvalid = !empty;

    `ifdef FORMAL
        logic past_valid;
        initial past_valid = 0;
        always@(posedge clk)
            past_valid <= 1;

        initial m_axis_tvalid = 0;
        initial s_axis_tready = 1;
        // Reset
        always@(posedge clk)
            if (!$past(rstn))
                a0: assert (s_axis_tready && !m_axis_tvalid);

        // When m_axis_tready is 0 and m_axis_tvalid is 1, m_axis_tvalid and m_axis_tdata must not change until m_axis_tready is asserted
        always@(posedge clk)
            if(!$past(m_axis_tready) && $past(m_axis_tvalid) && past_valid && $past(rstn))
                a1: assert(m_axis_tvalid == $past(m_axis_tvalid) && m_axis_tdata == $past(m_axis_tdata));

    `endif
endmodule