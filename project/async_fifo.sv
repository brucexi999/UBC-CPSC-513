module ASYNC_FIFO #(
    parameter DEPTH = 16,
    parameter WIDTH = 8
) (
    input wclk,
    input rclk,
    input wrstn,
    input rrstn,

    input [WIDTH-1:0] wdata,
    input wen,
    output logic full,

    output logic [WIDTH-1:0] rdata,
    input ren,
    output logic empty
);
    localparam int PTR_WIDTH = $clog2(DEPTH) + 1; // +1 such that the write pointer can wrap around and produce the full condition
    logic [PTR_WIDTH-1:0] wptr, rptr; // Pointers in binary
    logic [PTR_WIDTH-1:0] wptr_gray, rptr_gray; // Pointers in Gray code
    logic [PTR_WIDTH-1:0] wptr_gray_sync1, rptr_gray_sync1; // Intermediate wires in the 2-FF synchronizers
    logic [PTR_WIDTH-1:0] wptr_gray_sync2, rptr_gray_sync2; // Output of the 2-FF synchronizers, clock domains crossed
    logic [WIDTH-1:0] mem [0:DEPTH-1];

    // Cross the read Gray pointer into the write clock domain via the r->w synchronizer
    always@(posedge wclk or negedge wrstn) begin
        if (!wrstn) begin
            {rptr_gray_sync2, rptr_gray_sync1} <= 0;
        end
        else begin
            {rptr_gray_sync2, rptr_gray_sync1} <= {rptr_gray_sync1, rptr_gray};
        end
    end

    always@(posedge wclk or negedge wrstn) begin
        if (!wrstn) begin
            wptr <= 0;
        end
        else if (wen & !full) begin
            wptr <= wptr + 1;
        end
    end

    always@(posedge wclk or negedge wrstn) begin
        if (!wrstn) begin
            int i;
            for (i=0; i<DEPTH; i++) begin
                mem[i] <= 0;
            end
        end
        else if (wen & !full) begin
            mem[wptr[PTR_WIDTH-2:0]] <= wdata;
        end
    end

    assign wptr_gray = wptr ^ (wptr >> 1);
    assign full = (wptr_gray == {~rptr_gray_sync2[PTR_WIDTH-1:PTR_WIDTH-2], rptr_gray_sync2[PTR_WIDTH-3:0]});

    // Cross the write Gray pointer into the read clock domain via the w->r synchronizer
    always@(posedge rclk or negedge rrstn) begin
        if (!rrstn) begin
            {wptr_gray_sync2, wptr_gray_sync1} <= 0;
        end
        else begin
            {wptr_gray_sync2, wptr_gray_sync1} <= {wptr_gray_sync1, wptr_gray};
        end
    end

    always@(posedge rclk or negedge rrstn) begin
        if (!rrstn) begin
            rptr <= 0;
        end
        else if (!empty && ren) begin
            rptr <= rptr + 1;
        end
    end

    assign rptr_gray = rptr ^ (rptr >> 1);
    assign rdata = mem[rptr[PTR_WIDTH-2:0]];
    assign empty = (rptr_gray == wptr_gray_sync2);

endmodule