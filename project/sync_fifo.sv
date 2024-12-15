module SYNC_FIFO #(
    parameter integer DEPTH = 16,
    parameter integer WIDTH = 8
) (
    input clk,
    input rstn,

    input [WIDTH-1:0] wdata,
    input wen,
    output logic full,
    
    output logic [WIDTH-1:0] rdata,
    input ren,
    output logic empty
);

    localparam int PTR_WIDTH = $clog2(DEPTH) + 1; // +1 such that the write pointer can wrap around and produce the full condition
    logic [PTR_WIDTH-1:0] wptr, rptr;
    logic [WIDTH-1:0] mem [0:DEPTH-1];

    always@(posedge clk) begin
        if (!rstn) begin
            int i;
            for (i=0; i<DEPTH; i++) begin
                mem[i] <= 0;
            end
        end
        else if (!full && wen) begin
            mem[wptr[PTR_WIDTH-2:0]] <= wdata;
        end
    end

    always@(posedge clk) begin
        if(!rstn) begin
            wptr <= 0;
        end
        else if (!full && wen) begin
            wptr <= wptr + 1;
        end
    end

    always@(posedge clk) begin
        if(!rstn) begin
            rptr <= 0;
        end
        else if (!empty && ren) begin
            rptr <= rptr + 1;
        end
    end

    assign full = {~wptr[PTR_WIDTH-1], wptr[PTR_WIDTH-2:0]} == rptr;
    assign empty = wptr == rptr;
    assign rdata = mem[rptr[PTR_WIDTH-2:0]];

    /*
    Will be asserted at the second cycle and hence help eliminate the issue
    where $past() will return undefined values at the first cycle
    */
    logic past_valid;
    initial past_valid = 0;
    always@(posedge clk)
        past_valid <= 1;

    initial wptr = 0;
    initial rptr = 0;

    `ifdef FORMAL
        // Never full and empty at the same time
        always@(*)
            a0: assert(!(full && empty));

        // If full, then the two pointers should only defer at the MSB
        always@(*)
            if (full)
                a1: assert({~wptr[PTR_WIDTH-1], wptr[PTR_WIDTH-2:0]} == rptr);
        
        // If empty, then the two pointers should be the same
        always@(*)
            if (empty)
                a2: assert(wptr == rptr);

        // No overflow
        always@(posedge clk)
            if ($past(full) && $past(wen) && past_valid && $past(rstn))
                a3: assert(wptr == $past(wptr));
        
        // No underflow
        always@(posedge clk)
            if ($past(empty) && $past(ren) && past_valid && $past(rstn))
                a4: assert(rptr == $past(rptr));

        // Normal write
        always@(posedge clk)
            if (!$past(full) && $past(wen) && past_valid && $past(rstn)) begin
                if ($past(wptr) == {PTR_WIDTH{1'b1}})
                    a5: assert(wptr == 0);
                else
                    a6: assert(wptr == $past(wptr) + 1);
            end
        
        // Normal read
        always@(posedge clk)
            if (!$past(empty) && $past(ren) && past_valid && $past(rstn)) begin
                if ($past(rptr) == {PTR_WIDTH{1'b1}})
                    a7: assert(rptr == 0);
                else
                    a8: assert(rptr == $past(rptr) + 1);
            end
        
        // Reset
        always@(posedge clk)
            if (!$past(rstn))
                a9: assert(wptr == 0 && rptr == 0);
    `endif

endmodule