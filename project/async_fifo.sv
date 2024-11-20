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

    `ifdef FORMAL
        logic past_valid_glb, past_valid_w, past_valid_r;
        initial {past_valid_glb, past_valid_w, past_valid_r} = 0;
        always@($global_clock) begin
            past_valid_glb <= 1;
        end

        always@(posedge wclk) begin
            past_valid_w <= 1;
        end

        always@(posedge rclk) begin
            past_valid_r <= 1;
        end

        //============================== Initials ===================================
        initial rptr = 0;
        initial rptr_gray = 0;
        initial rptr_gray_sync1 = 0;
        initial rptr_gray_sync2 = 0;
        initial wptr = 0;
        initial wptr_gray = 0;
        initial wptr_gray_sync1 = 0;
        initial wptr_gray_sync2 = 0;
        initial full = 0;
        initial empty = 1;

        //================================ Clocks ====================================
        localparam WIDTH_CLK = 5;
        (* anyconst *) logic [WIDTH_CLK-1:0] wclk_step, rclk_step;

        always@(*) begin
            assume(wclk_step != 0);
            assume(rclk_step != 0);
        end            

        logic [WIDTH_CLK-1:0] wclk_ctr, rclk_ctr;

        always@($global_clock) begin
            wclk_ctr <= wclk_ctr + wclk_step;
            rclk_ctr <= rclk_ctr + rclk_step;
        end

        always@(*) begin
            assume(wclk == wclk_ctr[WIDTH_CLK-1]);
            assume(rclk == rclk_ctr[WIDTH_CLK-1]);
        end

        //================================ Resets ====================================

        // Initially, assume both resets are asserted
        initial assume(!wrstn);
        initial assume(!rrstn);
        //initial assume(rrstn == wrstn);
        // Assume the two resets are asserted simultaneously
        always@($global_clock) begin
            assume($fell(wrstn) == $fell(rrstn));
        end
        
        // Assume the two resets are released synchronously with respect to their clocks
        always@($global_clock) begin
            if(!($rose(wclk))) begin
                assume(!$rose(wrstn));
            end
            
            if(!($rose(rclk))) begin
                assume(!$rose(rrstn));
            end
        end

        /* 
        If wrstn is asserted, rrstn may have already been deasserted because the two 
        resets are not deasserted at the same time. What we are sure about is that 
        the read logic will be in the reset state and empty is 1. At this point, if 
        wrstn is still asserted, then the read pointer must remain as 0 because we 
        can't read anything without something being written first. The opposite is 
        not ture. If wrstn is deasserted prior than rrstn, then while rrstn is low, 
        the write pointer may have already incremented.
        */
        //always@($global_clock) begin
        //    if(!wrstn) begin
        //        assert(rptr == 0);
        //    end
        //end

        always@(*) begin
            // If past_valid_w is low, we treat it as reset
            if(!past_valid_w || !wrstn) begin  
                assume(!wen);
                assert(!full);
                assert(wptr == 0);
                assert(wptr_gray == 0);
                assert(rptr_gray_sync1 == 0);
                assert(rptr_gray_sync2 == 0);
                // These are signals in the read clock domain, refer to the comment
                // section above
                assert(wptr_gray_sync1 == 0);
                assert(wptr_gray_sync2 == 0);
                assert(rptr == 0);
                assert(empty);
            end

            if(!past_valid_r || !rrstn) begin
                assume(!ren);
                assert(rptr == 0);
                assert(rptr_gray == 0);
                assert(wptr_gray_sync1 == 0);
                assert(wptr_gray_sync2 == 0);

            end

        end

        //================================= Inputs ===================================
        always@($global_clock) begin
            if(past_valid) begin
                if(!$rose(wclk)) begin
                    assume($stable(wen));
                    assume($stable(wdata));
                    assert($stable(full) || !wrstn);  // Async reset
                end

                if(!$rose(rclk)) begin
                    assume($stable(ren));
                    // If the async reset comes in, then it must be empty
                    assert(empty || $stable(rdata));  
                    assert($stable(empty) || !rrstn);
                end
            end
        end

        //============================== W/R Operations ===============================
        logic [PTR_WIDTH-1:0] num_entry;  // Number of valid entries in the FIFO
        assign num_entry = wptr - rptr;

        initial assert(num_entry == 0);
        always@($global_clock) begin
            assert(num_entry <= DEPTH);
        end

        always@($global_clock) begin
            if (num_entry == DEPTH) begin
                assert(full);
            end
            if (num_entry == 0) begin
                assert(empty);
            end
        end

        always@(*) begin
            assert(wptr_gray == (wptr>>1)^wptr);
            assert(rptr_gray == (rptr>>1)^rptr);
        end

        logic [PTR_WIDTH-1:0] wptr_sync1, wptr_sync2, rptr_sync1, rptr_sync2;

        initial {wptr_sync1, wptr_sync2, rptr_sync1, rptr_sync2} = 0;

        always@(posedge wclk or negedge wrstn) begin
            if(!wrstn) begin
                {rptr_sync2, rptr_sync1} <= 0;
            end
            else begin
                {rptr_sync2, rptr_sync1} <= {rptr_sync1, rptr};
            end
        end

        always@(posedge rclk or negedge rrstn) begin
            if(!wrstn) begin
                {wptr_sync2, wptr_sync1} <= 0;
            end
            else begin
                {wptr_sync2, wptr_sync1} <= {wptr_sync1, wptr};
            end
        end

        always@(*) begin
            assert(rptr_gray_sync1 == (rptr_sync1>>1) ^ rptr_sync1);
            assert(rptr_gray_sync2 == (rptr_sync2>>1) ^ rptr_sync2);
            assert(wptr_gray_sync1 == (wptr_sync1>>1) ^ wptr_sync1);
            assert(wptr_gray_sync2 == (wptr_sync2>>1) ^ wptr_sync2);
        end

    `endif

endmodule