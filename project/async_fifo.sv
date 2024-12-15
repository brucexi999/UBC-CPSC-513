module ASYNC_FIFO #(
    parameter DEPTH = 8,
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

    //============================== Initials ===================================
    initial rptr = 0;
    initial rptr_gray_sync1 = 0;
    initial rptr_gray_sync2 = 0;
    initial wptr = 0;
    initial wptr_gray_sync1 = 0;
    initial wptr_gray_sync2 = 0;

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
        //always@($global_clock) begin
        //    assume($fell(wrstn) == $fell(rrstn));
        //    assume($rose(wrstn) == $rose(rrstn));
        //end

        always@($global_clock) begin
            assume (wrstn == rrstn);
        end
        
        // Assume the two resets are released synchronously with respect to their clocks
        //always@($global_clock) begin
        //    if(!($rose(wclk))) begin
        //        assume(!$rose(wrstn));
        //    end
            
        //    if(!($rose(rclk))) begin
        //        assume(!$rose(rrstn));
        //    end
        //end

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
        //        a25: assert(rptr == 0);
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
            if(past_valid_glb) begin
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

        //================================= Pointers ==================================
        logic [PTR_WIDTH-1:0] num_entry;  // Number of valid entries in the FIFO
        assign num_entry = wptr - rptr;

        initial assert(num_entry == 0);
        always@(*) begin
            assert(num_entry <= DEPTH);
        end

        always@(*) begin
            if (num_entry == DEPTH) begin
                assert(full);
            end
            if (num_entry == 0) begin
                assert(empty);
            end
        end

        always@(*) begin
            assert(wptr_gray == wptr ^ (wptr>>1));
            assert(rptr_gray == rptr ^ (rptr>>1));
        end

        //  No overflow
        always@($global_clock) begin
            //if($past(num_entry) == DEPTH && $past(wen) && past_valid_glb) begin
            if($past(full) && $past(wen) && past_valid_glb) begin
                assert(wptr == $past(wptr) || !wrstn);
            end
        end

        always@(*) begin
            if(wptr[PTR_WIDTH-1] != rptr[PTR_WIDTH-1]) begin
                assert(wptr[PTR_WIDTH-2:0] <= rptr[PTR_WIDTH-2:0]);
            end
        end

        // No underflow
        always@($global_clock) begin
            //if($past(num_entry) == 0 && $past(ren) && past_valid_glb) begin
            if($past(empty)&& $past(ren) && past_valid_glb) begin
                assert(rptr == $past(rptr) || !rrstn);
            end
        end

        always@(*) begin
            if(wptr[PTR_WIDTH-1] == rptr[PTR_WIDTH-1]) begin
                assert(rptr[PTR_WIDTH-2:0] <= wptr[PTR_WIDTH-2:0]);
            end
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
            if(!rrstn) begin
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

        logic [PTR_WIDTH-1:0] num_entry_r2w, num_entry_w2r;
        
        assign num_entry_r2w = wptr - rptr_sync2;
        assign num_entry_w2r = wptr_sync2 - rptr;

        always@(*) begin
            assert(num_entry_r2w <= DEPTH);
            assert(num_entry_w2r <= DEPTH);
        end

        always@(*) begin
            if(wptr_gray == {~rptr_gray_sync2[PTR_WIDTH-1:PTR_WIDTH-2], rptr_gray_sync2[PTR_WIDTH-3:0]}) begin
                assert(full);
            end
            if(rptr_gray == wptr_gray_sync2) begin
                assert(empty);
            end
        end

        //=================================== W/R =====================================
        (* anyconst *) logic [PTR_WIDTH-1:0] first_addr;
        logic [PTR_WIDTH-1:0] second_addr;
        assign second_addr = first_addr + 1;

        (* anyconst *) logic [WIDTH-1:0] first_data;
        logic [WIDTH-1:0] second_data;
        assign second_data = first_data + 1;

        logic first_addr_valid, second_addr_valid;
        
        always@(*) begin
            first_addr_valid = 0;
            if((wptr > rptr) && (first_addr < wptr) && (first_addr >= rptr)) begin
                first_addr_valid = 1;
            end
            else if((wptr < rptr) && (first_addr < wptr)) begin
                first_addr_valid = 1;
            end
            else if((wptr < rptr) && (first_addr >= rptr)) begin
                first_addr_valid = 1;
            end 
        end

        always@(*) begin
            second_addr_valid = 0;
            if((wptr > rptr) && (second_addr < wptr) && (second_addr >= rptr)) begin
                    second_addr_valid = 1;
            end
            else if((wptr < rptr) && (second_addr < wptr)) begin
                    second_addr_valid = 1;
            end
            else if((wptr < rptr) && (second_addr >= rptr)) begin
                    second_addr_valid = 1;
            end 
        end

        logic first_in_fifo, second_in_fifo, both_in_fifo;
        // For the first data to be in the FIFO, its address must be valid and its value
        // must match the data in the FIFO's mem at that address
        assign first_in_fifo = first_addr_valid && (mem[first_addr[PTR_WIDTH-2:0]] == first_data);
        assign second_in_fifo = second_addr_valid && (mem[second_addr[PTR_WIDTH-2:0]] == second_data);
        assign both_in_fifo = first_in_fifo && second_in_fifo;

        /*
        If both data are in the FIFO, then the FIFO can remain in that state indefinitely, 
        or alternatively a read request can read the first data from the FIFO. Then, the 
        FIFO can wait with the second value in memory indefinitely or it can be read out
        */

        logic wait_first_read, wait_second_read, read_first, read_second;
        
        /* 
        Intuitively, if both data are in the FIFO, then it shouldn't be empty. However,
        this can happen becuase it takes two extre read cycles for the write pointer to 
        travel to the read domain and produce the empty flag. During this time, there 
        could be data being written in the write domain.
        */

        assign wait_first_read = both_in_fifo && (!ren || rptr != first_addr || empty);
        assign read_first = ren && (rdata == first_data) && !empty && rptr == first_addr && both_in_fifo;
        assign wait_second_read = second_in_fifo && (!ren || empty) && (rptr == second_addr);
        assign read_second = ren && (rdata == second_data) && !empty && (rptr == second_addr) && second_in_fifo;

        always@($global_clock) begin
            // Refer to line 153 for why it's wrstn instead of rrstn
            if(past_valid_glb && wrstn) begin
                if($past(wait_first_read)) begin
                    assert(wait_first_read || ($rose(rclk) && read_first));
                end
                if($past(read_first)) begin
                    assert((!$rose(rclk) && read_first) || ($rose(rclk) && read_second) || wait_second_read);
                end
                if($past(wait_second_read)) begin
                    assert(wait_second_read || ($rose(rclk) && read_second));
                end
            end
        end

    `endif

endmodule