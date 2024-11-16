module SYNC_FIFO_TB;

    parameter DEPTH = 8;
    parameter WIDTH = 8; 

    logic wclk;
    logic wrstn;
    logic rclk;
    logic rrstn;

    logic [WIDTH-1:0] wdata;
    logic wen;
    logic full;
    
    logic [WIDTH-1:0] rdata;
    logic ren;
    logic empty;

    ASYNC_FIFO #(DEPTH, WIDTH) DUT (
        .*
    );

    initial begin
        wclk <= 0;
        wrstn <= 0;
        #35;
        wrstn <= 1;
        #1000;
        $stop;
    end

    always #5 wclk <= ~wclk;

    initial begin
        rclk <= 0;
        rrstn <= 0;
        #35;
        rrstn <= 1;
    end

    always #10 rclk <= ~rclk;

    initial begin
        // Write until full
        wen <= 0;
        wdata <= 0;

        #35;
        for (int i=0; i<DEPTH; i++) begin
            @(posedge wclk);
            wen <= 1;
            wdata <= i;
        end
        @(posedge wclk);
        wen <= 0;
        repeat(DEPTH-1) @(posedge rclk);

        // Random write
        for (int i=0; i<50; i++) begin
            @(posedge wclk);
            wen <= $urandom;
            wdata <= i;
        end
    end

    initial begin
        // read until empty
        ren <= 0;

        #35;
        repeat(DEPTH) @(posedge wclk);
        for (int i=0; i<DEPTH; i++) begin
            @(posedge rclk);
            ren <= 1;
        end

        // Random read
        for (int i=0; i<50; i++) begin
            @(posedge rclk);
            ren <= $urandom;
        end
    end

    initial begin
        $dumpfile("dump.vcd");
        $dumpvars;
    end

endmodule