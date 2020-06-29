`timescale 1 ps/ 1 ps
module test();

reg reset;
reg clk;
                  
mips m1 (reset, clk);

initial
begin
	clk =0; reset = 0;
	#5 reset = 1;
	#10 reset = 0;
	$readmemh("pipeline3.txt",m1.i1.im_byte_mem);
end

always  #10 clk = ~clk;
                                    
endmodule


