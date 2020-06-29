module mips(reset,clk);		//top level module, no input to this system is needed(except reset and clk)
input reset, clk;

wire[4:0] rd,rt,rs,RD,ID_EX_rsout,ID_EX_rtout,ID_EX_RDout,ID_EX_rsin,ID_EX_rtin,ID_EX_RDin,EX_MEM_RDout,
EX_MEM_RDin,MEM_WB_RDout,MEM_WB_RDin;
wire[31:0] instr, in_A, in_B, Bus_A, Bus_B, busW, Extender_out, Decider_out, data_out, data_in, alu_out, Addr,
IF_ID_instrout,IF_ID_PCout,IF_ID_instrin,IF_ID_PCin,ID_EX_instrout,ID_EX_PCout,ID_EX_immout,
ID_EX_Bus_Aout,ID_EX_Bus_Bout,ID_EX_instrin,ID_EX_PCin,ID_EX_immin,ID_EX_Bus_Ain,ID_EX_Bus_Bin,EX_MEM_ALUResultout,EX_MEM_ALUResultin,
EX_MEM_instrout,EX_MEM_Bus_Bout,EX_MEM_instrin,EX_MEM_Bus_Bin,MEM_WB_ALUresultout,MEM_WB_instrin,
MEM_WB_ALUresultin,MEM_WB_DMout,MEM_WB_DMin,MEM_WB_instrout,outputPC,ori_B,beq_A,beq_B;
wire RegDst, ALUsrc, MemtoReg, RegWr, MemWr, nPC_sel, is_J, zero,Flush_IF_ID,ID_EX_RegWrout,ID_EX_ALUsrcout,
ID_EX_MemtoRegout,ID_EX_MemWrout,ID_EX_RegWrin,ID_EX_ALUsrcin,ID_EX_MemtoRegin,ID_EX_MemWrin,EX_MEM_RegWrout,
EX_MEM_MemtoRegout,EX_MEM_MemWrout,EX_MEM_RegWrin,EX_MEM_MemtoRegin,EX_MEM_MemWrin,MEM_WB_RegWrout,
MEM_WB_MemtoRegout,MEM_WB_RegWrin,MEM_WB_MemtoRegin,PC_write_enable,IF_ID_write_enable,ID_EX_DonotRefreshin,ID_EX_DonotRefreshout;
wire[1:0] ALUctr, ExtOp,ID_EX_ALUctrout,ID_EX_ALUctrin,forwardA,forwardB,forwardSW;
wire[2:0] forwardBEQA,forwardBEQB;

assign RD = (RegDst)?rd:rt;			//when RegDst = 1, rd = rd; when RegDst = 0, rd = rt;

assign in_A = (forwardA[1:1])?EX_MEM_ALUResultout:(forwardA[0:0])?busW:ID_EX_Bus_Aout;

assign ori_B = (ID_EX_ALUsrcout)?ID_EX_immout:ID_EX_Bus_Bout;		//when ALU_src = 0 use register[rt], else use extended imm
assign in_B = (forwardB[1:1])?EX_MEM_ALUResultout:(forwardB[0:0])?busW:ori_B;
assign zero = (beq_A == beq_B);
assign beq_A = (forwardBEQA[2:2])?alu_out:(forwardBEQA[1:1])?EX_MEM_ALUResultout:(forwardBEQA[0:0])?busW:Bus_A;
assign beq_B = (forwardBEQB[2:2])?alu_out:(forwardBEQB[1:1])?EX_MEM_ALUResultout:(forwardBEQB[0:0])?busW:Bus_B;

assign busW = (MEM_WB_MemtoRegout)?MEM_WB_DMout:MEM_WB_ALUresultout;		//determines whether data_out or alu_out will be RF's input
assign data_in = EX_MEM_Bus_Bout;
assign Addr = EX_MEM_ALUResultout;

//assign syntax for latches connection with segments: IF/ID
assign IF_ID_instrin = instr;
assign IF_ID_PCin = outputPC;

//assign syntax for latches connection with segments: ID/EX
assign ID_EX_instrin = IF_ID_instrout;
assign ID_EX_PCin = IF_ID_PCout;
assign ID_EX_rsin = rs;
assign ID_EX_rtin = rt;
assign ID_EX_RDin = RD;
assign ID_EX_immin = Extender_out;
assign ID_EX_Bus_Ain = Bus_A;
assign ID_EX_Bus_Bin = Bus_B;
assign ID_EX_RegWrin = RegWr;
assign ID_EX_ALUsrcin = ALUsrc;
assign ID_EX_ALUctrin = ALUctr;
assign ID_EX_MemtoRegin = MemtoReg;
assign ID_EX_MemWrin = MemWr;
assign ID_EX_DonotRefreshin = (nPC_sel && zero) || is_J;

//assign syntax for latches connection with segments: EX/MEM
assign EX_MEM_instrin = ID_EX_instrout;
assign EX_MEM_RDin = ID_EX_RDout;
assign EX_MEM_ALUResultin = alu_out;
assign EX_MEM_Bus_Bin = (forwardSW[1:1])?EX_MEM_ALUResultout:(forwardSW[0:0])?MEM_WB_ALUresultout:ID_EX_Bus_Bout;
assign EX_MEM_RegWrin = ID_EX_RegWrout;
assign EX_MEM_MemtoRegin = ID_EX_MemtoRegout;
assign EX_MEM_MemWrin = ID_EX_MemWrout;

//assign syntax for latches connection with segments: MEM/WB
assign MEM_WB_instrin = EX_MEM_instrout;
assign MEM_WB_RDin = EX_MEM_RDout;
assign MEM_WB_RegWrin = EX_MEM_RegWrout;
assign MEM_WB_MemtoRegin = EX_MEM_MemtoRegout;
assign MEM_WB_ALUresultin = EX_MEM_ALUResultout;
assign MEM_WB_DMin = data_out;

//instantiation here
ControlUnit c1(rs, rt, rd, RegDst, RegWr, ALUsrc, ALUctr, MemtoReg, MemWr, ExtOp, nPC_sel, is_J, IF_ID_instrout);
ALU a1(alu_out, in_A, in_B, ID_EX_ALUctrout);																
IFU i1(instr, outputPC, reset, nPC_sel, zero, clk, is_J, IF_ID_instrout, IF_ID_PCout,PC_write_enable,ID_EX_DonotRefreshout);
DM d1(data_out, data_in, clk, EX_MEM_MemWrout, Addr);
RF r1(Bus_A, Bus_B, clk, MEM_WB_RegWrout, MEM_WB_RDout, rs, rt, busW, reset);
Extender e1(Extender_out, ExtOp, IF_ID_instrout);

IF_ID ifid1(IF_ID_instrout,IF_ID_PCout,IF_ID_instrin,IF_ID_PCin,clk,Flush_IF_ID,reset,IF_ID_write_enable);

ID_EX idex1(ID_EX_instrout,ID_EX_PCout,ID_EX_rsout,ID_EX_rtout,ID_EX_RDout,ID_EX_immout,
ID_EX_Bus_Aout,ID_EX_Bus_Bout,ID_EX_RegWrout,ID_EX_ALUsrcout,
ID_EX_ALUctrout,ID_EX_MemtoRegout,ID_EX_MemWrout,ID_EX_DonotRefreshout,ID_EX_DonotRefreshin,ID_EX_instrin,ID_EX_PCin,ID_EX_rsin,ID_EX_rtin,ID_EX_RDin,
ID_EX_immin,ID_EX_Bus_Ain,ID_EX_Bus_Bin,ID_EX_RegWrin,ID_EX_ALUsrcin,
ID_EX_ALUctrin,ID_EX_MemtoRegin,ID_EX_MemWrin,clk,reset);

EX_MEM exmem1(EX_MEM_instrout,EX_MEM_RDout,EX_MEM_ALUResultout,EX_MEM_Bus_Bout,EX_MEM_RegWrout,
EX_MEM_MemtoRegout,EX_MEM_MemWrout,EX_MEM_instrin,EX_MEM_RDin,EX_MEM_ALUResultin,EX_MEM_Bus_Bin,
EX_MEM_RegWrin,EX_MEM_MemtoRegin,EX_MEM_MemWrin,clk,reset);

MEM_WB memwb1(MEM_WB_instrout,MEM_WB_RDout,MEM_WB_RegWrout,MEM_WB_MemtoRegout,MEM_WB_ALUresultout,MEM_WB_DMout,
MEM_WB_instrin,MEM_WB_RDin,MEM_WB_RegWrin,MEM_WB_MemtoRegin,MEM_WB_ALUresultin,MEM_WB_DMin,clk,reset);

Forwarding_unit fu1(forwardBEQA,forwardBEQB,forwardSW,forwardA, forwardB, ID_EX_rsout, ID_EX_rtout, EX_MEM_RDout,
EX_MEM_RegWrout, MEM_WB_RDout, MEM_WB_RegWrout,ID_EX_instrout,EX_MEM_instrout,MEM_WB_instrout,rs,rt,ID_EX_RDout);

HazardDetectionUnit hdu1(Flush_IF_ID,PC_write_enable,IF_ID_write_enable,ID_EX_instrout,rs,rt,ID_EX_RDout,IF_ID_instrout);

endmodule

	
																						
module ControlUnit(rs, rt, rd, RegDst, RegWr, ALUsrc, ALUctr, MemtoReg, MemWr, ExtOp, nPC_sel, is_J, instr);
input[31:0] instr;
output[4:0] rs, rd, rt;
output[1:0] ExtOp, ALUctr;
output RegDst, RegWr, MemtoReg, ALUsrc, MemWr, nPC_sel, is_J;

wire lui, ori, lw, sw, addu, subu, beq, j, Rtype;

//judge all instructions:
assign lui = ~instr[31:31] & ~instr[30:30] & instr[29:29] & instr[28:28] & instr[27:27] & instr[26:26];
assign Rtype = ~instr[31:31] & ~instr[30:30] & ~instr[29:29] & ~instr[28:28] & ~instr[27:27] & ~instr[26:26];
assign sw = instr[31:31] & ~instr[30:30] & instr[29:29] & ~instr[28:28] & instr[27:27] & instr[26:26];
assign lw = instr[31:31] & ~instr[30:30] & ~instr[29:29] & ~instr[28:28] & instr[27:27] & instr[26:26];
assign ori = ~instr[31:31] & ~instr[30:30] & instr[29:29] & instr[28:28] & ~instr[27:27] & instr[26:26];
assign beq = ~instr[31:31] & ~instr[30:30] & ~instr[29:29] & instr[28:28] & ~instr[27:27] & ~instr[26:26];
assign j = ~instr[31:31] & ~instr[30:30] & ~instr[29:29] & ~instr[28:28] & instr[27:27] & ~instr[26:26];
assign addu = Rtype & instr[0] & ~instr[1] & ~instr[2] & ~instr[3] & ~instr[4] & instr[5];
assign subu = Rtype & instr[0] & instr[1] & ~instr[2] & ~instr[3] & ~instr[4] & instr[5];

//control signals:
assign rs = instr[25:21];
assign	rt = instr[20:16];
assign rd = instr[15:11];
		
assign ExtOp[0:0] = lw | sw;  //lw and sw set to 1, else 0; default 0
assign ExtOp[1:1] = lui;

assign ALUctr[0:0] = subu;    //subu 1, else 0
assign ALUctr[1:1] = ori;     //ori 1 --- or operation

assign MemtoReg = lw;
assign MemWr = sw;
assign RegWr = lw | Rtype | ori | lui;
assign RegDst = Rtype;
assign ALUsrc = ~Rtype;
assign nPC_sel = beq;
assign is_J = j;


endmodule



module ALU(alu_out, in_A, in_B, ALUctr);			//ALU
input[31:0] in_A, in_B;
input[1:0] ALUctr;					//opcode
output[31:0] alu_out;

wire isor,issub;
wire[31:0] temp_out, or_out, subu_out, addu_out;

assign isor = ALUctr[1:1];
assign issub = ALUctr[0:0];

assign alu_out = isor?or_out:temp_out;
assign or_out = in_A | in_B;
assign temp_out = issub?subu_out:addu_out;
assign subu_out = in_A - in_B;
assign addu_out = in_A + in_B;

endmodule



module IFU(instr, outputPC, reset, nPC_sel, zero, clk, is_J, jinstr, jPC,PC_write_enable,ID_EX_DonotRefreshout);
input nPC_sel, zero, clk, reset, is_J,PC_write_enable,ID_EX_DonotRefreshout;
input[31:0] jinstr,jPC;        //jinstr is for calculating the PC of beq and j
output[31:0] instr,outputPC;

reg[31:0] PC;
reg[7:0] im_byte_mem[1023:0];										//total instruction memory of 1KB

wire[17:0] imm_var;				//imm*4
wire branch_signal;				//check if to branch
wire[15:0] imm;					//last 16 bits of the instruction
wire[31:0] pcnew, pcbr, pctemp;

assign	instr = {im_byte_mem[PC[9:0]],im_byte_mem[PC[9:0]+1],im_byte_mem[PC[9:0]+2],im_byte_mem[PC[9:0]+3]};			//load the instruction
assign outputPC = pctemp;

assign imm = jinstr[15:0];
assign imm_var = {imm,2'b0};					//imm_var = imm * 4
assign branch_signal = zero & nPC_sel;		//when zero and nPC_sel are both 1 then branch

always@(posedge clk,posedge reset, posedge PC_write_enable)
begin
	if(reset)
		PC = 32'h0000_3000;
	else
	  begin
  if(!PC_write_enable)
    PC = pcnew;
  else if(PC_write_enable)
    PC = ID_EX_DonotRefreshout?PC:(PC-4);
  end
end

  assign pcnew = (is_J==0 && branch_signal==0)?pctemp:pcbr;
  assign pctemp = PC + 4;
  assign pcbr = (is_J==1)?{jPC[31:28],jinstr[25:0],2'b00}:jPC + PC_Extender(imm_var);

function[31:0] PC_Extender;
input[17:0] imm_in;																		//input is the imm*4
PC_Extender = (imm_in[17:17])?{14'b1,imm_in}:{14'b0,imm_in};				//signed extension
endfunction

endmodule



module RF(Bus_A, Bus_B, clk, RegWr, RD, rs, rt, busW, reset);					//register file
input clk, RegWr, reset;
input[4:0] RD, rs, rt;			
input[31:0] busW;						//busW is the value to be stored into registers
output[31:0] Bus_A, Bus_B;

reg[31:0] register[31:0];			//32registers

wire isOverwriteA,isOverwriteB;  //check if the output is to be modified in the same clk cycle

assign isOverwriteA = (rs==RD) && (rs!=0) && RegWr;
assign isOverwriteB = (rt==RD) && (rt!=0) && RegWr;

assign	Bus_A = (isOverwriteA)?busW:register[rs];
assign	Bus_B = (isOverwriteB)?busW:register[rt];

always@(posedge clk)
begin 
	if(reset)
	begin
	register[0] <= 32'b0;
	register[1] <= 32'b0;
	register[2] <= 32'b0;
	register[3] <= 32'b0;
	register[4] <= 32'b0;
	register[5] <= 32'b0;
	register[6] <= 32'b0;
	register[7] <= 32'b0;
	register[8] <= 32'b0;
	register[9] <= 32'b0;
	register[10] <= 32'b0;
	register[11] <= 32'b0;
	register[12] <= 32'b0;
	register[13] <= 32'b0;
	register[14] <= 32'b0;
	register[15] <= 32'b0;
	register[16] <= 32'b0;
	register[17] <= 32'b0;
	register[18] <= 32'b0;
	register[19] <= 32'b0;
	register[20] <= 32'b0;
	register[21] <= 32'b0;
	register[22] <= 32'b0;
	register[23] <= 32'b0;
	register[24] <= 32'b0;
	register[25] <= 32'b0;
	register[26] <= 32'b0;
	register[27] <= 32'b0;
	register[28] <= 32'b0;
	register[29] <= 32'b0;
	register[30] <= 32'b0;
	register[31] <= 32'b0;
	end
	if(RegWr && RD != 0)				//register0 should not be changed
	begin	
		register[RD] <= busW;			//write operation only happens when RegWr = 1 AND posedge clk both established
	end
	
end

endmodule



module DM(data_out, data_in, clk, MemWr, Addr);					//data memory
input[31:0] Addr;
input[31:0] data_in;
input clk, MemWr;
output[31:0] data_out;

reg[7:0] byte_mem[1023:0];										//total data memory of 1KB

wire[9:0] addr;

assign addr = Addr[9:0];

assign data_out = {byte_mem[addr], byte_mem[addr+1], byte_mem[addr+2], byte_mem[addr+3]};	
//the output of DM,big endianness

always@(posedge clk)
begin
	if(MemWr)
	begin
		byte_mem[addr] <= data_in[31:24];
		byte_mem[addr+1] <= data_in[23:16];
		byte_mem[addr+2] <= data_in[15:8];
		byte_mem[addr+3] <= data_in[7:0];
	end
	
end

endmodule



module Extender(Extender_out, ExtOp, instr);		//Extender for sign_extension,zero_extension and lui extension
input[1:0] ExtOp;
input[31:0] instr;
output[31:0] Extender_out;
reg[31:0] Extender_out;
wire[15:0] imm16;

assign imm16 = instr[15:0];

always@(*)
begin
case(ExtOp)
	2'b00: Extender_out <= {16'b0, imm16};
	2'b01: if(imm16[15:15])
	Extender_out <= {16'b1111111111111111, imm16};
	else
	Extender_out <= {16'b0, imm16};
	2'b10: Extender_out <= {imm16,16'b0};					//for lui to use
endcase
end
endmodule



module IF_ID(IF_ID_instrout,IF_ID_PCout,IF_ID_instrin,IF_ID_PCin,clk,Flush_IF_ID,reset,IF_ID_write_enable);
input[31:0] IF_ID_instrin,IF_ID_PCin;
input clk,Flush_IF_ID,reset,IF_ID_write_enable;
output[31:0] IF_ID_instrout,IF_ID_PCout;

reg[31:0] IF_ID_instr,IF_ID_PC;

assign IF_ID_instrout = IF_ID_instr;
assign IF_ID_PCout = IF_ID_PC;

always@(posedge clk,posedge reset, posedge Flush_IF_ID)
begin
  if(Flush_IF_ID)
    begin
      IF_ID_instr <= 32'b0;      //clear IF_ID if flush
      IF_ID_PC <= 32'b0;
    end
  if(reset)
    begin
      IF_ID_instr <= 32'b0;      //initialization on reset
      IF_ID_PC <= 32'b0;
    end
  else if(!IF_ID_write_enable)
    begin
      IF_ID_instr <= IF_ID_instrin;
      IF_ID_PC <= IF_ID_PCin;
    end  
end

endmodule



//the control signal of jump instructions will not go into this part, go directly back to IFU
//rs, rt, rd, RegWr, ALUsrc, ALUctr, MemtoReg, MemWr, nPC_sel, is_J, instr, zero, PC, imm, Bus_A, Bus_B
module ID_EX(ID_EX_instrout,ID_EX_PCout,ID_EX_rsout,ID_EX_rtout,ID_EX_RDout,ID_EX_immout,
ID_EX_Bus_Aout,ID_EX_Bus_Bout,ID_EX_RegWrout,ID_EX_ALUsrcout,
ID_EX_ALUctrout,ID_EX_MemtoRegout,ID_EX_MemWrout,ID_EX_DonotRefreshout,ID_EX_DonotRefreshin,ID_EX_instrin,ID_EX_PCin,ID_EX_rsin,ID_EX_rtin,ID_EX_RDin,
ID_EX_immin,ID_EX_Bus_Ain,ID_EX_Bus_Bin,ID_EX_RegWrin,ID_EX_ALUsrcin,
ID_EX_ALUctrin,ID_EX_MemtoRegin,ID_EX_MemWrin,clk,reset);

input ID_EX_RegWrin,ID_EX_ALUsrcin,ID_EX_MemtoRegin,ID_EX_MemWrin,clk,reset,ID_EX_DonotRefreshin;
input[1:0] ID_EX_ALUctrin;
input[31:0] ID_EX_immin,ID_EX_Bus_Ain,ID_EX_Bus_Bin,ID_EX_instrin,ID_EX_PCin; 
input[4:0] ID_EX_rsin,ID_EX_rtin,ID_EX_RDin;
output ID_EX_RegWrout,ID_EX_ALUsrcout,ID_EX_MemtoRegout,ID_EX_MemWrout,ID_EX_DonotRefreshout;
output[1:0] ID_EX_ALUctrout;
output[31:0] ID_EX_instrout,ID_EX_PCout,ID_EX_immout,ID_EX_Bus_Aout,ID_EX_Bus_Bout;
output[4:0] ID_EX_rsout,ID_EX_rtout,ID_EX_RDout;
  
reg ID_EX_is_J,ID_EX_RegWr,ID_EX_ALUsrc,ID_EX_MemtoReg,ID_EX_MemWr,ID_EX_DonotRefresh;  //zero given by RF
reg[1:0] ID_EX_ALUctr;
reg[31:0] ID_EX_imm,ID_EX_Bus_A,ID_EX_Bus_B,ID_EX_instr,ID_EX_PC;     //the imm here is already Extended
reg[4:0] ID_EX_rs,ID_EX_rt,ID_EX_RD;

assign ID_EX_RegWrout = ID_EX_RegWr;
assign ID_EX_ALUsrcout = ID_EX_ALUsrc;
assign ID_EX_MemtoRegout = ID_EX_MemtoReg;
assign ID_EX_MemWrout = ID_EX_MemWr;
assign ID_EX_ALUctrout = ID_EX_ALUctr;
assign ID_EX_immout = ID_EX_imm;
assign ID_EX_Bus_Aout = ID_EX_Bus_A;
assign ID_EX_Bus_Bout = ID_EX_Bus_B;
assign ID_EX_instrout = ID_EX_instr;
assign ID_EX_PCout = ID_EX_PC;
assign ID_EX_rsout = ID_EX_rs;
assign ID_EX_rtout = ID_EX_rt;
assign ID_EX_RDout = ID_EX_RD;
assign ID_EX_DonotRefreshout = ID_EX_DonotRefresh;

always@(posedge clk,posedge reset)            //refresh registers every clk cycle
begin
  if(reset)
    begin
      ID_EX_PC <= 32'b0;
      ID_EX_RegWr <= 1'b0;
      ID_EX_ALUsrc <= 1'b0;
      ID_EX_MemtoReg <= 1'b0;
      ID_EX_MemWr <= 1'b0;
      ID_EX_ALUctr <= 2'b0;
      ID_EX_imm <= 32'b0;
      ID_EX_Bus_A <= 32'b0;
      ID_EX_Bus_B <= 32'b0;
      ID_EX_instr <= 32'b0;
      ID_EX_rs <= 5'b0;
      ID_EX_rt <= 5'b0;
      ID_EX_RD <= 5'b0;
      ID_EX_DonotRefresh <= 1'b0;
    end
  else
    begin
      ID_EX_PC <= ID_EX_PCin;
      ID_EX_RegWr <= ID_EX_RegWrin;
      ID_EX_ALUsrc <= ID_EX_ALUsrcin;
      ID_EX_MemtoReg <= ID_EX_MemtoRegin;
      ID_EX_MemWr <= ID_EX_MemWrin;
      ID_EX_ALUctr <= ID_EX_ALUctrin;
      ID_EX_imm <= ID_EX_immin;
      ID_EX_Bus_A <= ID_EX_Bus_Ain;
      ID_EX_Bus_B <= ID_EX_Bus_Bin;
      ID_EX_instr <= ID_EX_instrin;
      ID_EX_rs <= ID_EX_rsin;
      ID_EX_rt <= ID_EX_rtin;
      ID_EX_RD <= ID_EX_RDin;
      ID_EX_DonotRefresh <= ID_EX_DonotRefreshin;
  end
end
endmodule



//rd, RegWr, MemtoReg, MemWr, instr, Bus_B, alu_out
module EX_MEM(EX_MEM_instrout,EX_MEM_RDout,EX_MEM_ALUResultout,EX_MEM_Bus_Bout,EX_MEM_RegWrout,
EX_MEM_MemtoRegout,EX_MEM_MemWrout,EX_MEM_instrin,EX_MEM_RDin,EX_MEM_ALUResultin,EX_MEM_Bus_Bin,
EX_MEM_RegWrin,EX_MEM_MemtoRegin,EX_MEM_MemWrin,clk,reset);
input[31:0] EX_MEM_instrin,EX_MEM_RDin,EX_MEM_ALUResultin,EX_MEM_Bus_Bin;
input[4:0] EX_MEM_RDin;
input EX_MEM_RegWrin,EX_MEM_MemtoRegin,EX_MEM_MemWrin,clk,reset;
output[31:0] EX_MEM_instrout,EX_MEM_ALUResultout,EX_MEM_Bus_Bout;
output[4:0] EX_MEM_RDout;
output EX_MEM_RegWrout,EX_MEM_MemtoRegout,EX_MEM_MemWrout;

reg[31:0] EX_MEM_instr,EX_MEM_ALUResult,EX_MEM_Bus_B;   //Bus_B is used for SW data_in
reg[4:0] EX_MEM_RD;
reg EX_MEM_RegWr,EX_MEM_MemtoReg,EX_MEM_MemWr;

assign EX_MEM_instrout = EX_MEM_instr;
assign EX_MEM_ALUResultout = EX_MEM_ALUResult;
assign EX_MEM_Bus_Bout = EX_MEM_Bus_B;
assign EX_MEM_RDout = EX_MEM_RD;
assign EX_MEM_RegWrout = EX_MEM_RegWr;
assign EX_MEM_MemtoRegout = EX_MEM_MemtoReg;
assign EX_MEM_MemWrout = EX_MEM_MemWr;

always@(posedge clk,posedge reset)
begin
  if(reset)
    begin
      EX_MEM_instr <= 32'b0;
      EX_MEM_ALUResult <= 32'b0;
      EX_MEM_Bus_B <= 32'b0;
      EX_MEM_RD <= 5'b0;
      EX_MEM_RegWr <= 1'b0;
      EX_MEM_MemtoReg <= 1'b0;
      EX_MEM_MemWr <= 1'b0;
    end
  else
    begin
      EX_MEM_instr <= EX_MEM_instrin;
      EX_MEM_ALUResult <= EX_MEM_ALUResultin;
      EX_MEM_Bus_B <= EX_MEM_Bus_Bin;
      EX_MEM_RD <= EX_MEM_RDin;
      EX_MEM_RegWr <= EX_MEM_RegWrin;
      EX_MEM_MemtoReg <= EX_MEM_MemtoRegin;
      EX_MEM_MemWr <= EX_MEM_MemWrin;
    end
end

endmodule



//rd, RegWr, MemtoReg, instr, alu_out
module MEM_WB(MEM_WB_instrout,MEM_WB_RDout,MEM_WB_RegWrout,MEM_WB_MemtoRegout,MEM_WB_ALUresultout,MEM_WB_DMout,
MEM_WB_instrin,MEM_WB_RDin,MEM_WB_RegWrin,MEM_WB_MemtoRegin,MEM_WB_ALUresultin,MEM_WB_DMin,clk,reset);
input[31:0] MEM_WB_instrin,MEM_WB_ALUresultin,MEM_WB_DMin;
input[4:0] MEM_WB_RDin;
input MEM_WB_RegWrin,MEM_WB_MemtoRegin,clk,reset;
output[31:0] MEM_WB_ALUresultout,MEM_WB_DMout,MEM_WB_instrout;
output[4:0] MEM_WB_RDout;
output MEM_WB_RegWrout,MEM_WB_MemtoRegout;

reg[31:0] MEM_WB_instr,MEM_WB_ALUresult,MEM_WB_DM;
reg[4:0] MEM_WB_RD;
reg MEM_WB_RegWr,MEM_WB_MemtoReg;

assign MEM_WB_instrout = MEM_WB_instr;
assign MEM_WB_ALUresultout = MEM_WB_ALUresult;
assign MEM_WB_RDout = MEM_WB_RD;
assign MEM_WB_RegWrout = MEM_WB_RegWr;
assign MEM_WB_MemtoRegout = MEM_WB_MemtoReg;
assign MEM_WB_DMout = MEM_WB_DM;            //the choose of DMout and alu_out is not to be done in this part

always@(posedge clk,posedge reset)
begin
  if(reset)
    begin
      MEM_WB_instr <= 32'b0;
      MEM_WB_ALUresult <= 32'b0;
      MEM_WB_RD <= 5'b0;
      MEM_WB_RegWr <= 1'b0;
      MEM_WB_MemtoReg <= 1'b0;
      MEM_WB_DM <= 32'b0;
    end
  else
    begin
     MEM_WB_instr <= MEM_WB_instrin;
     MEM_WB_ALUresult <= MEM_WB_ALUresultin;
     MEM_WB_RD <= MEM_WB_RDin;
     MEM_WB_RegWr <= MEM_WB_RegWrin;
     MEM_WB_MemtoReg <= MEM_WB_MemtoRegin;
     MEM_WB_DM <= MEM_WB_DMin;
    end
end

endmodule



//forwarding unit used to resolve data hazard
module Forwarding_unit(forwardBEQA,forwardBEQB,forwardSW,forwardA, forwardB, ID_EX_rsout, ID_EX_rtout, EX_MEM_RDout,
EX_MEM_RegWrout, MEM_WB_RDout, MEM_WB_RegWrout,ID_EX_instrout,EX_MEM_instrout,MEM_WB_instrout,rs,rt,ID_EX_RDout);
  input[31:0] ID_EX_instrout,EX_MEM_instrout,MEM_WB_instrout;
  input[4:0] ID_EX_rsout,ID_EX_rtout,EX_MEM_RDout,MEM_WB_RDout,ID_EX_RDout,rs,rt;
  input MEM_WB_RegWrout,EX_MEM_RegWrout;
  output[1:0] forwardA, forwardB, forwardSW;
  output[2:0] forwardBEQA,forwardBEQB;
  
  wire is_EX_MEM_A,is_EX_MEM_B,is_MEM_WB_A,is_MEM_WB_B,is_sw,is_SW_EX_MEM_B,is_SW_MEM_WB_B,
  is_sw_exmem,is_sw_memwb,is_beq_idex_A,is_beq_idex_B,is_beq_exmem_A,is_beq_exmem_B,
  is_beq_memwb_A,is_beq_memwb_B;
  
  assign is_beq_idex_A = (rs == ID_EX_RDout) && ~(ID_EX_RDout == 0) && ~is_sw;
  assign is_beq_idex_B = (rt == ID_EX_RDout) && ~(ID_EX_RDout == 0) && ~is_sw;
  assign is_beq_exmem_A = (rs == EX_MEM_RDout) && EX_MEM_RegWrout && ~(EX_MEM_RDout == 0) && ~is_sw_exmem;
  assign is_beq_exmem_B = (rt == EX_MEM_RDout) && EX_MEM_RegWrout && ~(EX_MEM_RDout == 0) && ~is_sw_exmem;
  assign is_beq_memwb_A = (rs == MEM_WB_RDout) && MEM_WB_RegWrout && ~(MEM_WB_RDout == 0) && ~is_sw_memwb;
  assign is_beq_memwb_B = (rt == MEM_WB_RDout) && MEM_WB_RegWrout && ~(MEM_WB_RDout == 0) && ~is_sw_memwb;
  
  assign is_sw = ID_EX_instrout[31:31] & ~ID_EX_instrout[30:30] & ID_EX_instrout[29:29] & ~ID_EX_instrout[28:28] & ID_EX_instrout[27:27] & ID_EX_instrout[26:26];
  assign is_sw_exmem = EX_MEM_instrout[31:31] & ~EX_MEM_instrout[30:30] & EX_MEM_instrout[29:29] & ~EX_MEM_instrout[28:28] & EX_MEM_instrout[27:27] & EX_MEM_instrout[26:26];
  assign is_sw_memwb = MEM_WB_instrout[31:31] & ~MEM_WB_instrout[30:30] & MEM_WB_instrout[29:29] & ~MEM_WB_instrout[28:28] & MEM_WB_instrout[27:27] & MEM_WB_instrout[26:26];

  assign is_EX_MEM_A = (ID_EX_rsout == EX_MEM_RDout) && EX_MEM_RegWrout && ~(EX_MEM_RDout == 0) && ~is_sw_exmem;
  assign is_EX_MEM_B = (ID_EX_rtout == EX_MEM_RDout) && EX_MEM_RegWrout && ~(EX_MEM_RDout == 0) && ~is_sw && ~is_sw_exmem;
  assign is_MEM_WB_A = (ID_EX_rsout == MEM_WB_RDout) && MEM_WB_RegWrout && ~(MEM_WB_RDout == 0) && ~is_sw_memwb;
  assign is_MEM_WB_B = (ID_EX_rtout == MEM_WB_RDout) && MEM_WB_RegWrout && ~(MEM_WB_RDout == 0) && ~is_sw && ~is_sw_memwb;
  
  assign is_SW_EX_MEM_B = (ID_EX_rtout == EX_MEM_RDout) && EX_MEM_RegWrout && ~(EX_MEM_RDout == 0);
  assign is_SW_MEM_WB_B = (ID_EX_rtout == MEM_WB_RDout) && MEM_WB_RegWrout && ~(MEM_WB_RDout == 0);
  
  assign forwardA[0:0] = ~is_EX_MEM_A && is_MEM_WB_A;
  assign forwardA[1:1] = is_EX_MEM_A;
  assign forwardB[0:0] = ~is_EX_MEM_B && is_MEM_WB_B;
  assign forwardB[1:1] =  is_EX_MEM_B;
  assign forwardSW[0:0] = ~is_SW_EX_MEM_B && is_SW_MEM_WB_B;
  assign forwardSW[1:1] = is_SW_EX_MEM_B;
  assign forwardBEQA[0:0] = is_beq_memwb_A;
  assign forwardBEQA[1:1] = is_beq_exmem_A;
  assign forwardBEQA[2:2] = is_beq_idex_A;
  assign forwardBEQB[0:0] = is_beq_memwb_B;
  assign forwardBEQB[1:1] = is_beq_exmem_B;
  assign forwardBEQB[2:2] =  is_beq_idex_B;
  
endmodule



module HazardDetectionUnit(Flush_IF_ID,PC_write_enable,IF_ID_write_enable,ID_EX_instrout,rs,rt,ID_EX_RDout,IF_ID_instrout);
  output Flush_IF_ID,PC_write_enable,IF_ID_write_enable;    //1 is disable and 0 is enable, Flush when 1
  input[31:0] ID_EX_instrout,IF_ID_instrout;
  input[4:0] rs,rt,ID_EX_RDout;
  
  wire load_use,jump,is_ID_EX_lw,is_register_overlap, is_ID_EX_j, is_ID_EX_beq,is_IF_ID_empty;
  
  assign is_IF_ID_empty = (IF_ID_instrout===32'b0);
  assign is_ID_EX_lw = ID_EX_instrout[31:31] & ~ID_EX_instrout[30:30] & ~ID_EX_instrout[29:29] & ~ID_EX_instrout[28:28] & ID_EX_instrout[27:27] & ID_EX_instrout[26:26];
  assign is_ID_EX_j = ~ID_EX_instrout[31:31] & ~ID_EX_instrout[30:30] & ~ID_EX_instrout[29:29] & ~ID_EX_instrout[28:28] & ID_EX_instrout[27:27] & ~ID_EX_instrout[26:26];
  assign is_ID_EX_beq = ~ID_EX_instrout[31:31] & ~ID_EX_instrout[30:30] & ~ID_EX_instrout[29:29] & ID_EX_instrout[28:28] & ~ID_EX_instrout[27:27] & ~ID_EX_instrout[26:26];
  assign is_register_overlap = (rs == ID_EX_RDout) || (rt == ID_EX_RDout);
  assign jump = (is_ID_EX_j || is_ID_EX_beq)  && ~is_IF_ID_empty;
  assign load_use = is_ID_EX_lw && is_register_overlap;
  
  assign IF_ID_write_enable = jump || load_use;
  assign PC_write_enable = jump || load_use;
  assign Flush_IF_ID = jump || load_use;
  
endmodule