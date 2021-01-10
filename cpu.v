

module cpu_design(
		input clk,             			// System Clock
		input reset,           			// System Reset
		input [0:31] instruction,		// Instruction from Instruction Memory
		input [0:63] dataIn,        // Data from Data Memory
		output [0:31] pc,						// Program counter output to Instr Memory
		output [0:63] dataOut,      // Write Data to Data Memory
		output [0:31] memAddr,      // Write Address for Data Memory
		output memEn,           		// Data Memory Enable
		output memWrEn              // Data Memory Write Enable
	);

	wire [0:31] instr;

	//instruction format variables
	wire [0:5] func, dp_func;
	wire [0:1] ww, dp_ww;
	wire [0:2] ppp, dp_ppp;
	wire [0:4] rA, rB, rD, dp_rA, dp_rB, dp_rD;
	wire [0:5] opcode, dp_opcode;
	wire [0:15] i_addr, dp_iaddr;

  wire [0:31] id_cntrl, dff_idcntrl;
	wire [0:15] id_iaddr, dff_iaddr;

	prog_cntr pc1 (.clk(clk), .reset(reset), .pc(pc));

	dff32x1 dff_cpu1 (.CLK(clk), .RST(reset), .D(instruction), .Q(instr));

	if_id_stage ifid (.clk(clk), .reset(reset), .instruction(instr), .func(func),
										.ww(ww), .ppp(ppp), .rA(rA), .rB(rB), .rD(rD),
										.opcode(opcode), .i_addr(i_addr));

	datapath dp (.clk(clk), .reset(reset), .func(func), .ww(ww), .ppp(ppp),
							 .rA(rA), .rB(rB), .rD(rD), .opcode(opcode),
							 .i_addr(i_addr), .dataIn(dataIn), .dataOut(dataOut),
							 .memAddr(memAddr), .memEn(memEn), .memWrEn(memWrEn));

endmodule

//
//dff32x1 module
//1 x 32-bit DFF
//
module dff32x1 (CLK, RST, D, Q);
	input CLK, RST;
  input [0:31] D;
	output reg [0:31] Q;

	always @ (posedge CLK) begin
		if (RST) begin
			Q <= 32'b0;
		end else begin
			Q <= D;
		end
	end
endmodule //end dff module






// ############################################################################################
// ALU



module alu (
		input clk,             // System Clock
		input reset,           // System Reset
		input [0:5] func,
		input [0:1] ww,
		input [0:4] shift_amount,
		input [0:63] din1      ,   // Data from stage reg
		input [0:63] din2      ,   // Data from stage reg
		output reg [0:63] aluout
	);

	always @(*) begin

		
			case (func)

				6'd0: aluout = din1 & din2;		// And rA and rB and store in rD				

				6'd1: aluout = din1 | din2;		// OR rA and rB and store in rD				

				6'd2: aluout = din1 ^ din2;		// XOR rA and rB and store in rD				

				6'd3: aluout = ~din1;			// NOT rA and store in rD				

				6'd4: aluout = din1;			// MOV rA and store in rD				

				6'd5: begin				// ADD rA and rB and store in rD

					case (ww)

						2'b00: begin

								aluout[0:7] = din1[0:7] + din2[0:7];
								aluout[8:15] = din1[8:15] + din2[8:15];
								aluout[16:23] = din1[16:23] + din2[16:23];
								aluout[24:31] = din1[24:31] + din2[24:31];
								aluout[32:39] = din1[32:39] + din2[32:39];
								aluout[40:47] = din1[40:47] + din2[40:47];
								aluout[48:55] = din1[48:55] + din2[48:55];
								aluout[56:63] = din1[56:63] + din2[56:63];

						end

						2'b01: begin

								aluout[0:15] = din1[0:15] + din2[0:15];
								aluout[16:31] = din1[16:31] + din2[16:31];
								aluout[32:47] = din1[32:47] + din2[32:47];
								aluout[48:63] = din1[48:63] + din2[48:63];

						end

						2'b10: begin

								aluout[0:31] = din1[0:31] + din2[0:31];
								aluout[32:63] = din1[32:63] + din2[32:63];

						end

						2'b11: aluout = din1 + din2;

					endcase
				end				

				6'd6: begin				// SUB rA and rB and store in rD

					case (ww)

						2'b00: begin

								aluout[0:7] = din1[0:7] + (8'b1 + ~din2[0:7]);
								aluout[8:15] = din1[8:15] + (8'b1 + ~din2[8:15]);
								aluout[16:23] = din1[16:23] + (8'b1 + ~din2[16:23]);
								aluout[24:31] = din1[24:31] + (8'b1 + ~din2[24:31]);
								aluout[32:39] = din1[32:39] + (8'b1 + ~din2[32:39]);
								aluout[40:47] = din1[40:47] + (8'b1 + ~din2[40:47]);
								aluout[48:55] = din1[48:55] + (8'b1 + ~din2[48:55]);
								aluout[56:63] = din1[56:63] + (8'b1 + ~din2[56:63]);

						end

						2'b01: begin

								aluout[0:15] = din1[0:15] + (8'b1 + ~din2[0:15]);
								aluout[16:31] = din1[16:31] + (8'b1 + ~din2[16:31]);
								aluout[32:47] = din1[32:47] + (8'b1 + ~din2[32:47]);
								aluout[48:63] = din1[48:63] + (8'b1 + ~din2[48:63]);

						end

						2'b10: begin

								aluout[0:31] = din1[0:31] + (8'b1 + ~din2[0:31]);
								aluout[32:63] = din1[32:63] + (8'b1 + ~din2[32:63]);

						end

						2'b11: aluout = din1 + (8'b1 + ~din2);

					endcase
				end

				6'd7: begin		// MUL even rA and rB and store in rD				

					case (ww)

						2'b00: begin

								aluout[0:15] = din1[0:7] * din2[0:7];
								aluout[16:31] = din1[16:23] * din2[16:23];
								aluout[32:47] = din1[32:39] * din2[32:39];
								aluout[48:63] = din1[48:55] * din2[48:55];

						end

						2'b01: begin

								aluout[0:31] = din1[0:15] * din2[0:15];
								aluout[32:63] = din1[32:47] * din2[32:47];

						end

						2'b10: aluout = din1[0:31] * din2[0:31];

						2'b11: aluout = din1[0:31] * din2[0:31];

					endcase

				end

				6'd8: begin		// MUL odd rA and rB and store in rD				

					case (ww)

						2'b00: begin

								aluout[0:15] = din1[8:15] * din2[8:15];
								aluout[16:31] = din1[24:31] * din2[24:31];
								aluout[32:47] = din1[40:47] * din2[40:47];
								aluout[48:63] = din1[56:63] * din2[56:63];

						end

						2'b01: begin

								aluout[0:31] = din1[16:31] * din2[16:31];
								aluout[32:63] = din1[48:63] * din2[48:63];

						end

						2'b10: aluout = din1[32:63] * din2[32:63];

						2'b11: aluout = din1[32:63] * din2[32:63];

					endcase

				end

				6'd9: begin				// ADD rA and rB and store in rD

					case (ww)

						2'b00: begin

								aluout[0:7] = {din1[4:7] , din1[0:3]};
								aluout[8:15] = {din1[12:15] , din1[8:11]};
								aluout[16:23] = {din1[20:23] , din1[16:19]};
								aluout[24:31] = {din1[28:31] , din1[24:27]};
								aluout[32:39] = {din1[36:39] , din1[32:35]};
								aluout[40:47] = {din1[44:47] , din1[40:43]};
								aluout[48:55] = {din1[52:55] , din1[48:51]};
								aluout[56:63] = {din1[60:63] , din1[56:59]};

						end

						2'b01: begin

								aluout[0:15] = {din1[8:15] , din1[0:7]};
								aluout[16:31] = {din1[24:31] , din1[16:23]};
								aluout[32:47] = {din1[40:47] , din1[32:39]};
								aluout[48:63] = {din1[56:63] , din1[48:55]};

						end

						2'b10: begin

								aluout[0:31] = {din1[16:31] , din1[0:15]};
								aluout[32:63] = {din1[48:63] , din1[32:47]};

						end

						2'b11: aluout = {din1[32:63] , din1[0:31]};

					endcase
				end			

				6'd10: begin		// shift left logical and store in rD				

					case (ww)

						2'b00: begin

								aluout[0:7] = din1[0:7] << din2[5:7];
								aluout[8:15] = din1[8:15] << din2[13:15];
								aluout[16:23] = din1[16:23] << din2[21:23];
								aluout[24:31] = din1[24:31] << din2[29:31];
								aluout[32:39] = din1[32:39] << din2[37:39];
								aluout[40:47] = din1[40:47] << din2[45:47];
								aluout[48:55] = din1[48:55] << din2[53:55];
								aluout[56:63] = din1[56:63] << din2[61:63];
								
						end

						2'b01: begin

								aluout[0:15] = din1[0:15] << din2[12:15];
								aluout[16:31] = din1[24:31] << din2[28:31];
								aluout[32:47] = din1[32:47] << din2[44:47];
								aluout[48:63] = din1[48:55] << din2[60:63];

						end

						2'b10: begin

								aluout[0:31] = din1[0:31] << din2[27:31];
								aluout[31:63] = din1[31:63] << din2[59:63];

						end

						2'b11: aluout = din1[0:63] << din2[58:63];

					endcase

				end

				6'd11: begin				// shift left immediate

					case (ww)

						2'b00: begin

								aluout[0:7] = din1[0:7] << shift_amount[2:4];
								aluout[8:15] = din1[8:15] << shift_amount[2:4];
								aluout[16:23] = din1[16:23] << shift_amount[2:4];
								aluout[24:31] = din1[24:31] << shift_amount[2:4];
								aluout[32:39] = din1[32:39] << shift_amount[2:4];
								aluout[40:47] = din1[40:47] << shift_amount[2:4];
								aluout[48:55] = din1[48:55] << shift_amount[2:4];
								aluout[56:63] = din1[56:63] << shift_amount[2:4];
							
						end

						2'b01: begin

								aluout[0:15] = din1[0:15] << shift_amount[1:4];
								aluout[16:31] = din1[16:31] << shift_amount[1:4];
								aluout[32:47] = din1[32:47] << shift_amount[1:4];
								aluout[48:63] = din1[48:63] << shift_amount[1:4];

						end

						2'b10: begin

								aluout[0:31] = din1[0:31] << shift_amount[0:4];
								aluout[32:63] = din1[32:63] << shift_amount[0:4];

						end

						2'b11: aluout[0:63] = din1[0:63] << shift_amount[0:4];

					endcase

				end

				6'd12: begin		// shift right logical and store in rD				

					case (ww)

						2'b00: begin

								aluout[0:7] = din1[0:7] >> din2[5:7];
								aluout[8:15] = din1[8:15] >> din2[13:15];
								aluout[16:23] = din1[16:23] >> din2[21:23];
								aluout[24:31] = din1[24:31] >> din2[29:31];
								aluout[32:39] = din1[32:39] >> din2[37:39];
								aluout[40:47] = din1[40:47] >> din2[45:47];
								aluout[48:55] = din1[48:55] >> din2[53:55];
								aluout[56:63] = din1[56:63] >> din2[61:63];
								
						end

						2'b01: begin

								aluout[0:15] = din1[0:15] >> din2[12:15];
								aluout[16:31] = din1[24:31] >> din2[28:31];
								aluout[32:47] = din1[32:47] >> din2[44:47];
								aluout[48:63] = din1[48:55] >> din2[60:63];

						end

						2'b10: begin

								aluout[0:31] = din1[0:31] >> din2[27:31];
								aluout[31:63] = din1[31:63] >> din2[59:63];

						end

						2'b11: aluout = din1[0:63] >> din2[58:63];

					endcase

				end

				6'd13: begin				// shift right immediate

					case (ww)

						2'b00: begin

								aluout[0:7] = din1[0:7] >> shift_amount[2:4];
								aluout[8:15] = din1[8:15] >> shift_amount[2:4];
								aluout[16:23] = din1[16:23] >> shift_amount[2:4];
								aluout[24:31] = din1[24:31] >> shift_amount[2:4];
								aluout[32:39] = din1[32:39] >> shift_amount[2:4];
								aluout[40:47] = din1[40:47] >> shift_amount[2:4];
								aluout[48:55] = din1[48:55] >> shift_amount[2:4];
								aluout[56:63] = din1[56:63] >> shift_amount[2:4];
							
						end

						2'b01: begin

								aluout[0:15] = din1[0:15] >> shift_amount[1:4];
								aluout[16:31] = din1[16:31] >> shift_amount[1:4];
								aluout[32:47] = din1[32:47] >> shift_amount[1:4];
								aluout[48:63] = din1[48:63] >> shift_amount[1:4];

						end

						2'b10: begin

								aluout[0:31] = din1[0:31] >> shift_amount[0:4];
								aluout[32:63] = din1[32:63] >> shift_amount[0:4];

						end

						2'b11: aluout[0:63] = din1[0:63] >> shift_amount[0:4];

					endcase

				end

				6'd14: begin		// shift right arithmetic and store in rD				

					case (ww)

						2'b00: begin

								aluout[0:7] = $signed(din1[0:7]) >>> din2[5:7];
								aluout[8:15] = $signed(din1[8:15]) >>> din2[13:15];
								aluout[16:23] = $signed(din1[16:23]) >>> din2[21:23];
								aluout[24:31] = $signed(din1[24:31]) >>> din2[29:31];
								aluout[32:39] = $signed(din1[32:39]) >>> din2[37:39];
								aluout[40:47] = $signed(din1[40:47]) >>> din2[45:47];
								aluout[48:55] = $signed(din1[48:55]) >>> din2[53:55];
								aluout[56:63] = $signed(din1[56:63]) >>> din2[61:63];
								
						end

						2'b01: begin

								aluout[0:15] = $signed(din1[0:15]) >>> din2[12:15];
								aluout[16:31] = $signed(din1[24:31]) >>> din2[28:31];
								aluout[32:47] = $signed(din1[32:47]) >>> din2[44:47];
								aluout[48:63] = $signed(din1[48:55]) >>> din2[60:63];

						end

						2'b10: begin

								aluout[0:31] = $signed(din1[0:31]) >>> din2[27:31];
								aluout[31:63] = $signed(din1[31:63]) >>> din2[59:63];

						end

						2'b11: aluout = $signed(din1[0:63]) >>> din2[58:63];

					endcase

				end

				6'd15: begin				// shift right immediate

					case (ww)

						2'b00: begin

								aluout[0:7] = $signed(din1[0:7]) >>> shift_amount[2:4];
								aluout[8:15] = $signed(din1[8:15]) >>> shift_amount[2:4];
								aluout[16:23] = $signed(din1[16:23]) >>> shift_amount[2:4];
								aluout[24:31] = $signed(din1[24:31]) >>> shift_amount[2:4];
								aluout[32:39] = $signed(din1[32:39]) >>> shift_amount[2:4];
								aluout[40:47] = $signed(din1[40:47]) >>> shift_amount[2:4];
								aluout[48:55] = $signed(din1[48:55]) >>> shift_amount[2:4];
								aluout[56:63] = $signed(din1[56:63]) >>> shift_amount[2:4];
							
						end

						2'b01: begin

								aluout[0:15] = $signed(din1[0:15]) >>> shift_amount[1:4];
								aluout[16:31] = $signed(din1[16:31]) >>> shift_amount[1:4];
								aluout[32:47] = $signed(din1[32:47]) >>> shift_amount[1:4];
								aluout[48:63] = $signed(din1[48:63]) >>> shift_amount[1:4];

						end

						2'b10: begin

								aluout[0:31] = $signed(din1[0:31]) >>> shift_amount[0:4];
								aluout[32:63] = $signed(din1[32:63]) >>> shift_amount[0:4];

						end

						2'b11: begin
								aluout[0:63] = $signed(din1) >>> shift_amount[0:4];
						end
					endcase

				end
			default: aluout = 0;
			endcase

	end

endmodule






// ##################################################################################################################
// DATAPATH


//
//datapath module
//
module datapath(
		input clk,             // System Clock
		input reset,           // System Reset
		input [0:5] func,
		input [0:1] ww,
		input [0:2] ppp,
		input [0:4] rA, rB, rD,
		input [0:5] opcode,
		input [0:15] i_addr,
		input [0:63] dataIn,          // Data from Data Memory
		output [0:63] dataOut,        // Write Data to Data Memory
		output [0:31] memAddr,    		// Write Effective Address for Data Memory
		output memEn,				          // Data Memory Enable
		output memWrEn                // Data Memory Write Enable
	);

	wire [0:63] rfout1, dff_rfout1, rfout2, dff_rfout2, alu_out, wb_out;
	wire [0:63] dff_alu1out1, dff_alu1out2;

	wire [0:1] ex_ww, wb_ww;
	wire [0:4] ex_shft, ex_rD;
	wire [0:5] ex_func;
	wire [0:5] ex_opcode, wb_opcode;
	wire [0:15] ex_iaddr;

	wire wb_rfwren;
	wire [0:1] wb_sel;
	wire [0:2] wb_ppp;
	wire [0:4] wb_rD;

	//control signals
	wire [0:31] cpu_cntrl1, dff_rf2out, dff_ex1out;
	wire [0:15] cpu_cntrl2, dff_rf3out, dff_ex2out;


  //----------------------------------------------------------------------------
  //RF Stage

	//RF instantiation
	reg_file RF (.clk(clk), .reset(reset), .WrEn(wb_rfwren), .ww(wb_ww), .ppp(wb_ppp),
							 .rDaddr(wb_rD), .rAaddr(rA), .rBaddr(rB), .din(wb_out),
							 .dout1(rfout1), .dout2(rfout2));

	//----------------------------------------------------------------------------
 	//RF -> EX/MEM Stage Registers

  //RF dff for data out signals
 	dff64x2 dff_rf1 (.CLK(clk), .RST(reset), .D1(rfout1), .D2(rfout2),
 									 .Q1(dff_rfout1), .Q2(dff_rfout2));

	//control signals (func, ww, ppp, rA, rB, rD, opcode)
	dff32x1 dff_rf2 (.CLK(clk), .RST(reset), .D(cpu_cntrl1), .Q(dff_rf2out));

	//control signals (i_addr)
	dff16x1 dff_rf3 (.CLK(clk), .RST(reset), .D(cpu_cntrl2), .Q(dff_rf3out));

	//----------------------------------------------------------------------------
	//EX/MEM Stage

  //ALU instantiation
	alu alu1 (.clk(clk), .reset(reset), .func(ex_func), .ww(ex_ww),
						.shift_amount(ex_shft), .din1(dff_rfout1), .din2(dff_rfout2),
						.aluout(alu_out));

  //MEM instantiation
	MEM_signals mem1 (.opcode(ex_opcode), .i_addr(ex_iaddr), .memEn(memEn),
										.memWrEn(memWrEn), .EA(memAddr));

	//----------------------------------------------------------------------------
	//EX/MEM -> WB Stage Registers

  //EX dff for ALU data out signal
	dff64x2 dff_alu1 (.CLK(clk), .RST(reset), .D1(alu_out), .D2(dataIn),
									 .Q1(dff_alu1out1), .Q2(dff_alu1out2));

	//control signals (func, ww, ppp, rA, rB, rD, opcode)
	dff32x1 dff_ex1 (.CLK(clk), .RST(reset), .D(dff_rf2out), .Q(dff_ex1out));

	//control signals (i_addr)
	dff16x1 dff_ex2 (.CLK(clk), .RST(reset), .D(dff_rf3out), .Q(dff_ex2out));

	//----------------------------------------------------------------------------
	//WB Stage

	//MEM instantiation
	WB_stage wb1 (.wb_sel(wb_sel), .alu_in(dff_alu1out1), .noc_in(dff_alu1out2),
								.memin(dataIn),	.wb_dout(wb_out));

	//----------------------------------------------------------------------------
	//ID Signal Control

	//ID control signals (Buffer inputs)
	assign cpu_cntrl1 = {func, ww, ppp, rA, rB, rD, opcode};
	assign cpu_cntrl2 = i_addr;

	//EX/MEM stage assignments
	assign ex_func = dff_rf2out[0:5];				//func at EX stage
	assign ex_ww = dff_rf2out[6:7];					//ww at EX stage
	assign ex_shft = dff_rf2out[16:20];			//rB at EX stage
	assign ex_rD = dff_rf2out[21:25];				//rD at EX stage
	assign ex_opcode = dff_rf2out[26:31];		//opcode at EX stage
	assign ex_iaddr = dff_rf3out;						//iaddr to EX stage

	//WB stage assignments
	assign wb_ww = dff_ex1out[6:7];					//ww to RF module
	assign wb_ppp = dff_ex1out[8:10];				//ppp to RF module
	assign wb_rD = dff_ex1out[21:25];				//rD to RF module
	assign wb_opcode = dff_ex1out[26:31];		//opcode to wb_sel and wb_rfwren logic

	assign wb_sel[0] = (wb_opcode == 6'b100000 || wb_opcode == 6'b100010) ? 1'b1 : 1'b0;
	assign wb_sel[1] = (wb_opcode == 6'b100000) ? 1'b1 : 1'b0;

	assign wb_rfwren = (wb_opcode == 6'b101010 || wb_opcode == 6'b100000 ||
									 		wb_opcode == 6'b100010) ? 1'b1 : 1'b0;

	//----------------------------------------------------------------------------
	//Data Memory Output
	assign dataOut = dff_rfout1;							//rA output from RF dff

endmodule

//
//RF module
//3-port (2 rd, 1 wr), Asynchronous reads, Synchronous writes
//32 64-bit registers
//
module reg_file(
		input clk,            	// System Clock
		input reset,          	// System Reset
		input WrEn,         		// RF Write Enable
		input [0:1] ww,					// RF WW (word width)
		input [0:2] ppp,     	 	// RF PPP (participation)
		input [0:4] rDaddr,   	// Write Address for RF (rD)
		input [0:4] rAaddr,    	// Read Address for RF (rA)
		input [0:4] rBaddr,    	// Read Address for RF (rB)
		input [0:63] din,     	// Data from write back
		output [0:63] dout1,   	// Write Data 1 to stage reg
		output [0:63] dout2     // Write Data 1 to stage reg
	);

	integer i;
	reg [0:6] width;							// word width (based on ww)

	// Memory Declaration
	reg [0:63] rf_mem[0:31];		// 64-bit wide, 32-deep memory

	// Asynchronous READ Operation
	//assign dout1 = WrEn ? 64'bz : rf_mem[rAaddr];  //set to z if writing
	//assign dout2 = WrEn ? 64'bz : rf_mem[rBaddr];  //set to z if writing

	assign dout1 = rf_mem[rAaddr];
	assign dout2 = rf_mem[rBaddr];
	
	always @ (posedge clk) begin
		//$display($time," rf_mem0=%h, rf_mem1=%h, rf_mem2=%h, rf_mem3=%h, ", rf_mem[0], rf_mem[1], rf_mem[2], rf_mem[3]);
		//$display($time," rf_mem28=%h, rf_mem29=%h, rf_mem30=%h, rf_mem32=%h, ", rf_mem[28], rf_mem[29], rf_mem[30], rf_mem[31]);

		if (reset) begin
			//clear entire RF
			for (i=0; i<32; i=i+1) begin
				rf_mem[i] = 64'b0;
			end
		end else if (WrEn && rDaddr != 5'b0) begin
			case (ppp)
				3'b000: begin rf_mem[rDaddr][0:63] = din[0:63]; end //end case 3'b000
				3'b001: begin rf_mem[rDaddr][0:31] = din[0:31]; end //end case 3'b001
				3'b010: begin rf_mem[rDaddr][32:63] = din[32:63]; end //end case 3'b010
				3'b011: begin
						
										//if (i%2 == 0) begin
											//rf_mem[rDaddr][i+:width] <= din[i+:width];
											if (width == 7'd8) begin
												for(i=0;i<64;i=i+16) begin
													rf_mem[rDaddr][i+:8] = din[i+:8];
													end
											end else if (width == 7'd16) begin
											    for(i=0;i<64;i=i+32) begin
													rf_mem[rDaddr][i+:16] = din[i+:16];
													end
											end else if (width == 7'd32) begin
												for(i=0;i<64;i=i+64) begin
													rf_mem[rDaddr][i+:32] = din[i+:32];
													end
											end else if (width == 7'd64) begin
												for(i=0;i<64;i=i+128) begin
													rf_mem[rDaddr][i+:64] = din[i+:64];
													end
											end //end if-else
										//end //end if
									
								end //end case 3'b011
				3'b100: begin
									
										//if (i%2 != 0) begin
											//rf_mem[rDaddr][i+:width] <= din[i+:width];
											if (width == 7'd8) begin
												for (i=8; i<64; i=i+(2*8)) begin
													rf_mem[rDaddr][i+:8] = din[i+:8];
												end
											end else if (width == 7'd16) begin
												for (i=16; i<64; i=i+(2*16)) begin
													rf_mem[rDaddr][i+:16] = din[i+:16];
												end
											end else if (width == 7'd32) begin
												for (i=32; i<64; i=i+(2*32)) begin
													rf_mem[rDaddr][i+:32] = din[i+:32];
												end
											end else if (width == 7'd64) begin
												for (i=64; i<64; i=i+(2*64)) begin
													rf_mem[rDaddr][i+:64] = din[i+:64];
												end
											end //end if-else
										//end //end if
								end //end case 3'b100
				default: begin rf_mem[rDaddr][0:63] = din[0:63]; end //end case default
			endcase
		end //end if-else
	end //end always

	always @ (*) begin
		if (reset) begin
			width = 7'd0;
		end else if (ww == 2'b00) begin
			width = 7'd8;
		end else if (ww == 2'b01) begin
			width = 7'd16;
		end else if (ww == 2'b10) begin
			width = 7'd32;
		end else if (ww == 2'b11) begin
			width = 7'd64;
		end else begin
			width = 7'd0;
		end //end if-else
	end //end always

endmodule

//
//dff8x1 module
//1 x 8-bit DFF
//
module dff8x1 (CLK, RST, D, Q);
	input CLK, RST;
  input [0:7] D;
	output reg [0:7] Q;

	always @ (posedge CLK) begin
		if (RST) begin
			Q <= 8'b0;
		end else begin
			Q <= D;
		end
	end
endmodule //end dff module

//
//dff16x1 module
//1 x 16-bit DFF
//
module dff16x1 (CLK, RST, D, Q);
	input CLK, RST;
  input [0:15] D;
	output reg [0:15] Q;

	always @ (posedge CLK) begin
		if (RST) begin
			Q <= 16'b0;
		end else begin
			Q <= D;
		end
	end
endmodule //end dff module

//
//dff64x1 module
//1 x 64-bit DFF with enable
//
module dff64x1_L (CLK, RST, EN, D, Q);
	input CLK, RST, EN;
  input [0:63] D;
	output reg [0:63] Q;

	always @ (posedge CLK) begin
		if (RST) begin
			Q <= 64'b0;
		end else if (EN) begin
			Q <= D;
		end
	end
endmodule //end dff module

//
//dff64x2 module
//2 x 64-bit DFF
//
module dff64x2 (CLK, RST, D1, D2, Q1, Q2);
	input CLK, RST;
  input [0:63] D1, D2;
	output reg [0:63] Q1, Q2;

	always @ (posedge CLK) begin
		if (RST) begin
			Q1 <= 64'b0;
			Q2 <= 64'b0;
		end else begin
			Q1 <= D1;
			Q2 <= D2;
		end
	end
endmodule //end dff module





//###########################################################################################################
// DECODE CONTROL



//
//prog_cntr module
//increases counter by 4 every clk cycle
//
module prog_cntr(
		input clk,        	 // System Clock
		input reset,         // System Reset
		output [0:31] pc 		 // Instruction Address
	);

	reg [0:31] cntr;

	assign pc = cntr;

	always @ (posedge clk) begin
		if (reset) begin
			// clear counter
			cntr <= 32'b0;
		end else begin
			//increment cntr by 4 every clk cycle
			cntr <= cntr + 4;
		end //end if
	end //end always
endmodule

//
//instr_dec_cntrl module
//decode instructions and send control signals to execute said instruction
//sends control signals to datapath (where instr gets executed)
//
//instr format has two types (R-type and M-type)
//not all R-types are the same (rB can be register specifier or 5-bit immediate)
//
module if_id_stage(
		input clk,             // System Clock
		input reset,           // System Reset
		input [0:31] instruction, 		// Instruction from Instruction Memory
		output reg [0:5] func,
		output reg [0:1] ww,
		output reg [0:2] ppp,
		output reg [0:4] rA, rB, rD,
		output reg [0:5] opcode,
		output reg [0:15] i_addr
	);

	always @ (*) begin
		if (reset) begin
			// clear control signals
			func = 6'b000000;
			ww = 2'b00;
			ppp = 3'b000;
			rA = 5'b00000;
			rB = 5'b00000;
			rD = 5'b00000;
			opcode = 6'b000000;
			i_addr = 16'b0000_0000_0000_0000;

		//All others instructions are NOP
		end	else if (instruction[0:5] == 6'b111100) begin
			func = 6'b0;
			ww = 2'b0;
			ppp = 3'b0;
			rA = 5'b0;
			rB = 5'b0;
			rD = 5'b0;
			opcode = 6'b111100;
			i_addr = 16'b0;
		end	else if (instruction[0:5] == 6'b101010) begin
			opcode = instruction[0:5];
			rD = instruction[6:10];
			rA = instruction[11:15];
			rB = instruction[16:20];
			ppp = instruction[21:23];
			ww = instruction[24:25];
			func = instruction[26:31];
			i_addr = 16'bz;
		end	else if (instruction[0:5] == 6'b100000) begin
			opcode = instruction[0:5];
			rD = instruction[6:10];
			rA = 5'bz;
			rB = 5'bz;
			ppp = 3'bz;
			ww = 2'bz;
			func = 6'bz;
			i_addr = instruction[16:31];
		end	else if (instruction[0:5] == 6'b100001) begin
			opcode = instruction[0:5];
			rD = 5'bz;
			rA = instruction[6:10];
			rB = 5'bz;
			ppp = 3'bz;
			ww = 2'bz;
			func = 6'bz;
			i_addr = instruction[16:31];
		end else if(instruction[0:5] == 6'b100010) begin //Special Operation for receiving the data from CPU
			opcode = instruction[0:5];
			rD = instruction[6:10];
			rA = 5'bz;
			rB = 5'bz;
			ppp = 3'bz;
			ww = 2'bz;
			func = 6'bz;
			i_addr = instruction[16:31];
		end	else if(instruction[0:5] == 6'b100011) begin //Special Operation for sending data out from CPU
			opcode = instruction[0:5];
			rD = 5'bz;
			rA = instruction[6:10];
			rB = 5'bz;
			ppp = 3'bz;
			ww = 2'bz;
			func = 6'bz;
			i_addr = instruction[16:31];
		end	else begin
			func = 6'b0;
			ww = 2'b0;
			ppp = 3'b0;
			rA = 5'b0;
			rB = 5'b0;
			rD = 5'b0;
			opcode = 6'b111100;
			i_addr = 16'b0;
		end

	end //end always
endmodule






//##############################################################################################################################
// MEMORY & WB




module MEM_signals(opcode, i_addr, memEn, memWrEn, EA);
	input [0:5] opcode;
	input [0:15] i_addr;
	output reg memEn, memWrEn;
	output reg [0:31] EA;

	always @ (*) begin
		if(opcode == 6'b100000 || opcode == 6'b100001) begin
			memEn = 1'b1;
			EA = {16'b0,i_addr};
			if(opcode == 6'b100001) begin
				memWrEn = 1'b1;
			end else begin
				memWrEn = 1'b0;
			end //end if-else
		end	else if (opcode == 6'b100010) begin
			memEn = 1'b0;
			memWrEn= 1'b0;
			EA = {16'hffff,i_addr};	//EA for flit read from buffer
		end	else if (opcode == 6'b100011) begin
			memEn = 1'b0;
			memWrEn= 1'b0;
			EA = {16'haaaa,i_addr};	//EA for flit write to buffer
		end	else begin
			memEn = 1'b0;
			memWrEn = 1'b0;
			EA = 32'b0;
		end //end if-else
	end //end always
endmodule

module WB_stage(wb_sel, alu_in, noc_in, memin, wb_dout);
	input [0:63] alu_in, noc_in, memin;
	input [0:1] wb_sel;
	output [0:63] wb_dout;

	assign wb_dout = wb_sel[1] ? (wb_sel[0] ? memin : 64'bz) :
															 (wb_sel[0] ? noc_in : alu_in) ;

endmodule
