module alu (input [15:0] inputA,
	    input [15:0] inputB,
            input [2:0] opcode,
	    input clk,
	    input rst_n,
            output reg [31:0] result,
	    output reg[1:0] overflow_flag   
);
	
	always @(*) begin
		case (opcode)
		    3'b000: result = inputA + inputB;  // ADD
		    3'b001: result = inputA * inputB;  // MULTIPLY
		    3'b010: result = inputA - inputB;  // SUBTRACT
		    3'b011: result = inputA & inputB;  // AND
		    3'b100: result = inputA | inputB;  // OR
		    3'b101: result = inputA ^ inputB;  // XOR
		    3'b110: result = ~inputA;          // NOT (only operates on inputA)
		    default: result = 32'b0;           // Default case
		endcase
    	end

	// Input validity assumption for opcode
	assume property (@(posedge clk) opcode inside {3'b000, 3'b001, 3'b010, 3'b011, 3'b100, 3'b101, 3'b110});

	// SVA properties
	property check_add;
	@(posedge clk) (opcode == 3'b000) |-> (result == inputA + inputB);
	endproperty

	property check_multiply;
	@(posedge clk) (opcode == 3'b001) |-> (result == inputA * inputB);
	endproperty

	property check_subtract;
	@(posedge clk) (opcode == 3'b010) |-> (result == inputA - inputB);
	endproperty

	property check_and;
	@(posedge clk) (opcode == 3'b011) |-> (result == (inputA & inputB));
	endproperty

	property check_or;
	@(posedge clk) (opcode == 3'b100) |-> (result == (inputA | inputB));
	endproperty

	property check_xor;
	@(posedge clk) (opcode == 3'b101) |-> (result == (inputA ^ inputB));
	endproperty

	property check_not;
	@(posedge clk) (opcode == 3'b110) |-> (result == ~inputA);
	endproperty

	property input_stability;
    @(posedge clk) disable iff (!rst_n)
    (opcode != 3'b000 && opcode != 3'b001 && opcode != 3'b010 && opcode != 3'b011 && opcode != 3'b100 && opcode != 3'b101 && opcode != 3'b110) |-> 
        (inputA == $past(inputA) && inputB == $past(inputB) && opcode == $past(opcode));
	endproperty

	property output_stability;
    @(posedge clk) disable iff (!rst_n)
    (opcode == 3'b000 || opcode == 3'b001 || opcode == 3'b010 || opcode == 3'b011 || opcode == 3'b100 || opcode == 3'b101 || opcode == 3'b110) |-> 
        (result == $past(result) && overflow_flag == $past(overflow_flag));
	endproperty




	// Assertions
	ADD_CHECK: assert property (check_add) else $error("ADD operation failed");
	MULTIPLY_CHECK:assert property (check_multiply) else $error("MULTIPLY operation failed");
	SUBTRACT_CHECK: assert property (check_subtract) else $error("SUBTRACT operation failed");
	AND_CHECK: assert property (check_and) else $error("AND operation failed");
	OR_CHECK: assert property (check_or) else $error("OR operation failed");
	XOR_CHECK: assert property (check_xor) else $error("XOR operation failed");
	NOT_CHECK: assert property (check_not) else $error("NOT operation failed");

	INPUT_STABILITY: assert property (input_stability) else $error("Inputs changed during valid operation!");
	OUTPUT_STABILITY: assert property (output_stability) else $error("Outputs changed unexpectedly!");



endmodule
