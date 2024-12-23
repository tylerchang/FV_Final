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


	// Opcode Formatting
	assume property (@(posedge clk) opcode inside {3'b000, 3'b001, 3'b010, 3'b011, 3'b100, 3'b101, 3'b110});
	
	// Ensure inputA and inputB to be 16 bits
	assume property (@(posedge clk) $bits(inputA) == 16);
	assume property (@(posedge clk) $bits(inputB) == 16);


	// Functional Correctness
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
    @(posedge clk) (opcode != 3'b111) |-> (inputA == $past(inputA) && inputB == $past(inputB) && opcode == $past(opcode));
	endproperty

	property output_stability;
    @(posedge clk) (opcode == 3'b111) |-> result == $past(result);
	endproperty

	property input_transition_validity;
    @(posedge clk) $rose(opcode) |-> $stable(inputA) && $stable(inputB);
	endproperty

	property output_transition_validity;
    @(posedge clk) ($changed(opcode)) |-> result == $past(result);
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
	INPUT_TRANSITION_STABILITY: assert property (input_transition_validity) else $error("Inputs transitioned unexpectedly!");
	OUTPUT_TRANSITION_STABILITY: assert property (output_transition_validity) else $error("Outputs transitioned unexpectedly!");



endmodule
