clear -all

check_sec -analyze -spec -sv alu.sv
check_sec -analyze -imp -sv structural_alu.sv
check_sec -elaborate -spec -top alu
check_sec -elaborate -imp -top structural_alu
check_sec -setup
check_sec -auto_map_reset_x_values on

clock clk
reset ~rst_n

#read_design alu.sv -golden
#read_design alu_structural.sv -revised

#set_inputs {inputA inputB opcode clk rst_n}
#set_outputs {result overflow_flag}
#set_reset rst_n
#set_clock clk
#set_equivalence_mode sequential

#run_equivalence
#write_report -file alu_sequential_equivalence_report.txt

