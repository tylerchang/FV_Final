clear -all

check_sec -analyze -spec -sv alu_no_mul.sv
check_sec -analyze -imp -sv structural_alu.sv
check_sec -elaborate -spec -top alu
check_sec -elaborate -imp -top structural_alu
check_sec -setup
check_sec -auto_map_reset_x_values on
set_sec_autoprove_strategy basic

clock clk
reset ~rst_n

check_assumptions -task <embedded> -conflict
#check_sec -prove -bg
#check_sec -signoff -task <embedded>