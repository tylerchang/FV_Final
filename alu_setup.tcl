clear -all

analyze -sv09 alu.sv
elaborate -top alu -bbox_mul 32

clock clk
reset ~rst_n
