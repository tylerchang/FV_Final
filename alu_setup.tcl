clear -all

analyze -sv09 alu.sv
elaborate -top alu

clock clk
reset ~rst_n
