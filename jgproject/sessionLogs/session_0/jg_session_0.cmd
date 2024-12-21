# ----------------------------------------
# Jasper Version Info
# tool      : Jasper 2024.06
# platform  : Linux 4.18.0-553.32.1.el8_10.x86_64
# version   : 2024.06p002 64 bits
# build date: 2024.09.02 16:28:38 UTC
# ----------------------------------------
# started   : 2024-12-20 21:16:04 EST
# hostname  : cadpc14.(none)
# pid       : 644945
# arguments : '-label' 'session_0' '-console' '//127.0.0.1:34005' '-style' 'windows' '-data' 'AAAAgnicY2RgYLCp////PwMYMD6A0Aw2jAyoAMRnQhUJbEChGRhYYZqRNUkxJDLkMJQyxDMUM6QylABZBQx6QDoZKAoCACSrDB4=' '-proj' '/homes/user/stud/fall24/tyc2118/FV_Final/jgproject/sessionLogs/session_0' '-init' '-hidden' '/homes/user/stud/fall24/tyc2118/FV_Final/jgproject/.tmp/.initCmds.tcl' 'alu_setup.tcl'
clear -all

analyze -sv09 alu.sv
elaborate -top alu

clock clk
reset ~rst_n
