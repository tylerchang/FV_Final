# ALU Verification

Verify ALU implementation to guarantee functional correctness using JasperGold.

## Installation

Requires access to JasperGold Formal Verification Platform [here](https://www.cadence.com/en_US/home/tools/system-design-and-verification/formal-and-static-verification.html).

## Usage

Run scripts to setup Jasper Environment and additionally open the Jasper GUI. 

`run_sec.sh` doesn't open the SEC app by default, so a new tab with the SEC app is needed before interacting with the SEC tool.

```bash
# Run Formal Verficaiton on alu.sv
./run.sh

# Runs Sequential Equivalence Checking between alu_no_mul.sv and structural_alu.sv
./run_sec.sh
```
