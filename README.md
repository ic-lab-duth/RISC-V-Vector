# Overview

A configurable scalable Vector Datapath, tailored for the RISC-V ISA.

Features:
- Variable execution latency based on instruction type
- A register remapping scheme to support the RISC-V ISA's register groups and dynamic register file allocation
- A decoupled execution scheme that separates memory and computation instructions
- Hardware support for reduction operations


| ![vector_overview](/images/core_ppln.png) |
|:--:|
| *Overview of the Scalar and Vector pipelines* |

### Directory Hierarchy

The folder hierarchy is organised as follows:
- `images`: schematics and instruction mappings to microops
- `rtl` : contains all the synthesisable RTL files
- `sva` : contains related x-checks and assertions for the design
- `vector_simulator` : contains the TB to run a simulation with the Vector datapath, as well as some example stimulus.

## Repo State

- Support for Integer Arithmetic, Memory operations & Reduction operations
- Support for register grouping and dynamic register file allocation
- Decoupled execution between computational and memory instructions
- Current maximum vector lanes supported is 16.
- SVAs have been used in simulation only. No formal verification runs at the moment.

## Future Work
- Align to the newer versions of the RISC-V ISA 
- Replace MUL/DIV units with optimised hardware, to reduce execution latency and improve timing closure
- Decouple the vis<>vmu paths, which are currently very pressed for timing. Trials made in that area resulted in a much smaller footprint, due to the decompressed hardware
- Add back-pressure on the execution pipes, to allow for `vector_lanes > 16` configurations (Needed by the reduction tree to support more lanes)
- Add Floating point execution lanes


## The provided simulator
The repo at it's current stage contains the vector datapath, as well as a testbench that can be used to simulate payloads on it. The superscalar core is not provided yet, but will be released in the future. The hierarchy can be seen below:

_**TB Level Hierarchy:**_
->`vector_sim_top.sv` -> `vector_driver` & `vector_top`

|  Hierarchy Name  | Details                                                                                             |
|:----------------:|-----------------------------------------------------------------------------------------------------|
| vector_sim_top   | top level of the TB, instantiating the vector datapath and the scalar simulator. |
| vector_driver    | The TB driver that feeds the vector datapath with decoded vector instructions. |
| vector_top       | The top level of the vector datapath, as shown in figure 2. |
