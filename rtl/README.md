# Overview
This directory contains all the synthesisable RTL files.

All the parameters regarding the design can be found inside the `params.sv` file. Note that only a subset of them are tunable, as mentioned in the comments inside the file. Also, within the file there are some scalar parameters, which are not actively used by this repo, until the superscalar core is also released.

Any structs and macros used in the vector datapath can be found inside the `vmacros.sv` and `vstructs.sv` files respectively.

### Vector Datapath

The following table lists the major units in the vector datapath and their operation

|  Vector Unit Name  | Details                                                                                                  |
|:----------------:|-----------------------------------------------------------------------------------------------------|
| vrrm             | The Register Remap stage, responsible for the register grouping and allocation.                     |
| vis              | The Issue stage, responsible for hazard tracking and operand selection. It is based around a scoreboard.|
| vex              | The execution stage, containing the vector lanes and surround logic and connection.                     |
| vex_pipe         | The main execution lane, containing the different execution units.                                      |
| vmu              | The vector memory unit, containing sub-engines handling different memory accesses and arbitration logic for those engines. |
| vmu_ld_eng       | The load engine of the memory unit. |
| vmu_st_eng       | The store engine of the memory unit. |
| vmu_tp_eng       | The region prefetch engine of the memory unit, used in tangem with custom instructions to accelerate image loading from memory. |

The list of the curently supported operations (custom instructions are denoted with italic fonts):

|  Memory Operations  | Integer Operations  |
|:-------------------:|:-------------------:|
|  vfld               |vadd                 |
|  vflh               |vaddi                |
|  vflsd              |vaddw                |
|  vflsh              |vaddiw               |
|  vflsw              |vsub                 |
|  vflw               |vsubw                |
|  vflxd              |vmul                 |
|  vflxh              |vmulh                |
|  vflxw              |vmulhsu              |
|  vlb                |vmulhu               |
|  vlbu               |vmulwdn              |
|  vld                |vdiv                 |
|  vlh                |vdivu                |
|  vlhu               |vrem                 |
|  vlsb               |vremu                |
|  vlsbu              |vsll                 |
|  vlsd               |vslli                |
|  vlsw               |vsra                 |
|  vlswu              |vsrai                |
|  vlw                |vsrl                 |
|  vlwu               |vsrli                |
|  vlxb               |vand                 |
|  vlxbu              |vandi                |
|  vlxd               |vor                  |
|  vlxh               |vori                 |
|  vlxh               |vxor                 |
|  vlxhu              |vxori                |
|  vlxhu              |vseq                 |
|  vlxw               |vslt                 |
|  vlxwu              |vsltu                |
|  vsb                |vrelu                |
|  vsd                |vstep                |
|  vsh                |vbrelu               |
|  vssb               |vprelu               |
|  vssd               |vradd                |
|  vssh               |vrand                |
|  vssw               |vror                 |
|  vsw                |vrxor                |
|  vsxb               |                     |
|  vsxd               |                     |
|  vsxh               |                     |
|  vsxub              |                     |
|  vsxud              |                     |
|  vsxuh              |                     |
|  vsxuw              |                     |
|  vsxw               |                     |
|  *vtplcfg*          |                     |
|  *vtpl*             |                     |







































