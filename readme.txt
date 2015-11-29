X18-32 CPU  By Arlet Ottens <arlet@c-scape.nl>


The X18 CPU is a small CPU core for FPGA control tasks. It is meant to run from 
Xilinx FPGA block RAM, exploiting the 2 extra parity bits for free extra opcode space.

It has 16 registers, and a small internal stack (not accessible for programs). It uses 
a Harvard architecture, but the code space is also accessible in the data space through
the use a dual port block RAM. 

Most instructions run single cycle, except memory loads/moves, which take two cycles. 
The barrel shifter operations also take two cycles, to allow extra pipelining and higher
clock rate. The same applies to the optional multiply instruction.

The project goals were:

- high code density
- minimal resources/simplicity
- high speed
- rich memory operations (auto inc/dec and copy)

Because the CPU is meant to be used for different control tasks inside an FPGA, it is 
hard to specify exactly what it needs to have. The simplicity of the design allows fairly
easily tailoring to a specific task where you can remove instructions you don't need, and
replace them with other ones. 

 Instruction format:

   17  16  15  14  13  12  11  10   9   8   7   6   5   4   3   2   1   0
  +---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+
  | 0 | 0 |   operation   |      dst      |              imm              | - alu imm
  +---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+
  | 0 | 1 | smode | dmode |      dst      |      src      |     offset    | - mov
  +---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+
  | 1 | 0 |   operation   |      dst      |      src      |    reserved   | - alu 
  +---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+
  | 1 | 1 | 0 | 0 |                     must be zero                      | - ret 
  +---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+
  | 1 | 1 | 0 | 1 |                        address                        | - call
  +---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+
  | 1 | 1 | 1 | 0 |                        address                        | - jump
  +---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+
  | 1 | 1 | 1 | 1 |    cond   |                     rel                   | - branch
  +---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+

 'operation' can be one of the following:

  two cycle operations (00--)
 
  0000 logical shift right
  0001 logical shift left
  0010 (multiply)
  0011 -- reserved

  single cycle operations

  0100 bitwise and
  0101 bitwise or
  0110 bitwise xor
  0111 -- reserved
  1000 bitwise invert
  1001 memory load
  1010 move 
  1011 byte swap
  1100 add
  1101 -- reserved
  1110 subtract
  1111 compare

  smode/dmode can be one of the following:

  00 direct register load/store ("mov reg, reg" not supported)
  01 indirect load/store (offset is added to base address)
  02 indirect load/store with pre-decrement
  03 indirect load/store with post-increment
  
  branch cond codes:

  000 BEQ 
  001 BNE 
  010 BCS
  011 BCC
  100 BMI
  101 BPL
  110 BLT (signed less than)
  111 BGE (signed greater or equal)
