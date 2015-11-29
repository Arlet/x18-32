/*
 * cpu X18
 *
 * Copyright (C) Arlet Ottens <arlet@c-scape.nl>
 *
 * Instruction format:
 *
 *   17  16  15  14  13  12  11  10   9   8   7   6   5   4   3   2   1   0
 *  +---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+
 *  | 0 | 0 |   operation   |      dst      |              imm              | - alu imm
 *  +---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+
 *  | 0 | 1 | smode | dmode |      dst      |      src      |     offset    | - mov
 *  +---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+
 *  | 1 | 0 |   operation   |      dst      |      src      |    reserved   | - alu 
 *  +---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+
 *  | 1 | 1 | 0 | 0 |                     must be zero                      | - ret 
 *  +---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+
 *  | 1 | 1 | 0 | 1 |                        address                        | - call
 *  +---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+
 *  | 1 | 1 | 1 | 0 |                        address                        | - jump
 *  +---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+
 *  | 1 | 1 | 1 | 1 |    cond   |                     rel                   | - branch
 *  +---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+
 *
 * 'operation' can be one of the following:
 *
 *  two cycle operations (00--)
 * 
 *  0000 logical shift right
 *  0001 logical shift left
 *  0010 multiply
 *  0011 -- reserved
 *
 *  single cycle operations
 *
 *  0100 bitwise and
 *  0101 bitwise or
 *  0110 bitwise xor
 *  0111 -- reserved
 *  1000 bitwise invert
 *  1001 memory load
 *  1010 move 
 *  1011 byte swap
 *  1100 add
 *  1101 -- reserved
 *  1110 subtract
 *  1111 compare
 *
 *  smode/dmode can be one of the following:
 *
 *  00 direct register load/store ("mov reg, reg" not supported)
 *  01 indirect load/store (offset is added to base address)
 *  02 indirect load/store with pre-decrement
 *  03 indirect load/store with post-increment
 *  
 *  branch cond codes:
 *
 *  000 BEQ 
 *  001 BNE 
 *  010 BCS
 *  011 BCC
 *  100 BMI
 *  101 BPL
 *  110 BLT (signed less than)
 *  111 BGE (signed greater or equal)
 *
 */


module x18( 
    input clk,                  // clock input
    input reset,                // active high reset
    output [31:0] addr,         // external address bus (16k * 32 bit)
    input [31:0] di,            // data input
    output [31:0] do,           // data output
    output oe,                  // output enable
    output we,                  // write enable
    input iowait );             // add wait state when iowait=1 

reg [13:0] pc = 0;              // program counter
wire [17:0] ir;                 // instruction register

/*
 * IR fields decoded:
 */
wire alu0    = ir[16]    == 1'b0;       // any ALU-based instruction, including imm/alu2
wire alu2    = ir[16:14] == 3'b000;     // 2 cycle ALU instruction
wire imm0    = ir[17:16] == 2'b00;      // immediate instruction
wire mov0    = ir[17:16] == 2'b01;      // move from/to memory, or mem-mem copy
wire ret0    = ir[17:14] == 4'b1100;    // return 
wire call0   = ir[17:14] == 4'b1101;    // subroutine call
wire jump0   = ir[17:14] == 4'b1110;    // unconditional jump
wire branch0 = ir[17:14] == 4'b1111;    // conditional branch
wire brk0    = ir == 18'h3ffff;         // all ones = simulator brk

wire [2:0]  cond0   = ir[13:11];        // condition code
wire [3:0]  sreg0   = ir[7:4];          // source register number
wire [3:0]  dreg0   = ir[11:8];         // destination register number
wire [7:0]  immval0 = ir[7:0];          // 8-bit immediate value
wire [3:0]  op0     = ir[15:12];        // ALU operation
wire [1:0]  smode0  = ir[15:14];        // source mode of mov instruction
wire [1:0]  dmode0  = ir[13:12];        // destination mode of mov instruction
wire [10:0] rel0    = ir[10:0];         // branch offset
wire [13:0] addr0   = ir[13:0];         // jump/call address
wire [3:0]  offset0 = ir[3:0];          // memory offset

parameter 
    MODE_REG = 2'd0,                    // register load/store
    MODE_IND = 2'd1,                    // indirect load/store with 4 bit offset
    MODE_DEC = 2'd2,                    // indirect load/store with pre-decrement
    MODE_INC = 2'd3;                    // indirect load/store with post-increment

wire ld0   = mov0 & (smode0 != MODE_REG);
wire st0   = mov0 & (smode0 == MODE_REG);

/* 
 * internal state
 */
parameter
    EXEC  = 3'd0,                       // normal execution cycle
    ALU2  = 3'd1,                       // wait for 2 cycle ALU
    LOAD  = 3'd2,                       // load from memory
    STORE = 3'd3,                       // store 
    JMP1  = 3'd4,                       // 1st cycle of a PC-changing instruction
    JMP2  = 3'd5;                       // 2nd cycle of a PC-changing instruction

reg [2:0] state;                        // current cycle state
reg [2:0] next;                         // next cycle state

parameter
    // first 4 opcodes are all double cycle
    ALU_LSR = 4'b0000,                  // logical shift right
    ALU_LSL = 4'b0001,                  // logical shift left
    ALU_MUL = 4'b0010,                  // multiply
    ALU_3   = 4'b0011,                  // reserved for 2 cycle op

    // the rest are all single cycle
    ALU_AND = 4'b0100,                  // bitwise and
    ALU_OR  = 4'b0101,                  // bitwise or
    ALU_XOR = 4'b0110,                  // bitwise xor
    ALU_7   = 4'b0111,                  // reserved (bitwise clear)

    ALU_INV = 4'b1000,                  // bitwise invert
    ALU_MEM = 4'b1001,                  // memory load
    ALU_MOV = 4'b1010,                  // direct move 
    ALU_SWP = 4'b1011,                  // swap bytes

    ALU_ADD = 4'b1100,                  // add
    ALU_13  = 4'b1101,                  // reserved (add with carry ?) 
    ALU_SUB = 4'b1110,                  // subtract
    ALU_CMP = 4'b1111;                  // compare 

parameter
    COND_EQ = 3'd0,                     // branch when Z=1
    COND_NE = 3'd1,                     // branch when Z=0
    COND_CS = 3'd2,                     // branch when C=1 (unsigned greater/equal)
    COND_CC = 3'd3,                     // branch when C=0 (unsigned less then)
    COND_MI = 3'd4,                     // branch when N=1
    COND_PL = 3'd5,                     // branch when N=0
    COND_LT = 3'd6,                     // branch when N != V (signed less then)
    COND_GE = 3'd7;                     // branch when N == V (signed less then)

/*
 * ALU related
 */

reg  [2:0] cond;                        // condition codes
reg  [3:0] alu_op;
reg [31:0] immval;                      // immediate value used as ALU input
reg [32:0] alu_out;                     // extra bit for carry out
reg [32:0] alu_hold;                    // copy of alu_out
wire z = ~|alu_hold[31:0];              // zero flag 
wire c = alu_hold[32];                  // carry out
wire n = alu_hold[31];                  // negative flag
reg v31;                                // overflow bit
wire lt = v31 ^ c;                      // less-than flag
wire ci = 0;                            // carry in, not used
reg alu;                                // alu operation
reg imm;                                // immediate operand
wire [31:0] oper;                       // alu operand

/*
 * condition codes and branches
 */
reg cond_true;                          // branch condition is true
reg branch;                             // true if testing for branch
reg [13:0] target;                      // branch target

/* 
 * register file
 */

reg [31:0] regfile[0:15];               // register file memory
reg cmp;                                // doing compare instruction (don't write back)
reg [3:0] rd_reg;                       // read-only address in register file
reg [3:0] rw_reg;                       // read/write address in register file
wire [31:0] src = regfile[rd_reg];      // source register contents 
wire [31:0] dst = regfile[rw_reg];      // destination register contents

/*
 * stack
 */
reg [13:0] stack[0:15];                 // 16 deep stack
reg [3:0] sp_reg = 0;                   // stack pointer register
wire [3:0] sp = call0 ? sp_reg : sp_reg - 1;

/*
 * memory 
 */
reg mem2mem;                            // doing memory-memory moves
wire [31:0] rd_mem_data;                // data read from memory
wire [31:0] wr_mem_data = mem2mem ? (rd_mem_data | di) : src;
reg mem_wr_enable = 0;                  // memory write enable
reg [31:0] mem_addr = 0;                // memory address
reg [31:0] mem_offset = 0;              // memory address offset

// external memory interface
assign oe = (state == LOAD);
assign do = wr_mem_data;
assign addr = mem_addr;
assign we = mem_wr_enable;

wire sel_internal = (mem_addr[31:9] == 0);

RAMB16_S18_S36 code_data( 
        .CLKA(clk),
        .ENA( (next != LOAD) & (next != ALU2) & ~iowait ),
        .WEA(1'b0),
        .SSRA(1'b0),
        .ADDRA(pc[9:0]),
        .DOA(ir[15:0]),
        .DOPA(ir[17:16]),

        // copy of code memory is available at address 0

        .CLKB(clk),
        .ENB(1'b1),
        .WEB(1'b0),                     // read only
        .SSRB(~sel_internal),
        .ADDRB(mem_addr[8:0]),
        .DIB(wr_mem_data),
        .DIPB(4'b0),
        .DOB(rd_mem_data)
        );

`include "code.v"

integer i;

initial
    for( i = 0; i < 16; i = i + 1 )
        regfile[i] = 0;

/*
 * mem2mem indicates we're doing a memory-memory move.
 * This is true if both smode and dmode are not registers.
 */ 
always @(posedge clk)
    if( ~iowait )
        mem2mem <= (smode0 != MODE_REG) & (dmode0 != MODE_REG); 

/*
 * memory write enable, destination must not be a register,
 * and must be a store instruction, or the 2nd cycle of a
 * load/store.
 */
always @(posedge clk)
    if( ~iowait )
        mem_wr_enable <= (next == STORE) & (dmode0 != MODE_REG);

/*
 * always read from the source register. 
 */
always @(posedge clk)
    if( ~iowait )
        rd_reg <= sreg0;

/*
 * the read/write register is always the destination register,
 * except in a load state, where the source register is used 
 * as a pointer, and may have to be adjusted for post-increment/
 * pre-decrement through the ALU.
 */
always @(posedge clk)
    if( ~iowait )
        if( next == LOAD )
            rw_reg <= sreg0;
        else
            rw_reg <= dreg0;

/*
 * state machine 
 */

always @(posedge clk)
    if( reset )
        state <= JMP1;
    else
        state <= next;

always @*
    if( iowait )
        next = state;
    else case( state )
        JMP1:                                   next = JMP2;
        ALU2:                                   next = EXEC;
        LOAD:                                   next = STORE;

        default: 
            if( brk0 )                          $finish;
            else if( branch & cond_true )       next = JMP1;
            else if( jump0 | call0 | ret0 )     next = JMP1;
            else if( alu2 )                     next = ALU2;
            else if( st0 )                      next = STORE;
            else if( ld0 )                      next = LOAD;
            else                                next = EXEC;
    endcase

/*
 * branch logic
 */
always @(posedge clk)
    if( ~iowait )
        branch <= branch0 & (state != JMP1);

always @(posedge clk)
    if( ~iowait )
        target <=  pc + { {3{rel0[10]}}, rel0 };

/*
 * Program counter update
 */

always @(posedge clk)
    if( reset )
        pc <= 0;
    else if( ~iowait ) begin
        if( state == JMP1 )                             pc <= pc + 14'b1;
        else if( branch & cond_true )                   pc <= target;                       
        else if( jump0 | call0 )                        pc <= addr0;
        else if( ret0 )                                 pc <= stack[sp];
        else if( next != LOAD && next != ALU2 )         pc <= pc + 14'b1;
    end

/*
 * ALU operation. If not doing a mov, the operation is taken from the IR.
 * Otherwise, the ALU is set for memory data, or pointer post-inc/pre-dec.
 * Only the ALU can write to the register file.
 */

always @(posedge clk)
    if( ~iowait )
        if( ~mov0 )
            alu_op <= op0;
        else if( (next == STORE) & (dmode0 == MODE_REG) )
            alu_op <= ALU_MEM;
        else 
            alu_op <= ALU_ADD;

always @(posedge clk)
    if( ~iowait )
        imm <= mov0 | imm0; 

always @(posedge clk)
    if( ~iowait )
        alu <= alu0;

always @(posedge clk)
    if( ~iowait )
    cmp <= alu0 & (op0 == ALU_CMP);

/*
 * mode0 is the next mode for load/store, and mode is the current one
 */
wire [1:0] mode0 = (next == STORE) ? dmode0 : smode0;

/*
 * for pre-decrement, apply -1 offset to address.
 * for indirect, apply constant offset from instruction.
 */
always @(posedge clk)
    if( ~iowait)
        mem_offset <= (mode0 == MODE_DEC) ? ~0 : 
                      (mode0 == MODE_INC) ? 0  : offset0;

/*
 * immediate value going in to the ALU. During mov instructions the 
 * ALU is used for pointer updates, so the immediate value is either
 * 0, +1 or -1 depending on the mode.
 *
 * For immediate instructions, value is taken from IR.
 */
always @(posedge clk)
    if( ~iowait )
        if( mov0 )
           immval <= mode0 == MODE_INC ?  1 : 
                     mode0 == MODE_DEC ? -1 : 0;
        else 
           immval <= immval0;

/*
 * memory address calculation. 
 */
always @*
    mem_addr = dst + mem_offset; 

/*
 * register file
 */

always @(posedge clk)
    if( ~iowait & (state != JMP1) & (state != JMP2) & ((state != EXEC) | ~branch) & ~cmp )
        regfile[rw_reg] <= alu_out;

/*
 * stack
 */

always @(posedge clk)
    if( call0 & (state != JMP1) )
        stack[sp] <= pc;

always @(posedge clk)
    if( ~iowait & ~(branch & cond_true) & (state != JMP1) )
        if( call0 )
            sp_reg <= sp_reg + 1;
        else if( ret0 )
            sp_reg <= sp_reg - 1;

/*
 * ALU, 2 cycle results are stored in intermediate registers
 */
 
reg [31:0] shift_left;
reg [31:0] shift_right;

always @(posedge clk) begin
    shift_left  <= dst << oper;
    shift_right <= dst >> oper;
end

/*
 * ALU flags
 */


always @(posedge clk)
    if( ~iowait )
        alu_hold <= alu_out;

/*
 * ALU MUX
 */

assign oper = imm ? immval : src;

always @*
    case( alu_op )
            ALU_LSR : alu_out = shift_right;           // 2 cycle
            ALU_LSL : alu_out = shift_left;            
            ALU_MUL : alu_out = 16'hxxxx;              // not used (multiply);
            ALU_3   : alu_out = 16'hxxxx;              // not used

            ALU_AND : alu_out = dst & oper;
            ALU_OR  : alu_out = dst | oper;
            ALU_XOR : alu_out = dst ^ oper;
            ALU_7   : alu_out = 16'hxxxx;              // not used

            ALU_INV : alu_out = ~oper;
            ALU_MEM : alu_out = rd_mem_data | di;
            ALU_MOV:  alu_out = oper;
            ALU_SWP : alu_out = { oper[7:0], oper[15:8] }; 

            ALU_ADD : alu_out = dst + oper;
            ALU_13  : alu_out = 16'hxxxx;              // not used
            ALU_SUB : alu_out = dst - oper;
            ALU_CMP : alu_out = dst - oper;
    endcase

/*
 * v31 is the XOR bit 31 of add operands. It is used 
 * later for calculation of less-than flag. 
 */

always @(posedge clk)
    if( ~iowait )
        v31 <= dst[31] ^ (alu_op[0] ? immval[31] : src[31]);

always @(posedge clk)
    if( ~iowait )
        cond <= cond0;

always @*
    case( cond )
        COND_EQ : cond_true =  z;
        COND_NE : cond_true = ~z;
        COND_CS : cond_true =  c;
        COND_CC : cond_true = ~c;
        COND_MI : cond_true =  n;
        COND_PL : cond_true = ~n;
        COND_LT : cond_true = lt;
        COND_GE : cond_true = ~lt;
    endcase

/*
 * Simulation aids
 */

`ifdef SIM
wire [15:0] stacktop = stack[sp];
reg [8*5-1:0] statename;

always @*
    case( state )
         EXEC : statename = "EXEC";
         LOAD : statename = "LOAD";
         STORE: statename = "STORE";
         ALU2 : statename = "ALU2";
         JMP1 : statename = "JMP1";
         JMP2 : statename = "JMP2";
    endcase

wire [31:0] reg0 = regfile[0];
wire [31:0] reg1 = regfile[1];
wire [31:0] reg2 = regfile[2];
wire [31:0] reg3 = regfile[3];
wire [31:0] reg4 = regfile[4];
wire [31:0] reg5 = regfile[5];
wire [31:0] reg6 = regfile[6];
wire [31:0] reg7 = regfile[7];
wire [31:0] reg8 = regfile[8];
wire [31:0] reg9 = regfile[9];
wire [31:0] reg10 = regfile[10];
wire [31:0] reg11 = regfile[11];
wire [31:0] reg12 = regfile[12];
wire [31:0] reg13 = regfile[13];
wire [31:0] reg14 = regfile[14];
wire [31:0] reg15 = regfile[15];

reg [8*4-1:0] alu_name;
always @*
    case( alu_op )
        ALU_MEM: alu_name = "MEM";
        ALU_MUL: alu_name = "MUL";
        ALU_3  : alu_name = "R3 ";
        ALU_7  : alu_name = "R7 ";
        ALU_13 : alu_name = "R13";
        ALU_AND: alu_name = "AND";
        ALU_OR : alu_name = "OR";
        ALU_XOR: alu_name = "XOR";
        ALU_MOV: alu_name = "MOV";
        ALU_SWP: alu_name = "SWP";
        ALU_INV: alu_name = "INV";
        ALU_LSR: alu_name = "LSR";
        ALU_LSL: alu_name = "LSL";
        ALU_ADD: alu_name = "ADD";
        ALU_SUB: alu_name = "SUB";
        ALU_CMP: alu_name = "CMP";
    endcase
`endif

endmodule
