/*
*
* @author VLSI Lab, EE dept., Democritus University of Thrace
*
*/
//Packet Fetched from IF
typedef struct packed {
    logic [31 : 0] pc          ;
    logic [31 : 0] data        ;
    logic          taken_branch;
} fetched_packet;
//Internal ROB configuration (per entry)
typedef struct packed {
    logic          valid          ;
    logic          pending        ;
    logic          flushed        ;
    logic          valid_dest     ;
    logic [ 5 : 0] lreg           ;
    logic [ 5 : 0] preg           ;
    logic [ 5 : 0] ppreg          ;
    logic [ 4 : 0] microoperation ;
    logic          valid_exception; //Clear reorder buffer on exception
    logic [ 3 : 0] cause          ; //redirect depending on cause
    logic          is_store       ;
    logic [31 : 0] address        ;
    logic [31 : 0] pc             ;
} rob_entry;
//---------------------------------------------------------------------------------------
//Struct from IS stage to request new entries(2x max per cycle)
typedef struct packed {
    logic         valid_request_1 ;
    logic         valid_dest_1    ;
    logic [5 : 0] lreg_1          ;
    logic [5 : 0] preg_1          ;
    logic [5 : 0] ppreg_1         ;
    logic [4 : 0] microoperation_1;
    logic [31: 0] pc_1            ;

    logic         valid_request_2 ;
    logic         valid_dest_2    ;
    logic [5 : 0] lreg_2          ;
    logic [5 : 0] preg_2          ;
    logic [5 : 0] ppreg_2         ;
    logic [4 : 0] microoperation_2;
    logic [31: 0] pc_2            ;
} new_entries;
//---------------------------------------------------------------------------------------
//Struct to Update the Architectural Register File
typedef struct packed {
    logic          valid_commit;
    logic          valid_write ;
    logic          flushed     ;
    logic [ 5 : 0] ldst        ;
    logic [ 5 : 0] pdst        ;
    logic [ 5 : 0] ppdst       ;
    logic [31 : 0] data        ;
    logic [ 2 : 0] ticket      ;
    logic [31 : 0] pc          ;
} writeback_toARF;
//---------------------------------------------------------------------------------------
//Struct from EX stage to update internal ROB status
typedef struct packed {
    logic          valid          ;
    logic [ 5 : 0] destination    ;
    logic [ 2 : 0] ticket         ;
    logic [31 : 0] data           ;
    logic          valid_exception;
    logic [ 3 : 0] cause          ;
} ex_update;
//---------------------------------------------------------------------------------------
//Struct towards Issue stage
typedef struct packed {
    logic         is_full  ;
    logic         two_empty;
    logic [2 : 0] ticket   ;
} to_issue;
//---------------------------------------------------------------------------------------
//Struct Carrying a decoded Instruction
typedef struct packed {
    logic [31 : 0] pc               ;
    logic [ 5 : 0] source1          ;
    logic          source1_pc       ;
    logic [ 5 : 0] source2          ;
    logic          source2_immediate;
    logic [31 : 0] immediate        ;
    logic [ 5 : 0] source3          ;
    logic [ 5 : 0] destination      ;
    logic [ 1 : 0] functional_unit  ;
    logic [ 4 : 0] microoperation   ;
    logic [ 2 : 0] rm               ;
    logic          is_branch        ;
    logic          is_vector        ;
    logic          is_valid         ;
} decoded_instr;
//---------------------------------------------------------------------------------------
//Struct Carrying a decoded and Renamed Instruction
typedef struct packed {
    logic [31 : 0] pc               ;
    logic [ 5 : 0] source1          ;
    logic          source1_pc       ;
    logic [ 5 : 0] source2          ;
    logic          source2_immediate;
    logic [31 : 0] immediate        ;
    logic [ 5 : 0] source3          ;
    logic [ 5 : 0] destination      ;
    logic [ 1 : 0] functional_unit  ;
    logic [ 4 : 0] microoperation   ;
    logic [ 3 : 0] ticket           ;
    logic [ 2 : 0] rm               ;
    logic [ 1 : 0] rat_id           ;
    logic          is_branch        ;
    logic          is_vector        ;
    logic          is_valid         ;
} renamed_instr;
//---------------------------------------------------------------------------------------
//Scoreboard Bookkeeping (per entry)
typedef struct packed {
    logic         pending;
    logic [1 : 0] fu     ;
    logic [2 : 0] ticket ;
    logic         in_rob ;
}scoreboard_entry;
//---------------------------------------------------------------------------------------
//FU Busy Configuration(per Entry)
typedef struct packed {
    logic busy;
}fu_entry;
//--------------------------
//to_Execution Stage
typedef struct packed {
    logic          valid          ;
    logic [31 : 0] pc             ;
    logic [ 5 : 0] destination    ;

    logic [31 : 0] data1          ;

    logic [31 : 0] data2          ;

    logic [31 : 0] immediate      ;
    logic [ 1 : 0] functional_unit;
    logic [ 4 : 0] microoperation ;
    logic [ 2 : 0] rm             ;
    logic [ 1 : 0] rat_id         ;
    logic [ 2 : 0] ticket         ;
}to_execution;
//---------------------------------------------------------------------------------------
typedef struct packed {
    logic          valid_jump  ;
    logic          jump_taken  ;
    logic          is_comp     ;
    logic [ 1 : 0] rat_id      ;
    logic [31 : 0] orig_pc     ;
    logic [31 : 0] jump_address;
    logic [ 2 : 0] ticket      ;
} predictor_update;
//---------------------------------------------------------------------------------------