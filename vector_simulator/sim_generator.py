import csv
import math
import os
import sys
# -------------------------------------
TOTAL_BUBBLE_CYCLES = 4
# Default Parameters
FILE_NAME = 'instrs.csv'
VECTOR_LANES = 8
AVL = 16
REPEATS = 1
# -------------------------------------
# install colorama for colored prints
# > pip install colorama
try:
    from colorama import init
    from colorama import Fore, Back, Style
    init()
    colored = 1
except ImportError:
    colored = 0
# -------------------------------------
def print_global(string, color):
    if colored == 1:
        if color == 'green':
            print(Fore.GREEN + str(string) + Fore.WHITE)
        elif color == 'yellow':
            print(Fore.YELLOW + str(string) + Fore.WHITE)
        elif color == 'red':
            print(Fore.RED + str(string) + Fore.WHITE)
        elif color == 'magenta':
            print(Fore.MAGENTA + str(string)+Fore.WHITE)
        elif color == 'cyan':
            print(Fore.CYAN + str(string)+Fore.WHITE)
        else:
            print(string)
    else:
        print(string)
# -------------------------------------
def get_instruction_list(filename):
    print_global('> reading input file...','green')
    with open(filename, 'r') as f:
      reader = csv.reader(f)
      instruction_list = list(reader)
    instruction_list = remove_garbage(instruction_list)
    return instruction_list
# -------------------------------------
# Removes Comments (// or #) and empty lines
def remove_garbage(instruction_list):
    final_list = []
    for i in range(0,len(instruction_list)):
        if (len(instruction_list[i]) > 0):
            if (instruction_list[i][0][0] != '#' and instruction_list[i][0][0] != '/'):
                final_list.append(instruction_list[i])
    return final_list
# -------------------------------------
def get_microop(instruction):
    switcher = {
        "vl":"vl",
        "vfld":"1000001",
        "vflh":"1001001",
        "vflsd":"1100001",
        "vflsh":"1101001",
        "vflsw":"1100001",
        "vflw":"1000001",
        "vflxd":"1110001",
        "vflxh":"1111001",
        "vflxw":"1110001",
        "vlb":"1000100",
        "vlbu":"1000110",
        "vld":"1000000",
        "vlh":"1001000",
        "vlhu":"1001010",
        "vlsb":"1100100",
        "vlsbu":"1100110",
        "vlsd":"1100000",
        "vlsw":"1100000",
        "vlswu":"1100010",
        "vlw":"1000000",
        "vlwu":"1000010",
        "vlxb":"1110100",
        "vlxbu":"1110110",
        "vlxd":"1110000",
        "vlxh":"1101000",
        "vlxh":"1111000",
        "vlxhu":"1101010",
        "vlxhu":"1111010",
        "vlxw":"1110000",
        "vlxwu":"1110010",
        "vsb":"0000100",
        "vsd":"0000000",
        "vsh":"0001000",
        "vssb":"0100100",
        "vssd":"0100000",
        "vssh":"0101000",
        "vssw":"0100000",
        "vsw":"0000000",
        "vsxb":"0110100",
        "vsxd":"0110000",
        "vsxh":"0111000",
        "vsxub":"0110100",
        "vsxud":"0110000",
        "vsxuh":"0111000",
        "vsxuw":"0110000",
        "vsxw":"0110000",
        "vadd":"0000001",
        "vaddi":"0000010",
        "vaddw":"0000011",
        "vaddiw":"0000100",
        "vsub":"0000101",
        "vsubw":"0000110",
        "vmul":"0000111",
        "vmulh":"0001000",
        "vmulhsu":"0001001",
        "vmulhu":"0001010",
        "vmulwdn":"0001011",
        "vdiv":"0001100",
        "vdivu":"0001101",
        "vrem":"0001110",
        "vremu":"0001111",
        "vsll":"0010000",
        "vslli":"0010001",
        "vsra":"0010010",
        "vsrai":"0010011",
        "vsrl":"0010100",
        "vsrli":"0010101",
        "vand":"0010110",
        "vandi":"0010111",
        "vor":"0011000",
        "vori":"0011001",
        "vxor":"0011010",
        "vxori":"0011011",
        "vseq":"0011100",
        "vslt":"0011101",
        "vsltu":"0011110",
        "vtan":"0100000",
        "vsin":"0100001",
        "vcos":"0100010",
        "vrelu":"0100000",
        "vstep":"0100001",
        "vbrelu":"0100010",
        "vprelu":"0100011",
        "vradd":"1000000",
        "vrand":"1000001",
        "vror":"1000010",
        "vrxor":"1000011",
        "vtplcfg":"1110011",
        "vtpl":"1010011"
    }
    microop = switcher.get(instruction, "nothing")
    if microop == "nothing":
        print_global('--> wrong microop ('+ instruction +').. Exiting','red')
        exit(-1)
    return microop
# -------------------------------------
def get_fu(instruction):
    switcher = {
        "vfld":"00",
        "vflh":"00",
        "vflsd":"00",
        "vflsh":"00",
        "vflsw":"00",
        "vflw":"00",
        "vflxd":"00",
        "vflxh":"00",
        "vflxw":"00",
        "vlb":"00",
        "vlbu":"00",
        "vld":"00",
        "vlh":"00",
        "vlhu":"00",
        "vlsb":"00",
        "vlsbu":"00",
        "vlsd":"00",
        "vlsw":"00",
        "vlswu":"00",
        "vlw":"00",
        "vlwu":"00",
        "vlxb":"00",
        "vlxbu":"00",
        "vlxd":"00",
        "vlxh":"00",
        "vlxh":"00",
        "vlxhu":"00",
        "vlxhu":"00",
        "vlxw":"00",
        "vlxwu":"00",
        "vsb":"00",
        "vsd":"00",
        "vsh":"00",
        "vssb":"00",
        "vssd":"00",
        "vssh":"00",
        "vssw":"00",
        "vsw":"00",
        "vsxb":"00",
        "vsxd":"00",
        "vsxh":"00",
        "vsxub":"00",
        "vsxud":"00",
        "vsxuh":"00",
        "vsxuw":"00",
        "vsxw":"00",
        "vadd":"10",
        "vaddi":"10",
        "vaddw":"10",
        "vaddiw":"10",
        "vsub":"10",
        "vsubw":"10",
        "vmul":"10",
        "vmulh":"10",
        "vmulhsu":"10",
        "vmulhu":"10",
        "vmulwdn":"10",
        "vdiv":"10",
        "vdivu":"10",
        "vrem":"10",
        "vremu":"10",
        "vsll":"10",
        "vslli":"10",
        "vsra":"10",
        "vsrai":"10",
        "vsrl":"10",
        "vsrli":"10",
        "vand":"10",
        "vandi":"10",
        "vor":"10",
        "vori":"10",
        "vxor":"10",
        "vxori":"10",
        "vseq":"10",
        "vslt":"10",
        "vsltu":"10",
        "vtan":"01",
        "vsin":"01",
        "vcos":"01",
        "vradd":"10",
        "vrand":"10",
        "vror":"10",
        "vrxor":"10",
        "vrelu":"10",
        "vstep":"10",
        "vbrelu":"10",
        "vprelu":"10",
        "vtplcfg":"00",
        "vtpl":"00"
    }
    fu = switcher.get(instruction, "nothing")
    if fu == "nothing":
        print_global('--> wrong fu.. Exiting','red')
        exit(-2)
    return fu
# -------------------------------------
def get_operand(instruction):
    # strip spaces
    instruction = instruction.replace(" ", "")
    # Check if its register
    if instruction[0] == 'v':
        return instruction[1:], '0'
    # Check if its immediate
    elif instruction[0] == '#':
        return '0', instruction[1:]
    else:
        print_global('--> wrong operand.. Exiting','red')
        exit(-4)
# -------------------------------------
def get_number_vdst(instruction_list):
    destination_list = []
    for i in range(0,len(instruction_list)):
        destination, temp = get_operand(instruction_list[i][1])
        destination_list.append(destination+'\n')
    total_vregs = len(set(destination_list))
    return total_vregs
# -------------------------------------
def get_binary_32(input):
    number = int(input)
    return f'{number:032b}'
def get_binary_5(input):
    number = int(input)
    if number > 31:
        print_global('--> number bigger than 5.. Exiting','red')
        exit(-5)
    return f'{number:05b}'
# -------------------------------------
def instr_is_mem(fu):
    return (fu == "00")
# ================================================
# Read Command Line Arguments
if (len(sys.argv)>1):
    FILE_NAME = sys.argv[1]
print_global('using file: '+FILE_NAME,'green')
# -------------------------------------
if (len(sys.argv)>2):
    AVL = int(sys.argv[2])
print_global('initial maxvl: '+str(AVL),'green')
# -------------------------------------
if (len(sys.argv)>3):
    VECTOR_LANES = int(sys.argv[3])
print_global('using VECTOR_LANES = '+str(VECTOR_LANES),'green')
# ================================================
instruction_list = get_instruction_list(FILE_NAME)
if len(instruction_list) == 0:
    print_global('> Empty Instruction List, exiting...','red')
    exit(-1)

total_vregs = get_number_vdst(instruction_list)
print_global('> total used registers: '+str(total_vregs),'cyan')
max_vregs = int(32 / total_vregs)
maxvl = max_vregs * VECTOR_LANES
vl = min(maxvl, AVL)

REPEATS = math.ceil(AVL / maxvl)
# REPEATS = 16

print_global('>> reconfiguration for maxvl = '+str(max_vregs)+' vregs, = '+str(maxvl)+' elements','cyan')
print_global('>> reconfiguration for vl = '+str(vl)+' elements','cyan')
print_global('> total used registers: '+str(total_vregs),'cyan')
print_global('> total loops: '+str(REPEATS),'cyan')

# ================================================
print_global('> processing instructions...','green')

decoded_info_list = []
microop_list = []
fu_list = []
vl_list = []
destination_list = []
operand_a_list = []
operand_b_list = []
operand_c_list = []
data1_list = []
data2_list = []
immediate_list = []

vl_initial = vl
vl = get_binary_32(vl)

total_instructions = 0
zero_5 = get_binary_5(0)
zero_32 = get_binary_32(0)

# File to save the decoded info
# Process the list
for i in range(0,len(instruction_list)):
    vl = 0
    print_global('>> Instruction '+str(i),'yellow')
    # Get the Instruction
    instruction = instruction_list[i][0]
    # ---------------------------------------
    # Get the microop
    microop = get_microop(instruction)
    # Check for special encodings changing configs
    if (microop == 'vl'):
        temp, data = get_operand(instruction_list[i][1])
        vl = min(int(data), AVL)
        vl_list.append(vl)
        continue
    else:
        microop_list.append(microop+'\n')
    # ---------------------------------------
    # Get the FU
    fu = get_fu(instruction)
    fu_list.append(fu+'\n')
    # ---------------------------------------
    # Append the VL
    vl_list.append(vl)
    # ---------------------------------------
    # Get the Operands
    operand_num = len(instruction_list[i]) -1
    if operand_num == 1:
        destination, temp = get_operand(instruction_list[i][1])
        destination       = get_binary_5(destination)
        destination_list.append(destination+'\n')
        operand_a_list.append(zero_5+'\n')
        operand_b_list.append(zero_5+'\n')
        operand_c_list.append(zero_5+'\n')
        data1_list.append(zero_32+'\n')
        data2_list.append(zero_32+'\n')
        immediate_list.append(zero_32+'\n')
        operand_a = '-'
        operand_b = '-'
        operand_c = '-'
        data1 = '-'
        data2 = '-'
    elif operand_num == 2:
        destination, temp = get_operand(instruction_list[i][1])
        operand_a, data1  = get_operand(instruction_list[i][2])
        destination       = get_binary_5(destination)
        operand_a         = get_binary_5(operand_a)
        data1             = get_binary_32(data1)
        immediate         = data1
        destination_list.append(destination+'\n')
        operand_a_list.append(operand_a+'\n')
        operand_b_list.append(zero_5+'\n')
        operand_c_list.append(zero_5+'\n')
        data1_list.append(data1+'\n')
        data2_list.append(zero_32+'\n')
        immediate_list.append(immediate+'\n')
        operand_b = '-'
        operand_c = '-'
        data2 = '-'
    elif operand_num == 3:
        destination, temp = get_operand(instruction_list[i][1])
        operand_a, data1  = get_operand(instruction_list[i][2])
        operand_b, data2  = get_operand(instruction_list[i][3])
        destination       = get_binary_5(destination)
        operand_a         = get_binary_5(operand_a)
        operand_b         = get_binary_5(operand_b)
        data1             = get_binary_32(data1)
        data2             = get_binary_32(data2)
        immediate         = data2
        destination_list.append(destination+'\n')
        operand_a_list.append(operand_a+'\n')
        operand_b_list.append(operand_b+'\n')
        operand_c_list.append(zero_5+'\n')
        data1_list.append(data1+'\n')
        data2_list.append(data2+'\n')
        immediate_list.append(immediate+'\n')
        operand_c = '-'
    elif operand_num == 4:
        destination, temp = get_operand(instruction_list[i][1])
        operand_a, data1  = get_operand(instruction_list[i][2])
        operand_b, data2  = get_operand(instruction_list[i][3])
        operand_c, temp   = get_operand(instruction_list[i][4])
        destination       = get_binary_5(destination)
        operand_a         = get_binary_5(operand_a)
        operand_b         = get_binary_5(operand_b)
        operand_c         = get_binary_5(operand_c)
        data1             = get_binary_32(data1)
        data2             = get_binary_32(data2)
        immediate         = get_binary_32(temp)
        destination_list.append(destination+'\n')
        operand_a_list.append(operand_a+'\n')
        operand_b_list.append(operand_b+'\n')
        operand_c_list.append(operand_c+'\n')
        data1_list.append(data1+'\n')
        data2_list.append(data2+'\n')
        immediate_list.append(immediate+'\n')
    elif operand_num > 4:
        print_global('--> unsupported number of operands.. Exiting','red')
        exit(-3)
    # ---------------------------------------
    new_line = str(instruction_list[i])+': valid=1, dst='+str(destination)+', src1='+str(operand_a)+', src2='+str(operand_b)+', data1='+str(data1)+', data2='+str(data2)+', reconfigure='+str(0)+', immediate='+str(immediate)+', fu='+str(fu)+', microop='+str(microop)
    decoded_info_list.append(new_line)
    total_instructions = total_instructions +1


# ==============================================================
# ==============================================================
print_global('> writing results to file...','green')

# Create the results directory
subdir, file_extension = os.path.splitext(FILE_NAME)
result_dir = 'decoder_results/'+subdir
try:
    os.mkdir(result_dir)
except OSError:
    print_global('> result directory exists, overwriting..','yellow')
    # print ("Result directory exists, overwriting..")

# Write the Files
decoded_output_file  = open(result_dir+"/decoded_output.txt", "w")
reconfiguration_file = open(result_dir+"/reconfigure_output.txt", "w")
microop_file         = open(result_dir+"/microop_output.txt", "w")
fu_file              = open(result_dir+"/fu_output.txt", "w")
destination_file     = open(result_dir+"/destination_output.txt", "w")
operand_a_file       = open(result_dir+"/operand_a_output.txt", "w")
operand_b_file       = open(result_dir+"/operand_b_output.txt", "w")
operand_c_file       = open(result_dir+"/operand_c_output.txt", "w")
data1_file           = open(result_dir+"/data1_output.txt", "w")
data2_file           = open(result_dir+"/data2_output.txt", "w")
immediate_file       = open(result_dir+"/immediate_output.txt", "w")
maxvl_file           = open(result_dir+"/maxvl_output.txt", "w")
vl_file              = open(result_dir+"/vl_output.txt", "w")

total_instructions = 1
# First write the reconfiguration instruction
decoded_output_file.write('reconfigure: maxvl == '+str(maxvl)+'\n')
reconfiguration_file.write('1\n')
microop_file.write('0000000\n')
fu_file.write('00\n')
destination_file.write(zero_5+'\n')
operand_a_file.write(zero_5+'\n')
operand_b_file.write(zero_5+'\n')
operand_c_file.write(zero_5+'\n')
data1_file.write(zero_32+'\n')
data2_file.write(zero_32+'\n')
immediate_file.write(zero_32+'\n')
maxvl_file.write(get_binary_32(maxvl)+'\n')
vl_file.write(get_binary_32(vl_initial)+'\n')

# Now write the instructions
for j in range(0,REPEATS):
    if (j == REPEATS-1):
        current_vl = AVL - (REPEATS-1)*maxvl
    else:
        current_vl = vl_initial

    for i in range(0,len(decoded_info_list)):
        total_instructions = total_instructions +1
        # Write the Decoded Info into the file

        reconfiguration_file.write('0\n')
        # Write the struct fields into different files
        microop_file.write(microop_list[i])
        fu_file.write(fu_list[i])
        destination_file.write(destination_list[i])
        operand_a_file.write(operand_a_list[i])
        operand_b_file.write(operand_b_list[i])
        operand_c_file.write(operand_c_list[i])
        data1_file.write(data1_list[i])
        data2_file.write(data2_list[i])
        immediate_file.write(immediate_list[i])
        maxvl_file.write(get_binary_32(maxvl)+'\n')
        if (vl_list[i] == 0):
            vl_file.write(get_binary_32(current_vl)+'\n')
            decoded_output_file.write(decoded_info_list[i]+', vl='+str(current_vl)+'\n')
        else:
            vl_file.write(get_binary_32(vl_list[i])+'\n')
            decoded_output_file.write(decoded_info_list[i]+', vl='+str(vl_list[i])+'\n')
    # Overhead due to bookkeeping inside the scalar core
    # Adds specific encodings to be consumed by the TB to emulate bubble cycles
    for k in range(0,TOTAL_BUBBLE_CYCLES):
        total_instructions = total_instructions +1
        decoded_output_file.write('BUBBLE CYCLE: maxvl == '+str(maxvl)+'\n')
        reconfiguration_file.write('1\n') # part of the special encoding
        microop_file.write('1111111\n')   # part of the special encoding
        fu_file.write('11\n')             # part of the special encoding
        destination_file.write(zero_5+'\n')
        operand_a_file.write(zero_5+'\n')
        operand_b_file.write(zero_5+'\n')
        operand_c_file.write(zero_5+'\n')
        data1_file.write(zero_32+'\n')
        data2_file.write(zero_32+'\n')
        immediate_file.write(zero_32+'\n')
        maxvl_file.write(get_binary_32(0)+'\n')
        vl_file.write(get_binary_32(0)+'\n')

# Close the Files
decoded_output_file.close()
reconfiguration_file.close()
microop_file.close()
fu_file.close()
destination_file.close()
operand_a_file.close()
operand_b_file.close()
operand_c_file.close()
data1_file.close()
data2_file.close()
immediate_file.close()
maxvl_file.close()
vl_file.close()

# Write the parameters
# add the reconfiguration instruction
# total_instructions = REPEATS * total_instructions +1

params_file = open("decoder_results/autogenerated_params.sv", "w")
params_file.write('localparam int SIM_VECTOR_INSTRS = '+str(total_instructions)+';')
params_file.close()

print_global('> finished!','green')
print_global('> Total Instructions: '+str(total_instructions),'green')