quit -sim
file delete -force work

vlib work

#compile the dut code
#set cmd "vlog -F ../dut/files.f +incdir+.../dut/ -lint"
#set cmd "vlog -F files.f +incdir+../rtl/"
#eval $cmd

vlog -f files_rtl.f -f files_sim.f +incdir+../rtl/shared/ +incdir+../rtl/vector/ +incdir+../sva/

vsim -novopt work.vector_sim_top -onfinish "stop"
log -r /*
do wave_simulator.do
onbreak {wave zoom full}
run -all
wave zoom full