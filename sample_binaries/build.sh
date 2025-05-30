#!/bin/sh
# Problems finding libraries if we include the -static option
BUILD_ARGS='-O0 -fno-fpu -g'

# Cannot find some libraries necessary for linking
# Maybe look at https://www.cl.cam.ac.uk/~jrrk2/docs/riscv_compile/
#ccomprv $BUILD_ARGS sample.c -o samplerv.o -L/home/ixb140230/git_clones/SECOMP/runtime/
ccomprv $BUILD_ARGS -c -dcapasm sample.c -o samplerv.o
ccomprv $BUILD_ARGS -S sample.c
mv sample.s samplerv.s

ccompx64 $BUILD_ARGS -L/home/ixb140230/git_clones/CompCert/runtime/ sample.c -o samplex64.o
ccompx64 $BUILD_ARGS -S sample.c
mv sample.s samplex64.s
