# Cheri Research

This folder contains all the artifacts for the x86-to-CHERI translation project.

## Artifacts

* sample.c --- several simple functions that operate only on registers, note that even with the `-O0` flag to disable optimization the CompCert compiler optimizes away assignments and operations that result in statically determined values. E.g. `int x = 4; int y = 2; return x + y` is optimized to `return 6`.

## Build Instructions

1. Build [SECOMP](https://github.com/secure-compilation/SECOMP)'s CHERI RiscV enabled CompCert fork for rv64-linux. You will need the riscv64 extension to gcc and to use Coq's Flocq and MenhirLib (otherwise you'll get inconsistent assumptions when importing it and CompCert simultaneously).

    ```shell
    # WARNING: Untested build code.
    sudo apt-get install gcc-riscv64-linux-gnu
    git clone https://github.com/secure-compilation/SECOMP.git
    cd SECOMP
    ./configure -prefix $HOME -use-external-MenhirLib -use-external-Flocq -toolprefix "riscv64-linux-gnu-" rv64-linux
    make
    ln -s $PWD/ccomp $HOME/bin/ccomprv
    ```

2. Make it available as `ccomprv` in your PATH if the above code snippet did not.

3. Build the vanilla [CompCert](https://github.com/AbsInt/CompCert) for x86_64-linux.

    ```shell
    # WARNING: Untested build code.
    # Maybe you'll need this: sudo apt-get install glibc-devel.i686
    git clone https://github.com/AbsInt/CompCert.git
    cd CompCert
    ./configure -prefix $HOME x86_64-linux
    make
    ln -s $PWD/ccomp $HOME/bin/ccompx64
    ```

4. Make it available as `ccompx64` in your PATH if the above code snippet did not.

5. Run `./build.sh`.

6. Install CompCert through opam. This is redundant with 3 and 4, ideally these instructions will explain how to use the opam CompCert to compile the C code to x86_64.

    ```shell
    opam install coq-compcert
    ```

This should create the following files:

* samplerv.{o,s}
* sample.cap_asm    # cap is short for 'capability'
* samplex64.{o,s}

## Resources

* [Intel Manuals](https://www.intel.com/content/www/us/en/developer/articles/technical/intel-sdm.html) for understanding the semantics of CPU execution and individual instructions.

  * [Volume 1](https://www.cs.princeton.edu/courses/archive/spr18/cos217/reading/x86-64-1.pdf) provides an overview. Chapters 3 and 4 describe the CPU execution environment and data types. This can help inform the big picture of what an ideal semantics can handle. Chapter 4 summarizes the instruction set.

  * Volumes [2A](https://www.intel.com/content/dam/www/public/us/en/documents/manuals/64-ia-32-architectures-software-developer-vol-2a-manual.pdf) and [2B](https://www.intel.com/content/dam/www/public/us/en/documents/manuals/64-ia-32-architectures-software-developer-vol-2b-manual.pdf) give a detailed explanation of the instructions. Volume 2A Sections 1.3 and 3.1 describe notations and explain how to read the manuals.

* [x86 Instruction Reference](https://www.felixcloutier.com/x86/) provides a lightweight and easily searchable html version of volumes 2A and 2B above. It is not officially supported by intel and may not reflect the official manuals accurately. Look at Volume 2A sections 1.3 and 3.1 for guidance reading this reference.
