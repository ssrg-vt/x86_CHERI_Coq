# Sample Binaries

This folder contains sample binaries for testing the x86-CHERI equivalence
checking tool chain.

## Artifacts

* sample.c --- several simple functions that operate only on registers, note that even with the `-O0` flag to disable optimization the CompCert compiler optimizes away assignments and operations that result in easily determined values. E.g. `int x = 4; int y = 2; return x + y` is optimized to `return 6`, but the for-loop with a static effect is not optimized.

## Build Instructions

### Building Sample Binaries

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

This should create the following files:

* samplerv.{o,s}
* sample.cap_asm    # cap is short for 'capability'
* samplex64.{o,s}
