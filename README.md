# Cheri Research

The x86-CHERI equivalence checker checks whether two binaries, one for x86, the other for CHERI
are functionally equivalent.

## Building The Coq Files

1. Install CompCert through opam.

    ```shell
    opam install coq-compcert
    ```

2. Execute `coq_makefile`.

3. Execute `make`.

## Resources

* [Intel Manuals](https://www.intel.com/content/www/us/en/developer/articles/technical/intel-sdm.html) for understanding the semantics of CPU execution and individual instructions.

  * [Volume 1](https://www.cs.princeton.edu/courses/archive/spr18/cos217/reading/x86-64-1.pdf) provides an overview. Chapters 3 and 4 describe the CPU execution environment and data types. This can help inform the big picture of what an ideal semantics can handle. Chapter 4 summarizes the instruction set.

  * Volumes [2A](https://www.intel.com/content/dam/www/public/us/en/documents/manuals/64-ia-32-architectures-software-developer-vol-2a-manual.pdf) and [2B](https://www.intel.com/content/dam/www/public/us/en/documents/manuals/64-ia-32-architectures-software-developer-vol-2b-manual.pdf) give a detailed explanation of the instructions. Volume 2A Sections 1.3 and 3.1 describe notations and explain how to read the manuals.

* [x86 Instruction Reference](https://www.felixcloutier.com/x86/) provides a lightweight and easily searchable html version of volumes 2A and 2B above. It is not officially supported by intel and may not reflect the official manuals accurately. Look at Volume 2A sections 1.3 and 3.1 for guidance reading this reference.

* [Cheri RiscV Reference](https://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-987.pdf) - See Section 4 for the ISA overview, Section 7 for the instruction reference, and Section 6 for an overview of Sail, the ISA specification language.

* [Short Cheri Intro](https://www.lightbluetouchpaper.org/2022/07/22/formal-cheri/) - Cambridge blog post (July 2022).

* [Long Cheri Intro](https://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-941.pdf) - Cambridge technical paper 941 (September 2019).

* [Armv8 semantics paper](https://dl.acm.org/doi/10.1145/3290384) - short story is the most complete machine readable semantics are closed source as of 2019. This [paper](https://ieeexplore.ieee.org/stamp/stamp.jsp?tp=&arnumber=7886675) from 2016 is also relevant.
