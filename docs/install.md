# Installation instructions

0. Ensure the prerequisites are installed:

   - Git
   - Standard ML of New Jersey (version 110.89 or later, but see below)
   - GNU Emacs
   - (if running on Windows) Cygwin

   [Some versions](compiler-versions.html) of Standard ML of New
   Jersey contain bugs or incompatibilities that keep Istari from
   compiling.  Version 110.99.7.1 is confirmed to work on Linux, Mac,
   and Windows.

1. Obtain the distribution from Github:

       git clone --recursive --branch v1.0.1 https://github.com/kcrary/istari.git istari

2. If you forgot to use the `--recursive` option in the previous step,
   populate the `cmlib` directory:

       git submodule init
       git submodule update

3. Configure the build script, by copying `Makefile.inc.customize` to
   `Makefile.inc`, then edit `Makefile.inc` to fill in the `INSTALLDIR`
   definition, and to uncomment one of the `MKNJEXEC` definitions.

4. Build Istari:

       make smlnj

5. Install Istari:

       make install

6. Copy the contents of `emacs.customize` into your `.emacs` file, and
   edit the `istari-root` definition with the path to the Istari root
   directory.

7. (Optional) If you want to receive occasional updates about Istari,
   submit your name and email address using the form
   [here](https://mailman.srv.cs.cmu.edu/mailman/listinfo/istari-announce).
