# Installation instructions

0. Ensure the prerequisites are installed:

   - Git
   - Standard ML of New Jersey
   - GNU Emacs
   - (if running on Windows) Cygwin

1. Obtain the distribution from Github:

        git clone --recursive git@github.com:<your-github-id>/istari.git istari

2. Configure the build script, by copying `Makefile.inc.customize` to
   `Makefile.inc`, then edit `Makefile.inc` to fill in the `INSTALLDIR`
   definition, and to uncomment one of the `MKNJEXEC` definitions.

3. Build Istari:

       make smlnj

4. Install Istari:

       make install

5. Copy the contents of `emacs.customize` into your `.emacs` file, and
   edit the `istari-root` definition with the path to the Istari root
   directory.
