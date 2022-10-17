# Batch mode

One can run Istari in batch mode from the command line by `istari` (if
not auto-loading the libraries, `istari-nolib`).  Istari is much
faster in batch mode, and it writes an output file that can be loaded
elsewhere.

Batch mode is invoked as follows:

    istari [options] <istari-file>
    -no             do not write output
    -o <filename>   output file name
