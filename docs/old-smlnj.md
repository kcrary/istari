# Older versions of SML of New Jersey

Some old versions of SML/NJ contained a bug in the Basis in which the
large word type was 32 bits instead of 64 bits.  This was fixed in
110.89, but older versions are still in use in some places.

The best solution to this problem is to update SML/NJ.  If that is not
possible, the following workaround may fix the problem.  Starting from
the Istari root directory:

    cd cmlibi
    cp convert-word.sml convert-word-nj64.sml
    cp convert-word-nj32.sml convert-word.sml
    rm -f cmlib.ipds

Then build again.
