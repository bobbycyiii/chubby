# chubby
Generating necklace manifolds and testing them for hyperbolic Dehn filling

This software accompanies an upcoming paper with several coauthors.

To run the software, you need Regina, version 5.1 or higher, available
[here](https://regina-normal.github.io); and you need SnapPy, version
2.6 or higher, available [here](https://snappy.computop.org/).

To compile the documentation, you need Noweb, available
[here](https://www.cs.tufts.edu/~nr/noweb/), and Python.

To do everything in one fell swoop, run the following:

    notangle -Rcompile.sh neckl.nw > compile.sh
    chmod +x compile.sh
    ./compile.sh

This runs the enumeration and naming, builds the LaTeX files,
and compiles the LaTeX into PDF files.

This is a destructive process; it overwrites previous files.

On a five-year old x86-64 quad-core laptop, this compiles in under ten minutes.
