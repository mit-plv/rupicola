#!/bin/sh
set -eu

ROOT=$(realpath $(dirname "$0"))
cd "$ROOT"

(
    cd ../../../../../
    coqc ${COQFLAGS:-$(make -f Makefile.coqflags)} "$ROOT/Extraction.v"
    mv ip_*.ml* "$ROOT"
)

CC="${CC:-cc}"
CFLAGS="${CFLAGS:--O3}"

cc -DMAIN testdata.c -o testdata.exe && ./testdata.exe && rm testdata.exe
ulimit -s unlimited; taskset -c 0 dune exec --profile=release ./ubench_ocaml.exe "$(ocamlc -version)"
