#!/bin/sh
set -eu
cd "$(dirname "$0")"

COMPILERS="clang-11 clang-12 clang-13 gcc-9 gcc-10 gcc-11"
{
	printf "# %s\n" "$(grep 'processor\W*2' -A5 /proc/cpuinfo | tr '\n' ';' |  sed 's/;/; /g; s/\s\+/ /g; s/ \?: \?/=/g')"
	printf 'data=[\n'
	find Net/IPChecksum -name 'ubench_ocaml.sh' | xargs -n1 env CC="clang" CFLAGS="-O3" sh
	for CC in $COMPILERS; do
        if [ -x "$(command -v "$CC")" ]; then
		    find Net/IPChecksum -name 'ubench.sh' | xargs -n1 env CC="$CC" CFLAGS="-O3" sh
        fi
	done
	printf ']\n'
} | tee latest_benchmark_ocaml_results.py
