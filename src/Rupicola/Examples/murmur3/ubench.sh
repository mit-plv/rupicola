#/bin/sh
set -eu
cd "$(dirname "$0")"

( cd ../../../../
  COQFLAGS="${COQFLAGS:-"$(make -f Makefile.coqflags)"}" bedrock2/etc/bytedump.sh Rupicola.Examples.Arithmetic.murmur3_scramble_cbytes
  ) > murmur3_scramble_rupicola.h

CC="${CC:-cc}"
CFLAGS="${CFLAGS:--O3}"
benchmark=murmur3
for language in "c" "rupicola"; do
	CCname="$(printf "%s" "$CC" | sed 's/[0-9-]\+$//')"
	CCversion="$($CC --version | head -1 | tr ' ' '\n' | tail -1)"
	name="$benchmark-$language-${CCname}-$CCversion$CFLAGS"
	filename="benchmark-$(printf "%s" "$name" | tr -dc '0123456789=+-.ABCDEFGHIJKLMNOPQRSTUVWXYZ_abcdefghijklmnopqrstuvwxyz')"
	# ident="$(printf "%s" "$filename" | tr '=+-.' _)"
	$CC $CFLAGS -c ${benchmark}_${language}.c
	$CC $CFLAGS ubench.c ${benchmark}_${language}.o -o "$filename"

	doas /usr/local/bin/turboboost-off.sh > /dev/null
	doas /usr/local/bin/hyperthreading-off.sh > /dev/null
	doas /usr/bin/cpupower -c 2 frequency-set --governor performance > /dev/null
	printf '("%s", "%s", "%s", ' "$benchmark" "$language" "$CCname-$CCversion"
	taskset -c 2 ./"$filename"
	printf "),\n"
	doas /usr/local/bin/hyperthreading-on.sh > /dev/null
	doas /usr/local/bin/turboboost-on.sh > /dev/null
done
