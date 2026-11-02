#!/bin/sh

for c in mldsa_native_zetas.c mlkem_native_zetas.c keccak_rc.c fndsa_gm.c falcon_gmb.c; do
  clang --target=bpf -O2 -fPIC -ffreestanding -c "$c" -o "${c%.c}.o"
done
