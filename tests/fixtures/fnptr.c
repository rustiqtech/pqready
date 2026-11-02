// clang --target=bpf -O2 -fPIC -c fnptr.c -o fnptr.o

extern unsigned long sol_curve_group_op(unsigned long, const void *, const void *, void *);

typedef unsigned long (*handler)(const unsigned char *);

static unsigned long __attribute__((noinline)) on_curve(const unsigned char *in) {
  unsigned char out[64];
  return sol_curve_group_op(1, in, in + 32, out);
}

unsigned long entrypoint(const unsigned char *in, handler volatile *slot) {
  *slot = on_curve;
  return (*slot)(in);
}
