// clang --target=bpf -O2 -fPIC -fno-builtin -c memcmp_call.c -o memcmp_call.o
// clang --target=bpf -O2 -fPIC -c memcmp_call.c -o memcmp_inline.o

extern int memcmp(const void *, const void *, unsigned long);

static const unsigned char pad[40] = {1,2,3};
static const unsigned char ED25519_ID[32] = {
    3,125,70,214,124,147,251,190,18,249,66,143,131,141,64,255,
    5,112,116,73,39,244,138,100,252,202,112,68,128,0,0,0
};

int is_ed25519(const unsigned char *key) {
    return memcmp(key, ED25519_ID, 32) == 0 && pad[0];
}
