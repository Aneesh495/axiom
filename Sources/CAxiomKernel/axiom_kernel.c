#include "axiom_kernel.h"

#if defined(__arm64__) || defined(__aarch64__)
#include <arm_neon.h>
#elif defined(__x86_64__)
#include <immintrin.h>
#endif

uint64_t axiom_popcount64_array(const uint64_t* data, size_t count) {
    if (!data || count == 0) return 0;
    uint64_t total = 0;
    size_t i = 0;

#if defined(__arm64__) || defined(__aarch64__)
    uint64x2_t vtotal = vdupq_n_u64(0);
    for (; i + 2 <= count; i += 2) {
        uint8x16_t v = vld1q_u8((const uint8_t*)(data + i));
        uint8x16_t cnt = vcntq_u8(v);
        uint16x8_t p16 = vpaddlq_u8(cnt);
        uint32x4_t p32 = vpaddlq_u16(p16);
        uint64x2_t p64 = vpaddlq_u32(p32);
        vtotal = vaddq_u64(vtotal, p64);
    }
    total = vgetq_lane_u64(vtotal, 0) + vgetq_lane_u64(vtotal, 1);
#endif

    for (; i < count; i++) {
        total += (uint64_t)__builtin_popcountll(data[i]);
    }
    return total;
}

void axiom_vec_and(uint64_t* dest, const uint64_t* src1, const uint64_t* src2, size_t words) {
    if (!dest || !src1 || !src2) return;
    size_t i = 0;

#if defined(__arm64__) || defined(__aarch64__)
    for (; i + 2 <= words; i += 2) {
        uint64x2_t v1 = vld1q_u64(src1 + i);
        uint64x2_t v2 = vld1q_u64(src2 + i);
        vst1q_u64(dest + i, vandq_u64(v1, v2));
    }
#endif

    for (; i < words; i++) {
        dest[i] = src1[i] & src2[i];
    }
}

void axiom_vec_or(uint64_t* dest, const uint64_t* src1, const uint64_t* src2, size_t words) {
    if (!dest || !src1 || !src2) return;
    size_t i = 0;

#if defined(__arm64__) || defined(__aarch64__)
    for (; i + 2 <= words; i += 2) {
        uint64x2_t v1 = vld1q_u64(src1 + i);
        uint64x2_t v2 = vld1q_u64(src2 + i);
        vst1q_u64(dest + i, vorrq_u64(v1, v2));
    }
#endif

    for (; i < words; i++) {
        dest[i] = src1[i] | src2[i];
    }
}

void axiom_vec_xor(uint64_t* dest, const uint64_t* src1, const uint64_t* src2, size_t words) {
    if (!dest || !src1 || !src2) return;
    size_t i = 0;

#if defined(__arm64__) || defined(__aarch64__)
    for (; i + 2 <= words; i += 2) {
        uint64x2_t v1 = vld1q_u64(src1 + i);
        uint64x2_t v2 = vld1q_u64(src2 + i);
        vst1q_u64(dest + i, veorq_u64(v1, v2));
    }
#endif

    for (; i < words; i++) {
        dest[i] = src1[i] ^ src2[i];
    }
}

void axiom_vec_not(uint64_t* dest, const uint64_t* src, size_t words) {
    if (!dest || !src) return;
    size_t i = 0;

#if defined(__arm64__) || defined(__aarch64__)
    for (; i + 2 <= words; i += 2) {
        uint64x2_t v = vld1q_u64(src + i);
        vst1q_u64(dest + i, vmvnq_u8(vreinterpretq_u8_u64(v)));
    }
#endif

    for (; i < words; i++) {
        dest[i] = ~src[i];
    }
}

int axiom_vec_is_zero(const uint64_t* data, size_t words) {
    if (!data) return 1;
    for (size_t i = 0; i < words; i++) {
        if (data[i] != 0) return 0;
    }
    return 1;
}

uint64_t axiom_aig_hash64(uint32_t left, uint32_t right, uint8_t op) {
    // 64-bit splitmix style hash mixing for AIG structural hashing
    uint64_t k = ((uint64_t)left << 32) | (uint64_t)right;
    k ^= (uint64_t)op * 0x9e3779b97f4a7c15ULL;
    k = (k ^ (k >> 30)) * 0xbf58476d1ce4e5b9ULL;
    k = (k ^ (k >> 27)) * 0x94d049bb133111ebULL;
    return k ^ (k >> 31);
}

int64_t axiom_vec_dot_i64(const int64_t* a, const int64_t* b, size_t count) {
    if (!a || !b || count == 0) return 0;
    int64_t sum = 0;
    size_t i = 0;

#if defined(__arm64__) || defined(__aarch64__)
    int64x2_t vsum = vdupq_n_s64(0);
    for (; i + 2 <= count; i += 2) {
        int64x2_t va = vld1q_s64(a + i);
        int64x2_t vb = vld1q_s64(b + i);
        // Multiply and accumulate 64-bit integers
        int64_t prod0 = vgetq_lane_s64(va, 0) * vgetq_lane_s64(vb, 0);
        int64_t prod1 = vgetq_lane_s64(va, 1) * vgetq_lane_s64(vb, 1);
        vsum = vaddq_s64(vsum, (int64x2_t){prod0, prod1});
    }
    sum = vgetq_lane_s64(vsum, 0) + vgetq_lane_s64(vsum, 1);
#endif

    for (; i < count; i++) {
        sum += a[i] * b[i];
    }
    return sum;
}

int64_t axiom_bitset_find_first_set(const uint64_t* data, size_t words) {
    if (!data || words == 0) return -1;
    for (size_t i = 0; i < words; i++) {
        if (data[i] != 0) {
            int ctz = __builtin_ctzll(data[i]);
            return (int64_t)(i * 64 + (size_t)ctz);
        }
    }
    return -1;
}
