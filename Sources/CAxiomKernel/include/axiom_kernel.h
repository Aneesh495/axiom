#ifndef AXIOM_KERNEL_H
#define AXIOM_KERNEL_H

#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>

#ifdef __cplusplus
extern "C" {
#endif

// Fast bitwise population count on 64-bit array
uint64_t axiom_popcount64_array(const uint64_t* data, size_t count);

// Fast bitwise vector AND: dest = src1 & src2
void axiom_vec_and(uint64_t* dest, const uint64_t* src1, const uint64_t* src2, size_t words);

// Fast bitwise vector OR: dest = src1 | src2
void axiom_vec_or(uint64_t* dest, const uint64_t* src1, const uint64_t* src2, size_t words);

// Fast bitwise vector XOR: dest = src1 ^ src2
void axiom_vec_xor(uint64_t* dest, const uint64_t* src1, const uint64_t* src2, size_t words);

// Fast bitwise vector NOT: dest = ~src
void axiom_vec_not(uint64_t* dest, const uint64_t* src, size_t words);

// Check if vector is all zero: returns 1 if all zero, 0 otherwise
int axiom_vec_is_zero(const uint64_t* data, size_t words);

// Fast AIG node 64-bit hash combining left child, right child, and operator tag
uint64_t axiom_aig_hash64(uint32_t left, uint32_t right, uint8_t op);

#ifdef __cplusplus
}
#endif

#endif // AXIOM_KERNEL_H
