/* BitSet.c ---
 *
 * Filename: BitSet.c
 * Author: Abhishek Udupa
 * Created: Mon Sep 21 12:19:52 2015 (-0400)
 */

/* Copyright (c) 2015, Abhishek Udupa, University of Pennsylvania
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 3. All advertising materials mentioning features or use of this software
 *    must display the following acknowledgement:
 *    This product includes software developed by The University of Pennsylvania
 * 4. Neither the name of the University of Pennsylvania nor the
 *    names of its contributors may be used to endorse or promote products
 *    derived from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDER ''AS IS'' AND ANY
 * EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
 * WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER BE LIABLE FOR ANY
 * DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
 * (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
 * LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
 * ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

/* Code: */

#include "BitSet.h"
#include "FNVHash64.h"
#include <string.h>
#include <stdlib.h>
#include <stdio.h>

#define BITS_PER_BIT_VECTOR_ELEMENT (sizeof(u64) * 8)

#define BITS_TO_NUM_ELEMS(num_bits__) \
    ((num_bits__ + (BITS_PER_BIT_VECTOR_ELEMENT - 1)) / BITS_PER_BIT_VECTOR_ELEMENT)

#define BITSET_MAX_NUM_BITS ((u64)1 << 30)

/* Error codes */
#define BITSET_ERROR_CODE_OK (0)
#define BITSET_ERROR_CODE_INDEX_OOB (1)
#define BITSET_ERROR_CODE_NULL_PTR (2)
#define BITSET_ERROR_CODE_INCOMPATIBLE (3)
#define BITSET_ERROR_CODE_MEM_ALLOCATION (4)
#define BITSET_ERROR_CODE_LEN_TOO_LARGE (5)
#define BITSET_ERROR_CODE_LEN_TOO_SMALL (6)

const char* bitset_error_code_strings_[] = {
    "OK: No error occurred.",
    "Index out of bounds.",
    "Null pointer encountered.",
    "Incompatible bitsets for operation.",
    "Memory allocation error.",
    "Bit length too large.",
    "Bit length too small."
};

u32 bitset_last_error_code_ = 0;

u64 bitset_get_error_code()
{
    return bitset_last_error_code_;
}

const char* bitset_get_error_string_for_error_code(u64 error_code)
{
    return bitset_error_code_strings_[error_code];
}

const char* bitset_get_error_string_for_last_error()
{
    return bitset_get_error_string_for_error_code(bitset_last_error_code_);
}

BitSet* bitset_create_bitset(u64 num_bits)
{
    bitset_last_error_code_ = BITSET_ERROR_CODE_OK;
    if (num_bits == 0) {
        bitset_last_error_code_ = BITSET_ERROR_CODE_LEN_TOO_SMALL;
        return NULL;
    }

    BitSet* retval = (BitSet*)malloc(sizeof(BitSet));
    if (retval == NULL) {
        bitset_last_error_code_ = BITSET_ERROR_CODE_MEM_ALLOCATION;
        return NULL;
    }
    u64 bitvec_size = BITS_TO_NUM_ELEMS(num_bits);
    retval->m_num_bits = num_bits;
    retval->m_bit_vector = (u64*)calloc(bitvec_size, sizeof(u64));
    if (retval->m_bit_vector == NULL) {
        bitset_last_error_code_ = BITSET_ERROR_CODE_MEM_ALLOCATION;
        free(retval);
        return NULL;
    }
    return retval;
}

void bitset_destroy_bitset(BitSet* bitset)
{
    if (bitset == NULL) {
        return;
    }

    /* fprintf(stderr, "Destroying bitset\n"); */
    free(bitset->m_bit_vector);
    free(bitset);
}

BitSet* bitset_clone_bitset(const BitSet* bitset)
{
    u64 vec_len = 0, len = 0;
    BitSet* retval = NULL;

    bitset_last_error_code_ = BITSET_ERROR_CODE_OK;

    vec_len = bitset->m_num_bits;
    retval = bitset_create_bitset(vec_len);
    if (retval == NULL) {
        return NULL;
    }
    len = BITS_TO_NUM_ELEMS(vec_len);
    memcpy(retval->m_bit_vector, bitset->m_bit_vector, sizeof(u64) * len);
    return retval;
}

void bitset_resize_bitset(BitSet* bitset, u64 new_num_bits)
{
    bitset_last_error_code_ = BITSET_ERROR_CODE_OK;
    u64 old_num_bits = bitset->m_num_bits;
    if (new_num_bits == old_num_bits) {
        return;
    }
    u64 new_len = BITS_TO_NUM_ELEMS(new_num_bits);
    u64 old_len = BITS_TO_NUM_ELEMS(old_num_bits);
    u64 smallest_len = (new_len < old_len ? new_len : old_len);

    u64* new_bit_vec = (u64*)calloc(sizeof(u64), new_len);
    u64* old_bit_vec = bitset->m_bit_vector;
    memcpy(new_bit_vec, old_bit_vec, sizeof(u64) * smallest_len);
    bitset->m_bit_vector = new_bit_vec;
    bitset->m_num_bits = new_num_bits;
    free(old_bit_vec);
}

static inline bool check_bounds(const BitSet* bitset, u64 bit_num)
{
    if (bit_num >= bitset->m_num_bits) {
        bitset_last_error_code_ = BITSET_ERROR_CODE_INDEX_OOB;
        return false;
    } else {
        return true;
    }
}

static inline u64 construct_mask(u64 position)
{
    if (position == 0) {
        return 1;
    } else {
        u64 retval = 1;
        retval <<= position;
        return retval;
    }
}

bool bitset_are_bitsets_equal(const BitSet* bitset1, const BitSet* bitset2)
{
    u64 num_bits;
    bitset_last_error_code_ = BITSET_ERROR_CODE_OK;
    num_bits = bitset1->m_num_bits;
    if (num_bits != bitset2->m_num_bits) {
        bitset_last_error_code_ = BITSET_ERROR_CODE_INCOMPATIBLE;
        return false;
    }
    u64 len = BITS_TO_NUM_ELEMS(num_bits);
    if (memcmp(bitset1->m_bit_vector, bitset2->m_bit_vector, sizeof(u64) * len) != 0) {
        return false;
    } else {
        return true;
    }
}

void bitset_set_bit_in_bitset(u64 bit_number, BitSet* bitset)
{
    bitset_last_error_code_ = BITSET_ERROR_CODE_OK;
    if (!check_bounds(bitset, bit_number)) {
        return;
    }
    u64 offset = BITS_TO_NUM_ELEMS(bit_number + 1) - 1;
    u64 position = bit_number % BITS_PER_BIT_VECTOR_ELEMENT;
    u64 mask = construct_mask(position);
    bitset->m_bit_vector[offset] |= mask;
}

void bitset_clear_bit_in_bitset(u64 bit_number, BitSet* bitset)
{
    bitset_last_error_code_ = BITSET_ERROR_CODE_OK;
    if (!check_bounds(bitset, bit_number)) {
        return;
    }
    u64 offset = BITS_TO_NUM_ELEMS(bit_number + 1) - 1;
    u64 position = bit_number % BITS_PER_BIT_VECTOR_ELEMENT;
    u64 mask = construct_mask(position);
    mask = ~mask;
    bitset->m_bit_vector[offset] &= mask;
}

bool bitset_flip_bit_in_bitset(u64 bit_number, BitSet* bitset)
{
    bitset_last_error_code_ = BITSET_ERROR_CODE_OK;
    if (!check_bounds(bitset, bit_number)) {
        return false;
    }
    u64 offset = BITS_TO_NUM_ELEMS(bit_number + 1) - 1;
    u64 position = bit_number % BITS_PER_BIT_VECTOR_ELEMENT;
    u64 mask = construct_mask(position);
    bool retval = ((bitset->m_bit_vector[offset] & mask) != (u64)0);
    bitset->m_bit_vector[offset] ^= mask;
    return retval;
}

bool bitset_test_bit_in_bitset(u64 bit_number, const BitSet* bitset)
{
    bitset_last_error_code_ = BITSET_ERROR_CODE_OK;
    if (!check_bounds(bitset, bit_number)) {
        return false;
    }
    u64 offset = BITS_TO_NUM_ELEMS(bit_number + 1) - 1;
    u64 position = bit_number % BITS_PER_BIT_VECTOR_ELEMENT;
    u64 mask = construct_mask(position);
    bool retval = ((mask & bitset->m_bit_vector[offset]) != (u64)0);
    /* printf("Test Bit: Returning %s\n", retval ? "true" : "false"); */
    /* printf("Test Bit: Mask = %lX, Offset = %lu, Bit Vec Elem = %lX\n", */
    /*        mask, offset, bitset->m_bit_vector[offset]); */
    return retval;
}

void bitset_clear_all_bits_in_bitset(BitSet* bitset)
{
    bitset_last_error_code_ = BITSET_ERROR_CODE_OK;
    u64 len = BITS_TO_NUM_ELEMS(bitset->m_num_bits);
    memset(bitset->m_bit_vector, 0, sizeof(u64) * len);
}

void bitset_set_all_bits_in_bitset(BitSet* bitset)
{
    bitset_last_error_code_ = BITSET_ERROR_CODE_OK;
    u64 num_bits = bitset->m_num_bits;
    u64 len = BITS_TO_NUM_ELEMS(num_bits);
    u64 rem = num_bits % BITS_PER_BIT_VECTOR_ELEMENT;
    if (rem != 0) {
        memset(bitset->m_bit_vector, 0xFF, sizeof(u64) * (len-1));
        u64 mask = ((u64)1 << rem) - 1;
        bitset->m_bit_vector[len-1] |= mask;
    } else {
        memset(bitset->m_bit_vector, 0xFF, sizeof(u64) * len);
    }
}

u64 bitset_get_bitset_size(const BitSet* bitset)
{
    bitset_last_error_code_ = BITSET_ERROR_CODE_OK;
    return bitset->m_num_bits;
}

u64 bitset_get_num_one_bits(const BitSet* bitset)
{
    bitset_last_error_code_ = BITSET_ERROR_CODE_OK;

    u64 retval = (u64)0;
    u64* first = bitset->m_bit_vector;
    u64* last = first + BITS_TO_NUM_ELEMS(bitset->m_num_bits);
    for (u64* current = first; current != last; ++current) {
        u64 temp = *current;
        temp = temp - ((temp >> 1) & (u64)0x5555555555555555);
        temp = (temp & (u64)0x3333333333333333) + ((temp >> 2) & (u64)0x3333333333333333);
        temp = (temp + (temp >> 4)) & (u64)0x0F0F0F0F0F0F0F0F;
        retval += ((u64)(temp * (u64)0x0101010101010101) >> 56);
    }

    return retval;
}

u64 bitset_get_num_zero_bits(const BitSet* bitset)
{
    bitset_last_error_code_ = BITSET_ERROR_CODE_OK;
    u64 one_bits = bitset_get_num_one_bits(bitset);
    return (bitset->m_num_bits - one_bits);
}

bool bitset_are_bitsets_disjoint(const BitSet* bitset1, const BitSet* bitset2)
{
    bitset_last_error_code_ = BITSET_ERROR_CODE_OK;
    u64 num_bits1 = bitset1->m_num_bits;
    u64 num_bits2 = bitset2->m_num_bits;

    if (num_bits1 != num_bits2) {
        bitset_last_error_code_ = BITSET_ERROR_CODE_INCOMPATIBLE;
        return false;
    }


    u64 len = BITS_TO_NUM_ELEMS(num_bits1);
    u64* vec1 = bitset1->m_bit_vector;
    u64* vec2 = bitset1->m_bit_vector;

    for (u64 i = 0; i < len; ++i) {
        if ((vec1[i] & vec2[i]) != 0) {
            return false;
        }
    }
    return true;
}

bool bitset_is_first_subset_of_second(const BitSet* bitset1, const BitSet* bitset2)
{
    bitset_last_error_code_ = BITSET_ERROR_CODE_OK;
    u64 num_bits1 = bitset1->m_num_bits;
    u64 num_bits2 = bitset2->m_num_bits;

    if (num_bits1 != num_bits2) {
        bitset_last_error_code_ = BITSET_ERROR_CODE_INCOMPATIBLE;
        return false;
    }

    u64 len = BITS_TO_NUM_ELEMS(num_bits1);
    u64* vec1 = bitset1->m_bit_vector;
    u64* vec2 = bitset1->m_bit_vector;

    for (u64 i = 0; i < len; ++i) {
        if ((vec1[i] & vec2[i]) != vec1[i]) {
            return false;
        }
    }
    return true;
}

bool bitset_is_first_proper_subset_of_second(const BitSet* bitset1, const BitSet* bitset2)
{
    bitset_last_error_code_ = BITSET_ERROR_CODE_OK;
    u64 num_bits1 = bitset1->m_num_bits;
    u64 num_bits2 = bitset2->m_num_bits;

    if (num_bits1 != num_bits2) {
        bitset_last_error_code_ = BITSET_ERROR_CODE_INCOMPATIBLE;
        return false;
    }

    u64 len = BITS_TO_NUM_ELEMS(num_bits1);
    u64* vec1 = bitset1->m_bit_vector;
    u64* vec2 = bitset1->m_bit_vector;

    bool proper = false;
    for (u64 i = 0; i < len; ++i) {
        if ((vec1[i] & vec2[i]) != vec1[i]) {
            return false;
        }
        proper = (proper || (vec1[i] != vec2[i]));
    }
    return proper;
}

BitSet* bitset_and_bitsets_functional(const BitSet* bitset1, const BitSet* bitset2)
{
    bitset_last_error_code_ = BITSET_ERROR_CODE_OK;
    u64 num_bits = bitset1->m_num_bits;
    if (num_bits != bitset2->m_num_bits) {
        bitset_last_error_code_ = BITSET_ERROR_CODE_INCOMPATIBLE;
        return NULL;
    }
    u64 len = BITS_TO_NUM_ELEMS(num_bits);

    BitSet* retval = bitset_create_bitset(num_bits);
    if (retval == NULL) {
        return NULL;
    }
    u64* dest_vec = retval->m_bit_vector;
    u64* src_vec1 = bitset1->m_bit_vector;
    u64* src_vec2 = bitset2->m_bit_vector;
    for (u64 i = 0; i < len; ++i) {
        dest_vec[i] = src_vec1[i] & src_vec2[i];
    }
    return retval;
}

void bitset_and_bitsets(BitSet* bitset1, const BitSet* bitset2)
{
    bitset_last_error_code_ = BITSET_ERROR_CODE_OK;
    u64 num_bits = bitset1->m_num_bits;
    if (num_bits != bitset2->m_num_bits) {
        bitset_last_error_code_ = BITSET_ERROR_CODE_INCOMPATIBLE;
        return;
    }
    u64 len = BITS_TO_NUM_ELEMS(num_bits);

    u64* src_vec1 = bitset1->m_bit_vector;
    u64* src_vec2 = bitset2->m_bit_vector;
    for (u64 i = 0; i < len; ++i) {
        src_vec1[i] = src_vec1[i] & src_vec2[i];
    }
    return;
}

BitSet* bitset_or_bitsets_functional(const BitSet* bitset1, const BitSet* bitset2)
{
    bitset_last_error_code_ = BITSET_ERROR_CODE_OK;
    u64 num_bits = bitset1->m_num_bits;
    if (num_bits != bitset2->m_num_bits) {
        bitset_last_error_code_ = BITSET_ERROR_CODE_INCOMPATIBLE;
        return NULL;
    }
    u64 len = BITS_TO_NUM_ELEMS(num_bits);

    BitSet* retval = bitset_create_bitset(num_bits);
    if (retval == NULL) {
        return NULL;
    }
    u64* dest_vec = retval->m_bit_vector;
    u64* src_vec1 = bitset1->m_bit_vector;
    u64* src_vec2 = bitset2->m_bit_vector;
    for (u64 i = 0; i < len; ++i) {
        dest_vec[i] = src_vec1[i] | src_vec2[i];
    }
    return retval;
}

void bitset_or_bitsets(BitSet* bitset1, const BitSet* bitset2)
{
    bitset_last_error_code_ = BITSET_ERROR_CODE_OK;
    u64 num_bits = bitset1->m_num_bits;
    if (num_bits != bitset2->m_num_bits) {
        bitset_last_error_code_ = BITSET_ERROR_CODE_INCOMPATIBLE;
        return;
    }
    u64 len = BITS_TO_NUM_ELEMS(num_bits);

    u64* src_vec1 = bitset1->m_bit_vector;
    u64* src_vec2 = bitset2->m_bit_vector;
    for (u64 i = 0; i < len; ++i) {
        src_vec1[i] = src_vec1[i] | src_vec2[i];
    }
    return;
}

BitSet* bitset_xor_bitsets_functional(const BitSet* bitset1, const BitSet* bitset2)
{
    bitset_last_error_code_ = BITSET_ERROR_CODE_OK;
    u64 num_bits = bitset1->m_num_bits;
    if (num_bits != bitset2->m_num_bits) {
        bitset_last_error_code_ = BITSET_ERROR_CODE_INCOMPATIBLE;
        return NULL;
    }
    u64 len = BITS_TO_NUM_ELEMS(num_bits);

    BitSet* retval = bitset_create_bitset(num_bits);
    if (retval == NULL) {
        return NULL;
    }
    u64* dest_vec = retval->m_bit_vector;
    u64* src_vec1 = bitset1->m_bit_vector;
    u64* src_vec2 = bitset2->m_bit_vector;
    for (u64 i = 0; i < len; ++i) {
        dest_vec[i] = src_vec1[i] ^ src_vec2[i];
    }
    return retval;
}

void bitset_xor_bitsets(BitSet* bitset1, const BitSet* bitset2)
{
    bitset_last_error_code_ = BITSET_ERROR_CODE_OK;
    u64 num_bits = bitset1->m_num_bits;
    if (num_bits != bitset2->m_num_bits) {
        bitset_last_error_code_ = BITSET_ERROR_CODE_INCOMPATIBLE;
        return;
    }
    u64 len = BITS_TO_NUM_ELEMS(num_bits);

    u64* src_vec1 = bitset1->m_bit_vector;
    u64* src_vec2 = bitset2->m_bit_vector;
    for (u64 i = 0; i < len; ++i) {
        src_vec1[i] = src_vec1[i] ^ src_vec2[i];
    }
    return;
}

BitSet* bitset_negate_and_bitsets_functional(const BitSet* bitset1, const BitSet* bitset2)
{
    bitset_last_error_code_ = BITSET_ERROR_CODE_OK;
    u64 num_bits = bitset1->m_num_bits;
    if (num_bits != bitset2->m_num_bits) {
        bitset_last_error_code_ = BITSET_ERROR_CODE_INCOMPATIBLE;
        return NULL;
    }
    u64 len = BITS_TO_NUM_ELEMS(num_bits);

    BitSet* retval = bitset_create_bitset(num_bits);
    if (retval == NULL) {
        return NULL;
    }
    u64* dest_vec = retval->m_bit_vector;
    u64* src_vec1 = bitset1->m_bit_vector;
    u64* src_vec2 = bitset2->m_bit_vector;
    for (u64 i = 0; i < len; ++i) {
        dest_vec[i] = src_vec1[i] & (~(src_vec2[i]));
    }
    return retval;
}

void bitset_negate_and_bitsets(BitSet* bitset1, const BitSet* bitset2)
{
    bitset_last_error_code_ = BITSET_ERROR_CODE_OK;
    u64 num_bits = bitset1->m_num_bits;
    if (num_bits != bitset2->m_num_bits) {
        bitset_last_error_code_ = BITSET_ERROR_CODE_INCOMPATIBLE;
        return;
    }
    u64 len = BITS_TO_NUM_ELEMS(num_bits);

    u64* src_vec1 = bitset1->m_bit_vector;
    u64* src_vec2 = bitset2->m_bit_vector;
    for (u64 i = 0; i < len; ++i) {
        src_vec1[i] = src_vec1[i] & (~(src_vec2[i]));
    }
    return;
}

BitSet* bitset_negate_bitset_functional(const BitSet* bitset)
{
    bitset_last_error_code_ = BITSET_ERROR_CODE_OK;
    u64 num_bits = bitset->m_num_bits;
    u64 len = BITS_TO_NUM_ELEMS(num_bits);
    BitSet* retval = bitset_create_bitset(num_bits);
    if (retval == NULL) {
        return NULL;
    }
    u64* dest_vec = retval->m_bit_vector;
    u64* src_vec = bitset->m_bit_vector;

    for (u64 i = 0; i < len; ++i) {
        dest_vec[i] = ~(src_vec[i]);
    }
    return retval;
}

void bitset_negate_bitset(BitSet* bitset)
{
    bitset_last_error_code_ = BITSET_ERROR_CODE_OK;
    u64 num_bits = bitset->m_num_bits;
    u64 len = BITS_TO_NUM_ELEMS(num_bits);

    u64* src_vec = bitset->m_bit_vector;
    for (u64 i = 0; i < len; ++i) {
        src_vec[i] = ~(src_vec[i]);
    }
    return;
}

/* hashing */

u64 bitset_compute_bitset_hash(const BitSet* bitset)
{
    bitset_last_error_code_ = BITSET_ERROR_CODE_OK;
    u64 len = BITS_TO_NUM_ELEMS(bitset->m_num_bits);
    return fnv_64a_buf(bitset->m_bit_vector, sizeof(u64) * len, FNV1A_64_INIT);
}

/* debug functions */
void bitset_debug_print_bitset(const BitSet* bitset)
{
    u64 len = BITS_TO_NUM_ELEMS(bitset->m_num_bits);
    printf("Debug printing BitSet.\n");
    for (u64 i = 0; i < len; ++i) {
        printf("%lX\n", bitset->m_bit_vector[i]);
    }
    printf("End Debug printing BitSet.\n\n");
}

#undef BITS_PER_BIT_VECTOR_ELEMENT

/* BitSet.c ends here */
