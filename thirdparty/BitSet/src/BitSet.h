/* BitSet.h ---
 *
 * Filename: BitSet.h
 * Author: Abhishek Udupa
 * Created: Mon Sep 21 12:03:28 2015 (-0400)
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

#if !defined BIT_SET_H__
#define BIT_SET_H__

#include <stdio.h>
#include <stdbool.h>
#include <inttypes.h>
#include <stdint.h>

typedef uint8_t u08;
typedef uint16_t u16;
typedef uint32_t u32;
typedef uint64_t u64;

typedef int8_t i08;
typedef int16_t i16;
typedef int32_t i32;
typedef int64_t i64;

typedef struct BitSet_tag_ {
    u64* m_bit_vector;
    u64 m_num_bits;
} BitSet;

#ifdef __cplusplus
extern "C" {
#endif /* __cplusplus */

    BitSet* bitset_create_bitset(u64 num_bits);
    void bitset_destroy_bitset(BitSet* bitset);
    void bitset_set_bit_in_bitset(u64 bit_number, BitSet* bitset);
    void bitset_clear_bit_in_bitset(u64 bit_number, BitSet* bitset);
    /* returns the OLD value of the bit, i.e., the value BEFORE the flip */
    bool bitset_flip_bit_in_bitset(u64 bit_number, BitSet* bitset);

    bool bitset_test_bit_in_bitset(u64 bit_number, const BitSet* bitset);
    void bitset_clear_all_bits_in_bitset(BitSet* bitset);
    void bitset_set_all_bits_in_bitset(BitSet* bitset);
    u64 bitset_get_bitset_size(const BitSet* bitset);
    u64 bitset_get_num_one_bits(const BitSet* bitset);
    u64 bitset_get_num_zero_bits(const BitSet* bitset);

    BitSet* bitset_and_bitsets_functional(const BitSet* bitset1, const BitSet* bitset2);
    BitSet* bitset_or_bitsets_functional(const BitSet* bitset1, const BitSet* bitset2);
    BitSet* bitset_xor_bitsets_functional(const BitSet* bitset1, const BitSet* bitset2);
    /* AND the first bitset with the NEGATED second bitset */
    BitSet* bitset_negate_and_bitsets_functional(const BitSet* bitset1, const BitSet* bitset2);

    bool bitset_are_bitsets_equal(const BitSet* bitset1, const BitSet* bitset2);
    bool bitset_are_bitsets_disjoint(const BitSet* bitset1, const BitSet* bitset2);
    /* returns true if all the elements of first set are contained in the second */
    bool bitset_is_first_subset_of_second(const BitSet* bitset1, const BitSet* bitset2);
    bool bitset_is_first_proper_subset_of_second(const BitSet* bitset1, const BitSet* bitset2);

    /*
     new_size > size:
     additional (new_size - size) zero elements allocated, and can be set by later operations
     new_size < size:
     bit set is truncated to the new size
    */
    void bitset_resize_bitset(BitSet* bitset, u64 new_size);

    /* stores result in first argument */
    void bitset_and_bitsets(BitSet* bitset1, const BitSet* bitset2);
    void bitset_or_bitsets(BitSet* bitset1, const BitSet* bitset2);
    void bitset_xor_bitsets(BitSet* bitset1, const BitSet* bitset2);
    /* AND the first bitset with the NEGATED second bitset,
       store result in first bitset (destructive update) */
    void bitset_negate_and_bitsets(BitSet* bitset1, const BitSet* bitset2);

    BitSet* bitset_negate_bitset_functional(const BitSet* bitset);
    void bitset_negate_bitset(BitSet* bitset);

    BitSet* bitset_clone_bitset(const BitSet* bitset);

    u64 bitset_get_error_code();
    const char* bitset_get_error_string_for_error_code(u64 error_code);
    const char* bitset_get_error_string_for_last_error();

    /* hashing */
    u64 bitset_compute_bitset_hash(const BitSet* bitset);

    /* debug functions */
    void bitset_debug_print_bitset(const BitSet* bitset);

#ifdef __cplusplus
}
#endif /* __cplusplus */

#endif /* BIT_SET_H__ */

/* BitSet.h ends here */
