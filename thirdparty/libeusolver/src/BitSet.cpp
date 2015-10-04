// BitSet.cpp ---
// Filename: BitSet.cpp
// Author: Abhishek Udupa
// Created: Sat Oct  3 17:50:55 2015 (-0400)
//
// Copyright (c) 2013, Abhishek Udupa, University of Pennsylvania
// All rights reserved.
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions are met:
// 1. Redistributions of source code must retain the above copyright
//    notice, this list of conditions and the following disclaimer.
// 2. Redistributions in binary form must reproduce the above copyright
//    notice, this list of conditions and the following disclaimer in the
//    documentation and/or other materials provided with the distribution.
// 3. All advertising materials mentioning features or use of this software
//    must display the following acknowledgement:
//    This product includes software developed by The University of Pennsylvania
// 4. Neither the name of the University of Pennsylvania nor the
//    names of its contributors may be used to endorse or promote products
//    derived from this software without specific prior written permission.
//
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDER ''AS IS'' AND ANY
// EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
// WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
// DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER BE LIABLE FOR ANY
// DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
// (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
// LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
// ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
// (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
// SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
//
//

// Code:

#include "BitSet.hpp"

namespace eusolver {

// Implementation of BitSetException
BitSetException::BitSetException() noexcept
: m_exception_info("No information.")
{
    // Nothing here
}

BitSetException::BitSetException(const BitSetException& other) noexcept
: m_exception_info(other.m_exception_info)
{
    // Nothing here
}

BitSetException::BitSetException(BitSetException&& other) noexcept
: m_exception_info(std::move(other.m_exception_info))
{
    // Nothing here
}

BitSetException::~BitSetException()
{
    // Nothing here
}

BitSetException& BitSetException::operator = (const BitSetException& other) noexcept
{
    if (&other == this) {
        return *this;
    }
    m_exception_info = other.m_exception_info;
    return *this;
}

BitSetException& BitSetException::operator = (BitSetException&& other) noexcept
{
    if (&other == this) {
        return *this;
    }
    std::swap(m_exception_info, other.m_exception_info);
    return *this;
}

const std::string& BitSetException::get_exception_info() const noexcept
{
    return m_exception_info;
}

const char* BitSetException::what() const noexcept
{
    return m_exception_info.c_str();
}


// Implementation of BitSet::BitRef
BitSet::BitRef::BitRef()
    : m_bitset_ptr(nullptr), m_bit_position(0)
{
    // Nothing here
}

BitSet::BitRef::BitRef(const BitRef& other)
    : m_bitset_ptr(other.m_bitset_ptr), m_bit_position(other.m_bit_position)
{
    // Nothing here
}

BitSet::BitRef::BitRef(BitRef&& other)
    : BitRef()
{
    std::swap(other.m_bitset_ptr, m_bitset_ptr);
    std::swap(other.m_bit_position, m_bit_position);
}

BitSet::BitRef::BitRef(BitSet* bitset_ptr, u64 bit_position)
    : m_bitset_ptr(bitset_ptr), m_bit_position(bit_position)
{
    // Nothing here
}

BitSet::BitRef::~BitRef()
{
    // Nothing here
}

BitSet::BitRef& BitSet::BitRef::operator = (const BitRef& other)
{
    if (&other == this) {
        return *this;
    }
    m_bitset_ptr = other.m_bitset_ptr;
    m_bit_position = other.m_bit_position;
    return *this;
}

BitSet::BitRef& BitSet::BitRef::operator = (BitRef&& other)
{
    if (&other == this) {
        return *this;
    }
    std::swap(m_bitset_ptr, other.m_bitset_ptr);
    std::swap(m_bit_position, other.m_bit_position);
    return *this;
}

BitSet::BitRef& BitSet::BitRef::operator = (bool value)
{
    if (value) {
        m_bitset_ptr->set_bit(m_bit_position);
    } else {
        m_bitset_ptr->clear_bit(m_bit_position);
    }
    return *this;
}

BitSet::BitRef::operator bool () const
{
    return m_bitset_ptr->test_bit(m_bit_position);
}

bool BitSet::BitRef::operator == (const BitRef& other) const
{
    return ((bool)(*this) == (bool)other);
}

bool BitSet::BitRef::operator != (const BitRef& other) const
{
    return ((bool)(*this) != (bool)other);
}

bool BitSet::BitRef::operator == (bool value) const
{
    return (bool(*this) == value);
}

bool BitSet::BitRef::operator != (bool value) const
{
    return (bool(*this) != value);
}

bool BitSet::BitRef::operator ! () const
{
    return (!((bool)(*this)));
}


// Implementation of BitSet::ConstIterator
BitSet::ConstIterator::ConstIterator()
    : m_bitset(nullptr), m_bit_position(-1)
{
    // Nothing here
}

BitSet::ConstIterator::ConstIterator(const ConstIterator& other)
    : m_bitset(other.m_bitset), m_bit_position(other.m_bit_position)
{
    // Nothing here
}

BitSet::ConstIterator::ConstIterator(const BitSet* bitset, u64 bit_position)
    : m_bitset(bitset), m_bit_position(bit_position)
{
    // Nothing here
}

BitSet::ConstIterator::~ConstIterator()
{
    // Nothing here
}

BitSet::ConstIterator& BitSet::ConstIterator::operator = (const ConstIterator& other)
{
    if (&other == this) {
        return *this;
    }

    m_bitset = other.m_bitset;
    m_bit_position = other.m_bit_position;
    return *this;
}

bool BitSet::ConstIterator::operator == (const ConstIterator& other) const
{
    return (other.m_bitset == m_bitset && other.m_bit_position == m_bit_position);
}

bool BitSet::ConstIterator::operator != (const ConstIterator& other) const
{
    return (other.m_bitset != m_bitset || other.m_bit_position != m_bit_position);
}

u64 BitSet::ConstIterator::operator * () const
{
    if (m_bit_position < 0 ||
        (u64)m_bit_position >= m_bitset->get_size_of_universe()) {
        throw BitSetException((std::string)"Attempted to dereference an un-dereferenceable " +
                              "BitSet::iterator object.");
    }
    return m_bit_position;
}

BitSet::ConstIterator& BitSet::ConstIterator::operator ++ ()
{
    m_bit_position = m_bitset->get_next_element_greater_than(m_bit_position);
    return *this;
}

BitSet::ConstIterator BitSet::ConstIterator::operator ++ (int unused)
{
    auto retval = *this;
    ++(*this);
    return retval;
}

BitSet::ConstIterator& BitSet::ConstIterator::operator -- ()
{
    m_bit_position = m_bitset->get_prev_element_lesser_than(m_bit_position);
    return *this;
}

BitSet::ConstIterator BitSet::ConstIterator::operator -- (int unused)
{
    auto retval = *this;
    --(*this);
    return retval;
}

// Implementation of BitSet
inline void BitSet::allocate(u64 size_of_universe)
{
    auto const num_words = num_words_for_bits(size_of_universe);
    m_bit_vector = (WordType*)std::calloc(num_words, sizeof(WordType));
    m_size_of_universe = size_of_universe;
}

inline void BitSet::initialize(u64 size_of_universe, bool initial_value)
{
    if (initial_value) {
        auto const num_words = num_words_for_bits(size_of_universe);
        auto const bits_allocated = num_words * bits_per_word();
        auto const rem = bits_allocated - size_of_universe;
        if (rem == 0) {
            std::memset(m_bit_vector, 0xFF, sizeof(WordType) * num_words);
        } else {
            std::memset(m_bit_vector, 0xFF, sizeof(WordType) * (num_words - 1));
            m_bit_vector[num_words - 1] = ((WordType)1 << rem) - 1;
        }
    }
}

inline void BitSet::initialize(const BitSet& other)
{
    auto const num_words = other.m_size_of_universe;
    auto src_ptr = m_bit_vector;
    auto dst_ptr = other.m_bit_vector;
    memcpy(dst_ptr, src_ptr, sizeof(WordType) * num_words);
}

inline void BitSet::check_out_of_bounds(u64 bit_position) const
{
    if (bit_position >= m_size_of_universe) {
        throw BitSetException((std::string)"Index " + std::to_string(bit_position) +
                              " was out of bounds when used to index a BitSet object.");
    }
}

inline u64 BitSet::construct_mask(u64 bit_position)
{
    u64 retval = 1;
    auto const rem = bit_position % bits_per_word();
    if (rem > 0) {
        retval <<= rem;
    }
    return retval;
}

inline void BitSet::check_equality_of_universes(const BitSet* bitset1,
                                                const BitSet* bitset2)
{
    if (bitset1->m_size_of_universe != bitset2->m_size_of_universe) {
        throw BitSetException((std::string)"Size of universes not the same in binary " +
                              "operation involving two or more BitSet objects.");
    }
}

inline void BitSet::negate_bitset(const BitSet* bitset, BitSet* result)
{
    auto const size_of_universe = bitset->m_size_of_universe;
    auto const len = num_words_for_bits(size_of_universe);
    auto const actual_num_bits = len * bits_per_word();
    auto const rem = actual_num_bits - size_of_universe;
    auto const start_ptr = bitset->m_bit_vector;
    auto const end_ptr = start_ptr + (rem == 0 ? len : (len - 1));
    auto cur_ptr = start_ptr;
    for (cur_ptr = start_ptr; cur_ptr != end_ptr; ++cur_ptr) {
        *cur_ptr = ~(*cur_ptr);
    }
    if (rem != 0) {
        u64 mask = ((u64)1 << rem) - 1;
        *cur_ptr ^= mask;
    }
    return;
}

inline void BitSet::and_with_negated_second_bitsets(const BitSet* bitset1,
                                                    const BitSet* bitset2,
                                                    BitSet* result)
{
    struct OpFun
    {
        inline WordType operator () (WordType arg1, WordType arg2) const
        {
            return (arg1 & (~arg2));
        }
    };
    apply_binary_function_on_bitsets<OpFun>(bitset1, bitset2, result);
}

inline void BitSet::and_bitsets(const BitSet* bitset1, const BitSet* bitset2, BitSet* result)
{
    struct OpFun
    {
        inline WordType operator () (WordType arg1, WordType arg2) const
        {
            return (arg1 & arg2);
        }
    };
    apply_binary_function_on_bitsets<OpFun>(bitset1, bitset2, result);
}

inline void BitSet::or_bitsets(const BitSet* bitset1, const BitSet* bitset2, BitSet* result)
{
    struct OpFun
    {
        inline WordType operator () (WordType arg1, WordType arg2) const
        {
            return (arg1 | arg2);
        }
    };

    apply_binary_function_on_bitsets<OpFun>(bitset1, bitset2, result);
}

inline void BitSet::xor_bitsets(const BitSet* bitset1, const BitSet* bitset2, BitSet* result)
{
    struct OpFun
    {
        inline WordType operator () (WordType arg1, WordType arg2) const
        {
            return (arg1 ^ arg2);
        }
    };

    apply_binary_function_on_bitsets<OpFun>(bitset1, bitset2, result);
}


} /* end namespace eusolver */

//
// BitSet.cpp ends here
