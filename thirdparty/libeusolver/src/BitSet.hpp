// BitSet.hpp ---
//
// Filename: BitSet.hpp
// Author: Abhishek Udupa
// Created: Tue Sep 29 14:58:46 2015 (-0400)
//
//
// Copyright (c) 2015, Abhishek Udupa, University of Pennsylvania
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

#if !defined EUSOLVER_BITSET_HPP_
#define EUSOLVER_BITSET_HPP_

#include <string>
#include <utility>
#include <cstring>
#include <cstdlib>
#include <exception>
#include <iterator>

#include "EUSolverTypes.h"

#define BITSET_WORD_TYPE u64
#define BITSET_BITS_PER_BYTE ((u64)8)
#define BITSET_BYTES_PER_WORD (sizeof(BITSET_WORD_TYPE))
#define BITSET_BITS_PER_WORD (BITSET_BYTES_PER_WORD * BITSET_BITS_PER_BYTE)
#define BITSET_NUM_WORDS_FOR_BITS(num_bits__)   \
    ((u64)((num_bits__ + (BITSET_BITS_PER_WORD - 1)) / BITSET_BITS_PER_WORD))
#define BITSET_ALL_ONES_WORD_MASK \
    (((((BITSET_WORD_TYPE)1 << (BITSET_BITS_PER_WORD - 1)) - 1) << 1) | 1)

namespace eusolver {

class BitSetException : public std::exception
{
private:
    std::string m_exception_info;

public:
    inline BitSetException() noexcept
        : m_exception_info("No information")
    {
        // Nothing here
    }

    inline BitSetException(const BitSetException& other) noexcept
        : m_exception_info(other.m_exception_info)
    {
        // Nothing here
    }

    inline BitSetException(BitSetException&& other) noexcept
        : m_exception_info(std::move(other.m_exception_info))
    {
        // Nothing here
    }

    inline BitSetException(const std::string& exception_info) noexcept
        : m_exception_info(exception_info)
    {
        // Nothing here
    }

    virtual ~BitSetException() noexcept
    {
        // Nothing here
    }

    inline BitSetException& operator = (const BitSetException& other) noexcept
    {
        if (&other == this) {
            return *this;
        }
        m_exception_info = other.m_exception_info;
        return *this;
    }

    inline BitSetException& operator = (BitSetException&& other) noexcept
    {
        if (&other == this) {
            return *this;
        }
        std::swap(m_exception_info, other.m_exception_info);
        return *this;
    }

    inline const std::string& get_exception_info() const
    {
        return m_exception_info;
    }

    virtual const char* what() const noexcept
    {
        return m_exception_info.c_str();
    }
};

class BitSet
{
private:
    typedef BITSET_WORD_TYPE WordType;
    WordType* m_bit_vector;
    u64 m_size_of_universe;

    class BitRef
    {
    private:
        BitSet* m_bitset_ptr;
        u64 m_bit_position;

    public:
        inline BitRef()
            : m_bitset_ptr(nullptr), m_bit_position(0)
        {
            // Nothing here
        }

        inline BitRef(const BitRef& other)
            : m_bitset_ptr(other.m_bitset_ptr), m_bit_position(other.m_bit_position)
        {
            // Nothing here
        }

        inline BitRef(BitRef&& other)
            : BitRef()
        {
            std::swap(other.m_bitset_ptr, m_bitset_ptr);
            std::swap(other.m_bit_position, m_bit_position);
        }

        inline BitRef(BitSet* bitset_ptr, u64 bit_position)
            : m_bitset_ptr(bitset_ptr), m_bit_position(bit_position)
        {
            // Nothing here
        }

        inline ~BitRef()
        {
            // Nothing here
        }

        inline BitRef& operator = (const BitRef& other)
        {
            if (&other == this) {
                return *this;
            }
            m_bitset_ptr = other.m_bitset_ptr;
            m_bit_position = other.m_bit_position;
            return *this;
        }

        inline BitRef& operator = (BitRef&& other)
        {
            if (&other == this) {
                return *this;
            }
            std::swap(m_bitset_ptr, other.m_bitset_ptr);
            std::swap(m_bit_position, other.m_bit_position);
            return *this;
        }

        inline BitRef& operator = (bool value)
        {
            if (value) {
                m_bitset_ptr->set_bit(m_bit_position);
            } else {
                m_bitset_ptr->clear_bit(m_bit_position);
            }
        }

        inline operator bool () const
        {
            return m_bitset_ptr->test_bit(m_bit_position);
        }

        inline bool operator == (const BitRef& other) const
        {
            return ((bool)(*this) == (bool)other);
        }

        inline bool operator != (const BitRef& other) const
        {
            return ((bool)(*this) != (bool)other);
        }

        inline bool operator == (bool value) const
        {
            return (bool(*this) == value);
        }

        inline bool operator != (bool value) const
        {
            return (bool(*this) != value);
        }

        inline bool operator ! () const
        {
            return (!((bool)(*this)));
        }
    };

    // helper and utility functions
    inline void allocate(u64 size_of_universe)
    {
        auto const num_words = BITSET_NUM_WORDS_FOR_BITS(size_of_universe);
        m_bit_vector = (WordType*)std::calloc(num_words, sizeof(WordType));
        m_size_of_universe = size_of_universe;
    }

    inline void initialize(u64 size_of_universe, bool initial_value)
    {
        if (initial_value) {
            auto const num_words = BITSET_NUM_WORDS_FOR_BITS(size_of_universe);
            auto const bits_allocated = num_words * BITSET_BITS_PER_WORD;
            auto const rem = bits_allocated - size_of_universe;
            if (rem == 0) {
                std::memset(m_bit_vector, 0xFF, sizeof(WordType) * num_words);
            } else {
                std::memset(m_bit_vector, 0xFF, sizeof(WordType) * (num_words - 1));
                m_bit_vector[num_words - 1] = ((WordType)1 << rem) - 1;
            }
        }
    }

    inline void initialize(const BitSet& other)
    {
        auto const num_words = other.m_size_of_universe;
        auto src_ptr = m_bit_vector;
        auto dst_ptr = other.m_bit_vector;
        memcpy(dst_ptr, src_ptr, sizeof(WordType) * num_words);
    }

    inline void check_out_of_bounds(u64 bit_position) const
    {
        if (bit_position >= m_size_of_universe) {
            throw BitSetException((std::string)"Index " + std::to_string(bit_position) +
                                  " was out of bounds when used to index a BitSet object.");
        }
    }

    inline u64 construct_mask(u64 bit_position) const
    {
        u64 retval = 1;
        auto const rem = bit_position % BITSET_BITS_PER_WORD;
        if (rem > 0) {
            retval <<= rem;
        }
        return retval;
    }

public:
    class Iterator
    {
    private:
        BitSet* m_bit_set;
        u64 m_current_position;

    public:

    };

    class ConstIterator : public std::iterator<std::bidirectional_iterator_tag, u64,
                                               i64, const u64* const u64&>
    {
    private:
        const BitSet* m_bit_set;
        u64 m_current_position;

    public:
        inline ConstIterator()
            : m_bit_set(nullptr), m_current_position(0)
        {
            // Nothing here
        }

        inline ConstIterator(const BitSet* bit_set, u64 current_position)
            : m_bit_set(bit_set), m_current_position(current_position)
        {
            // Nothing here
        }

        inline ConstIterator(const ConstIterator& other)
            : m_bit_set(other.m_bit_set), m_current_position(other.m_current_position)
        {
            // Nothing here
        }

        inline ConstIterator(const Iterator& other)
            : m_bit_set(other.m_bit_set), m_current_position(other.m_current_position)
        {
            // Nothing here
        }

        inline ~ConstIterator()
        {
            // Nothing here
        }

        inline ConstIterator& operator = (const ConstIterator& other)
        {
            if (&other == this) {
                return *this;
            }
            m_bit_set = other.m_bit_set;
            m_current_position = other.m_current_position;
            return *this;
        }

        inline ConstIterator& operator = (const Iterator& other)
        {
            if (&other == this) {
                return *this;
            }
            m_bit_set = other.m_bit_set;
            m_current_position = other.m_current_position;
            return *this;
        }

        inline const u64& operator * () const
        {
            return m_current_position;
        }

        inline ConstIterator& operator ++ ()
        {
            auto const size_of_universe = m_bit_set->get_size_of_universe();
            while (!m_bit_set->test_bit(++m_current_position) &&
                   m_current_position < size_of_universe);
            return *this;
        }

        inline ConstIterator operator ++ (int unused)
        {
            auto retval = *this;
            ++(*this);
            return retval;
        }

        inline ConstIterator& operator -- ()
    };

    inline BitSet()
        : m_bit_vector(nullptr), m_size_of_universe(0)
    {
        // Nothing here
    }

    inline BitSet(const BitSet& other)
        : BitSet()
    {
        allocate(other.m_size_of_universe);
        initialize(other);
    }

    inline BitSet(BitSet&& other)
        : BitSet()
    {
        std::swap(m_bit_vector, other.m_bit_vector);
        std::swap(m_size_of_universe, other.m_size_of_universe);
    }

    inline BitSet(u64 size_of_universe)
        : BitSet()
    {
        allocate(size_of_universe);
    }

    inline BitSet(u64 size_of_universe, bool initial_value)
        : BitSet(size_of_universe)
    {
        allocate(size_of_universe);
        initialize(size_of_universe, initial_value)
    }

    inline ~BitSet()
    {
        if (m_bit_vector != nullptr) {
            std::free(m_bit_vector);
            m_size_of_universe = 0;
        }
    }

    inline BitSet& operator = (const BitSet& other)
    {
        if (&other == this) {
            return *this;
        }

        if (m_bit_vector != nullptr) {
            std::free(m_bit_vector);
            m_bit_vector = nullptr;
        }

        allocate(other.m_size_of_universe);
        initialize(other);
        return *this;
    }

    inline BitSet& operator = (BitSet&& other)
    {
        if (&other == this) {
            return *this;
        }

        std::swap(m_bit_vector, other.m_bit_vector);
        std::swap(m_size_of_universe, other.m_size_of_universe);
        return *this;
    }

    inline bool operator == (const BitSet& other) const
    {
        if (other.m_size_of_universe != m_size_of_universe) {
            return false;
        }

        auto const num_words = BITSET_NUM_WORDS_FOR_BITS(m_size_of_universe);
        return (std::memcmp(m_bit_vector, other.m_bit_vector, sizeof(WordType) * num_words) == 0);
    }

    inline bool operator != (const BitSet& other) const
    {
        return (!((*this) == other));
    }

    // is this a proper subset of other?
    inline bool operator < (const BitSet& other) const
    {
        if (m_size_of_universe != other.m_size_of_universe) {
            throw BitSetException("Incompatible bitsets in subset/superset comparison.");
        }

        auto const num_words = BITSET_NUM_WORDS_FOR_BITS(m_size_of_universe);
        WordType* my_ptr = m_bit_vector;
        WordType* other_ptr = other.m_bit_vector;
        WordType* my_end = my_ptr + num_words;

        bool proper = false;
        while (my_ptr != my_end) {
            if ((*my_ptr & *other_ptr) != *my_ptr) {
                return false;
            }
            proper = (proper || (*my_ptr != *other_ptr));
            ++my_ptr;
            ++other_ptr;
        }
        return proper;
    }

    // is this a subset of other
    inline bool operator <= (const BitSet& other) const
    {
        if (m_size_of_universe != other.m_size_of_universe) {
            throw BitSetException("Incompatible bitsets in subset/superset comparison.");
        }

        auto const num_words = BITSET_NUM_WORDS_FOR_BITS(m_size_of_universe);
        WordType* my_ptr = m_bit_vector;
        WordType* other_ptr = other.m_bit_vector;
        WordType* my_end = my_ptr + num_words;

        while (my_ptr != my_end) {
            if ((*my_ptr & *other_ptr) != *my_ptr) {
                return false;
            }
            ++my_ptr;
            ++other_ptr;
        }
        return true;
    }

    // is this a proper superset of other?
    inline bool operator > (const BitSet& other) const
    {
        return (!((*this) <= other));
    }

    // is this a superset of other?
    inline bool operator >= (const BitSet& other) const
    {
        return (!((*this) < other));
    }

    inline void set_bit(u64 bit_num)
    {
        check_out_of_bounds(bit_num);

        auto const offset = bit_num / BITSET_BITS_PER_WORD;
        auto const mask = construct_mask(bit_num);
        m_bit_vector[offset] |= mask;
    }

    inline void clear_bit(u64 bit_num)
    {
        check_out_of_bounds(bit_num);

        auto const offset = bit_num / BITSET_BITS_PER_WORD;
        auto const mask = construct_mask(bit_num);
        m_bit_vector[offset] &= (~mask);
    }

    inline bool test_bit(u64 bit_num) const
    {
        check_out_of_bounds(bit_num);

        auto const offset = bit_num / BITSET_BITS_PER_WORD;
        auto const mask = construct_mask(bit_num);
        return ((m_bit_vector[offset] & mask) != 0);
    }

    // returns the value of the bit BEFORE the flip
    inline bool flip_bit(u64 bit_num)
    {
        check_out_of_bounds(bit_num);

        auto const offset = bit_num / BITSET_BITS_PER_WORD;
        auto const mask = construct_mask(bit_num);
        const bool retval = ((m_bit_vector[offset] & mask) != 0);
        m_bit_vector[offset] ^= mask;
        return retval;
    }

    // gang set
    inline void set_all()
    {
        initialize(m_size_of_universe, true);
    }

    // gang clear
    inline void clear_all()
    {
        auto const num_words = BITSET_NUM_WORDS_FOR_BITS(m_size_of_universe);
        std::memset(m_bit_vector, 0, num_words * sizeof(WordType));
    }

    // gang flip
    inline void flip_all()
    {
        auto const num_words = BITSET_NUM_WORDS_FOR_BITS(m_size_of_universe);

        for (auto src_ptr = m_bit_vector, src_end = src_ptr + num_words;
             src_ptr != src_end; ++src_ptr) {
            *src_ptr ^= *src_ptr;
        }
    }

    inline bool operator [] (u64 bit_num) const
    {
        return test_bit(bit_num);
    }

    inline BitRef operator [] (u64 bit_num)
    {
        return BitRef(this, bit_num);
    }

    inline u64 get_size_of_universe() const
    {
        return m_size_of_universe;
    }

    inline u64 length() const
    {
        u64 retval = (u64)0;
        auto first = m_bit_vector;
        auto last = first + BITSET_NUM_WORDS_FOR_BITS(m_size_of_universe);
        for (auto current = first; current != last; ++current) {
            auto temp = *current;
            temp = temp - ((temp >> 1) & (u64)0x5555555555555555);
            temp = (temp & (u64)0x3333333333333333) + ((temp >> 2) & (u64)0x3333333333333333);
            temp = (temp + (temp >> 4)) & (u64)0x0F0F0F0F0F0F0F0F;
            retval += ((u64)(temp * (u64)0x0101010101010101) >> 56);
        }

        return retval;
    }

    inline u64 size() const
    {
        return length();
    }

    inline bool is_full() const
    {
        auto const num_words = BITSET_NUM_WORDS_FOR_BITS(m_size_of_universe);
        auto const rem = (num_words * BITSET_BITS_PER_WORD) - m_size_of_universe;
        auto const len = (rem == 0) ? num_words : num_words - 1;
        for (auto src_ptr = m_bit_vector, src_end = src_ptr + len;
             src_ptr != src_end; ++src_ptr) {
            if (*src_ptr != BITSET_ALL_ONES_WORD_MASK) {
                return false;
            }
        }
        if (rem != 0) {
            u64 mask = 1;
            mask <<= rem;
            --mask;
            if (((*(m_bit_vector + len)) & mask) != mask) {
                return false;
            }
        }
        return true;
    }

    inline bool is_empty() const
    {
        auto const num_words = BITSET_NUM_WORDS_FOR_BITS(m_size_of_universe);
        for (auto src_ptr = m_bit_vector, src_end = src_ptr + num_words;
             src_ptr != src_end; ++src_ptr) {
            if (*src_ptr != 0) {
                return false;
            }
        }
        return true;
    }

    BitSet operator & (const BitSet& other) const;
    BitSet operator | (const BitSet& other) const;
    BitSet operator ^ (const BitSet& other) const;
    BitSet operator ~ () const;
    BitSet operator ! () const;
    BitSet operator - (const BitSet& other) const;

    BitSet& operator &= (const BitSet& other);
    BitSet& operator |= (const BitSet& other);
    BitSet& operator ^= (const BitSet& other);
    BitSet& operator -= (const BitSet& other);

    // pointer based methods
    BitSet* intersection_with(const BitSet* other) const;
    void intersect_with_in_place(const BitSet* other);
    BitSet* union_with(const BitSet* other) const;
    void union_with_in_place(const BitSet* other);
    BitSet* symmetric_difference_with(const BitSet* other) const;
    void symmetric_difference_with_in_place(const BitSet* other);
    BitSet* negate() const;
    void negate_in_place();
    BitSet* difference_with(const BitSet* other) const;
    void difference_with_in_place(const BitSet* other);

    u64 hash() const;

    void resize(u64 new_num_bits, bool initial_value = false);
    std::string to_string() const;
    BitSet* clone() const;
};

} /* end namespace eusolver */

#undef BITSET_NUM_WORDS_FOR_BITS
#undef BITSET_BITS_PER_WORD
#undef BITSET_BYTES_PER_WORD
#undef BITSET_BITS_PER_BYTE
#undef BITSET_WORD_TYPE

#endif /* EUSOLVER_BITSET_HPP_ */

//
// BitSet.hpp ends here
