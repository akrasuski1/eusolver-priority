// BitVector.hpp ---
// Filename: BitVector.hpp
// Author: Abhishek Udupa
// Created: Sat Jan 23 19:10:43 2016 (-0500)
//
// Copyright (c) 2016, Abhishek Udupa, University of Pennsylvania
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

#if !defined EUSOLVER_BITVECTOR_HPP_
#define EUSOLVER_BITVECTOR_HPP_

#include <string>
#include <exception>
#include <gmp.h>

#include "EUSolverTypes.h"

namespace eusolver {

class BitVectorException : public std::exception
{
private:
    std::string m_exception_info;

public:
    BitVectorException() noexcept;
    BitVectorException(const BitVectorException& other) noexcept;
    BitVectorException(BitVectorException&& other) noexcept;
    BitVectorException(const std::string& exception_info) noexcept;
    virtual ~BitVectorException() noexcept;
    BitVectorException& operator = (const BitVectorException& other) noexcept;
    BitVectorException& operator = (BitVectorException&& other) noexcept;
    const std::string& get_exception_info() const noexcept;
    virtual const char* what() const noexcept override;
};

class BitVector
{
private:
    mpz_t m_representation;
    u32 m_bitvector_size;

public:
    BitVector();
    explicit BitVector(u32 size);
    BitVector(u64 value, u32 size);
    BitVector(i64 value, u32 size);
    BitVector(const std::string& value, u32 base, u32 size);
    BitVector(const char* value, u32 base, u32 size);

    BitVector(const BitVector& other);
    BitVector(BitVector&& other);

    ~BitVector();

    BitVector& operator = (const BitVector& other);
    BitVector& operator = (BitVector&& other);

    BitVector& operator = (u64 value);

    bool operator == (const BitVector& other) const;
    bool operator != (const BitVector& other) const;
    bool operator < (const BitVector& other) const;
    bool operator <= (const BitVector& other) const;
    bool operator > (const BitVector& other) const;
    bool operator >= (const BitVector& other) const;

    bool operator == (u64 other) const;
    bool operator != (u64 other) const;
    bool operator < (u64 other) const;
    bool operator <= (u64 other) const;
    bool operator > (u64 other) const;
    bool operator >= (u64 other) const;

    bool unsigned_lt(const BitVector& other) const;
    bool unsigned_le(const BitVector& other) const;
    bool unsigned_gt(const BitVector& other) const;
    bool unsigned_ge(const BitVector& other) const;

    bool signed_lt(const BitVector& other) const;
    bool signed_le(const BitVector& other) const;
    bool signed_gt(const BitVector& other) const;
    bool signed_ge(const BitVector& other) const;

    BitVector operator + (const BitVector& other) const;
    BitVector& operator += (const BitVector& other);
    BitVector add(const BitVector& other) const;
    void add_inplace(const BitVector& other) const;

    BitVector operator + (i64 other) const;
    BitVector& operator += (i64 other);
    BitVector add(i64 other) const;
    void add_inplace(i64 other) const;

    BitVector operator - (const BitVector& other) const;
    BitVector& operator -= (const BitVector& other);
    BitVector sub(const BitVector& other) const;
    void sub_inplace(const BitVector& other);

    BitVector operator - (i64 other) const;
    BitVector& operator -= (i64 other);
    BitVector sub(i64 other) const;
    void sub_inplace(i64 other);

    BitVector operator ~ () const;
    BitVector logical_negate() const;
    void logical_negate_inplace();

    BitVector operator & (const BitVector& other) const;
    BitVector& operator &= (const BitVector& other);
    BitVector logical_and(const BitVector& other) const;
    void logical_and_inplace(const BitVector& other);

    BitVector operator | (const BitVector& other) const;
    BitVector& operator |= (const BitVector& other);
    BitVector logical_ior(const BitVector& other) const;
    void logical_ior_inplace(const BitVector& other);

    BitVector operator ^ (const BitVector& other) const;
    BitVector& operator ^= (const BitVector& other);
    BitVector logical_xor(const BitVector& other) const;
    void logical_xor_inplace(const BitVector& other);

    BitVector operator << (u32 shift_amount) const;
    BitVector operator << (const BitVector& shift_amount) const;
    BitVector& operator <<= (u32 shift_amount);
    BitVector& operator <<= (const BitVector& shift_amount);

    BitVector logical_shift_left(u32 shift_amount) const;
    void logical_shift_left_inplace(u32 shift_amount);
    BitVector logical_shift_left(const BitVector& shift_amount) const;
    void logical_shift_left_inplace(const BitVector& shift_amount);

    BitVector operator >> (u32 shift_amount) const;
    BitVector operator >> (const BitVector& shift_amount) const;
    BitVector& operator >>= (u32 shift_amount);
    BitVector& operator >>= (const BitVector& shift_amount);

    BitVector logical_shift_right(u32 shift_amount) const;
    void logical_shift_right_inplace(u32 shift_amount);
    BitVector logical_shift_right(const BitVector& shift_amount) const;
    void logical_shift_right_inplace(const BitVector& shift_amount);

    BitVector arithmetic_shift_right(u32 shift_amount) const;
    void arithmetic_shift_right(u32 shift_amount);
    BitVector arithmetic_shift_right(const BitVector& shift_amount) const;
    void arithmetic_shift_right_inplace(const BitVector& shift_amount);
};

} /* end namespace eusolver */

#endif /* EUSOLVER_BITVECTOR_HPP_ */

//
// BitVector.hpp ends here
