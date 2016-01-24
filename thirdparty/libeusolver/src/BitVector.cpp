// BitVector.cpp ---
// Filename: BitVector.cpp
// Author: Abhishek Udupa
// Created: Sat Jan 23 19:10:24 2016 (-0500)
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

#include "BitVector.hpp"

namespace eusolver {

// Implementation of BitVectorException
BitVectorException::BitVectorException() noexcept
    : m_exception_info("BitVectorException: No information.")
{
    // Nothing here
}

BitVectorException::BitVectorException(const BitVectorException& other) noexcept
    : m_exception_info(other.m_exception_info)
{
    // Nothing here
}

BitVectorException::BitVectorException(BitVectorException&& other) noexcept
    : m_exception_info(std::move(other.m_exception_info))
{
    // Nothing here
}

BitVectorException::BitVectorException(const std::string& exception_info) noexcept
    : m_exception_info((std::string)"BitVectorException: " + exception_info)
{
    // Nothing here
}

BitVectorException::~BitVectorException()
{
    // Nothing here
}

BitVectorException& BitVectorException::operator = (const BitVectorException& other) noexcept
{
    if (&other == this) {
        return *this;
    }
    m_exception_info = other.m_exception_info;
    return *this;
}

BitVectorException& BitVectorException::operator = (BitVectorException&& other) noexcept
{
    if (&other == this) {
        return *this;
    }
    std::swap(m_exception_info, other.m_exception_info);
    return *this;
}

const std::string& BitVectorException::get_exception_info() const noexcept
{
    return m_exception_info;
}

const char* BitVectorException::what() const noexcept
{
    return m_exception_info.c_str();
}


// Implementation of BitVector
BitVector::BitVector()
    : m_bitvector_size(0)
{
    mpz_init(m_representation);
}

BitVector::BitVector(u32 size)
    : m_bitvector_size(size)
{
    mpz_init2(m_representation, size)
}

BitVector::BitVector(u64 value, u32 size)
    : m_bitvector_size(size)
{
    mpz_init2(m_representation, size);
    mpz_set_ui(m_representation, value);
}

BitVector::BitVector(i64 value, u32 size)
    : m_bitvector_size(size)
{
    mpz_init2(m_representation, size);
    mpz_set_si(m_representation, value);
}

BitVector::BitVector(const std::string& value, u32 base, u32 size)
    : m_bitvector_size(size)
{
    mpz_init2(m_representation, size);
    auto stat = mpz_set_str(m_representation, value.c_str(), base);
    if (stat == -1) {
        throw BitVectorException((std::string)"Error parsing bitvector string: " + value);
    }
}

BitVector::BitVector(const char* value, u32 base, u32 size)
{
    mpz_init2(m_representation, size);
    auto stat = mpz_set_str(m_representation, value, base);
    if (stat == -1) {
        throw BitVectorException((std::string)"Error parsing bitvector string: " + value);
    }
}

BitVector::BitVector(const BitVector& other)
    : m_bitvector_size(other.m_bitvector_size)
{
    mpz_init2(m_representation, m_bitvector_size);
    mpz_set(m_representation, other.m_representation);
}

BitVector::BitVector(BitVector&& other)
    : BitVector()
{
    std::swap(m_representation, other.m_representation);
    std::swap(m_bitvector_size, other.m_bitvector_size)
}

} /* end namespace eusolver */

//
// BitVector.cpp ends here
