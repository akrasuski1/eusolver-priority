// MultiLabelDecisionTreeLearner.cpp ---
//
// Filename: MultiLabelDecisionTreeLearner.cpp
// Author: Abhishek Udupa
// Created: Mon Oct  5 12:44:50 2015 (-0400)
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

#include <limits>

#include "MultiLabelDecisionTreeLearner.hpp"

#define EUSOLVER_DEBUG_DT_CHECK_INPUTS_ 1

namespace eusolver {
namespace multilabel_decision_tree_learner {

namespace detail_ {

typedef std::vector<const BitSet*> InputVector;

static inline void
check_dt_learning_inputs(const InputVector& attribute_vector,
                         const InputVector& labelling_vector)
{
    if (attribute_vector.size() != labelling_vector.size()) {
        throw DecisionTreeException((std::string)"Attribute and label data do not " +
                                    "have the same length.");
    }
    if (attribute_vector.size() == 0) {
        throw DecisionTreeException((std::string)"Inputs to decision tree learning cannot " +
                                    "be empty.");
    }
}

static inline i64 check_for_common_label(const InputVector& labelling_vector,
                                         const BitSet& sample_point_filter)
{
    BitSet accumulator = *(labelling_vector[0]);
    for (u64 i = 1, lim = labelling_vector.size(); i < lim; ++i) {
        if (sample_point_filter.test_bit(i)) {
            accumulator &= (*labelling_vector[i]);
        }
    }
    if (!(accumulator.is_empty())) {
        return accumulator.get_next_element_greater_than_or_equal_to(0);
    } else {
        return -1;
    }
}

static inline double
get_entropy_for_split(const InputVector& attribute_vector,
                      const InputVector& labelling_vector,
                      u64 attribute_to_split_on)
{
    return 0;
}

static inline const DecisionTreeNodeBase*
learn_dt_for_ml_data(const InputVector& attribute_vector,
                     const InputVector& labelling_vector,
                     const BitSet& sample_point_filter)
{

#if (EUSOLVER_DEBUG_DT_CHECK_INPUTS_ != 0)
    check_dt_learning_inputs(attribute_vector, labelling_vector);
#endif /* EUSOLVER_DEBUG_DT_CHECK_INPUTS_ */

    // check if we can exit early, that is if we have a common label
    auto const common_label_id = check_for_common_label(labelling_vector, sample_point_filter);
    if (common_label_id >= 0) {
        return new DecisionTreeLeafNode(common_label_id);
    }

    // Early exit not possible
    double max_weighted_entropy = std::numeric_limits<double>::min();
    i64 best_split_attribute = -1;
    auto const num_attributes = attribute_vector[0]->get_size_of_universe();
    auto const sample_point_universe_size = attribute_vector.size();

    for (u64 i = 0; i < num_attributes; ++i) {
        auto split_entropy = get_entropy_for_split(attribute_vector, labelling_vector, i);
        if (split_entropy > max_weighted_entropy) {
            best_split_attribute = i;
            max_weighted_entropy = split_entropy;
        }
    }

    // make the split on the chosen attribute
    auto positive_filter = sample_point_filter;
    for (u64 i = 0; i < sample_point_universe_size; ++i) {

    }
}

/**
   transposes an input vector, which contains one bitset for EACH
   input point/sample point, into another vector of bitsets "result".
   The number of elements in result is equal to the UNIVERSE of the
   bitsets in the input vector. The universe of each of the bitsets
   in the result is equal to the number of input points/sample points
   in the input vector
 */
static inline void
transpose_sample_point_major_vectors(const InputVector& input_vector,
                                     InputVector& result_vector)
{
    result_vector.clear();
    if (input_vector.size() == 0) {
        return;
    }

    auto const size_of_input_universe = input_vector[0]->get_size_of_universe();
    auto const num_input_points = input_vector.size();


}

template <typename PtrType>
static inline void free_ptr_vector(const std::vector<PtrType>& the_vector)
{
    auto const num_elems = the_vector.size();
    for (u64 i = 0; i < num_elems; ++i) {
        delete the_vector[i];
    }
}

} /* end namespace detail_ */


// Implementation of DecisionTreeException
DecisionTreeException::DecisionTreeException() noexcept
    : m_exception_info("DecisionTreeException: No information.")
{
    // Nothing here
}

DecisionTreeException::DecisionTreeException(const std::string& exception_info) noexcept
    : m_exception_info((std::string)"DecisionTreeException: " + exception_info)
{
    // Nothing here
}

DecisionTreeException::DecisionTreeException(const DecisionTreeException& other) noexcept
    : m_exception_info(other.m_exception_info)
{
    // Nothing here
}

DecisionTreeException::DecisionTreeException(DecisionTreeException&& other) noexcept
    : m_exception_info(std::move(other.m_exception_info))
{
    // Nothing here
}

DecisionTreeException::~DecisionTreeException() noexcept
{
    // Nothing here
}

DecisionTreeException&
DecisionTreeException::operator = (const DecisionTreeException& other) noexcept
{
    if (&other == this) {
        return *this;
    }
    m_exception_info = other.m_exception_info;
    return *this;
}

DecisionTreeException&
DecisionTreeException::operator = (DecisionTreeException&& other) noexcept
{
    if (&other == this) {
        return *this;
    }
    m_exception_info = std::move(other.m_exception_info);
    return *this;
}

const std::string& DecisionTreeException::get_exception_info() const noexcept
{
    return m_exception_info;
}

const char* DecisionTreeException::what() const noexcept
{
    return m_exception_info.c_str();
}


// Implementation of actual learning methods

/**
   attribute_vector: A vector containing one bitset for EACH sample point.
                     Each bitset contains the identifiers of the "guards"
                     that evaluate to true at that point.
   labelling_vector: A vector containing one bitset for EACH sample point.
                     Each bitset contains the identifiers of the "terms" that
                     satisfy the specification at that point.
 */
const DecisionTreeNodeBase*
learn_decision_tree_for_multi_labelled_data(const std::vector<const BitSet*>& attribute_vector,
                                            const std::vector<const BitSet*>& labelling_vector)
{
    BitSet sample_point_filter(attribute_vector.size(), true);
    return detail_::learn_dt_for_ml_data(attribute_vector,
                                         labelling_vector,
                                         sample_point_filter);
}

#undef EUSOLVER_DEBUG_DT_CHECK_INPUTS_

} /* end namespace multilabel_decision_tree_learner */
} /* end namespace eusolver */

//
// MultiLabelDecisionTreeLearner.cpp ends here
