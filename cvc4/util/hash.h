/*********************                                                        */
/*! \file hash.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Christopher L. Conway, Paul Meng
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "cvc4_public.h"

#ifndef __CVC4__HASH_H
#define __CVC4__HASH_H

#include <functional>
#include <string>

namespace std {

#ifdef CVC4_NEED_HASH_UINT64_T
// on some versions and architectures of GNU C++, we need a
// specialization of hash for 64-bit values
template <>
struct hash<uint64_t> {
  size_t operator()(uint64_t v) const {
    return v;
  }
};/* struct hash<uint64_t> */
#endif /* CVC4_NEED_HASH_UINT64_T */

}/* std namespace */

namespace CVC4 {


template <class T, class U, class HashT = std::hash<T>, class HashU = std::hash<U> >
struct PairHashFunction {
  size_t operator()(const std::pair<T, U>& pr) const {
    return HashT()(pr.first) ^ HashU()(pr.second);
  }
};/* struct PairHashFunction */

}/* CVC4 namespace */

#endif /* __CVC4__HASH_H */
