/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file Normalization.hpp
 * Defines class Normalization
 *
 */

#ifndef __InequalityResolutionCalculus_Normalization__
#define __InequalityResolutionCalculus_Normalization__

#include "Forwards.hpp"

#include "Inferences/InferenceEngine.hpp"
#include "Kernel/Ordering.hpp"
#include "Shell/UnificationWithAbstractionConfig.hpp"
#include "Inferences/PolynomialEvaluation.hpp"
#include "Indexing/InequalityResolutionIndex.hpp"
#include "Kernel/InequalityNormalizer.hpp"

namespace Inferences {
namespace InequalityResolutionCalculus {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class Normalization
: public ImmediateSimplificationEngine 
{
  InequalityNormalizer _normalizer;
public: 
  Normalization(Ordering& ord);
  CLASS_NAME(Normalization);
  USE_ALLOCATOR(Normalization);

  virtual Clause* simplify(Clause* cl) final override;
};

} // namespace InequalityResolutionCalculs
} // namespace Inferences

#endif /*__InequalityResolutionCalculus_Normalization__*/
