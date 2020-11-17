
#ifndef __PUSH_UNARY_MINUS_H__
#define __PUSH_UNARY_MINUS_H__

#include "Forwards.hpp"

#include "Lib/DHMap.hpp"

#include "Kernel/PolynomialNormalizer.hpp"
#include "Kernel/Theory.hpp"

#include "InferenceEngine.hpp"

namespace Inferences {

class PushUnaryMinus
: public ImmediateSimplificationEngine
{
public:
  CLASS_NAME(PushUnaryMinus);
  USE_ALLOCATOR(PushUnaryMinus);

  virtual ~PushUnaryMinus();

  Clause* simplify(Clause* cl);
};

};

#endif /* __PUSH_UNARY_MINUS_H__ */

