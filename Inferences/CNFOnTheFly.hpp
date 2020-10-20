
/*
 * File ProxyElimination.hpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file ProxyElimination.hpp
 * Defines class ProxyElimination.
 */

#ifndef __CNFOnTheFly__
#define __CNFOnTheFly__

#include "Forwards.hpp"
#include "InferenceEngine.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Inference.hpp"

#include "Indexing/TermIndex.hpp"

#include "InferenceEngine.hpp"

#include <memory>

namespace Inferences {
using namespace Indexing;

static Clause* replaceLits(Clause *c, Literal *a, Literal *b, InferenceRule r, bool incAge, Literal *d = 0, Literal* e = 0);
static TermList sigmaRemoval(TermList sigmaTerm, TermList expsrt);
static TermList piRemoval(TermList piTerm, Clause* clause, TermList expsrt);
static InferenceRule convert(Signature::Proxy cnst);
static ClauseIterator produceClauses(Clause* c, bool generating, SkolemisingFormulaIndex* index = 0);


class IFFXORRewriterISE
  : public ImmediateSimplificationEngine
{
public:

  CLASS_NAME(IFFXORRewriterISE);
  USE_ALLOCATOR(IFFXORRewriterISE);

  Clause* simplify(Clause* c);
};

class EagerClausificationISE
  : public ImmediateSimplificationEngine
{
public:

  CLASS_NAME(EagerClausificationISE);
  USE_ALLOCATOR(EagerClausificationISE);

  ClauseIterator simplifyMany(Clause* c);
  Clause* simplify(Clause* c){ NOT_IMPLEMENTED; }

};

class LazyClausification
  : public SimplificationEngine
{
public:
  CLASS_NAME(LazyClausification);
  USE_ALLOCATOR(LazyClausification);

  LazyClausification(){
    _formulaIndex = 0;
  }

  ClauseIterator perform(Clause* c);

  void attach(SaturationAlgorithm* salg) override;
  void detach() override;

private:
  SkolemisingFormulaIndex* _formulaIndex;
};

class LazyClausificationGIE
  : public GeneratingInferenceEngine
{
public:

  CLASS_NAME(LazyClausificationGIE);
  USE_ALLOCATOR(LazyClausificationGIE);

  LazyClausificationGIE(){
    _formulaIndex = 0;
  }

  void attach(SaturationAlgorithm* salg) override;
  void detach() override;

  ClauseIterator generateClauses(Clause* c);

private:
  SkolemisingFormulaIndex* _formulaIndex;
};

/*class NotProxyISE
  : public ImmediateSimplificationEngine
{
public:
  CLASS_NAME(NotProxyISE);
  USE_ALLOCATOR(NotProxyISE);
  
  Kernel::Clause* simplify(Kernel::Clause* c);
};


class EqualsProxyISE
   : public ImmediateSimplificationEngine
{

public:
  CLASS_NAME(EqualsProxyISE);
  USE_ALLOCATOR(EqualsProxyISE);
  
  Kernel::Clause* simplify(Kernel::Clause* c);        
};


class OrImpAndProxyISE
  : public ImmediateSimplificationEngine
{

public:
  CLASS_NAME(OrImpAndProxyISE);
  USE_ALLOCATOR(OrImpAndProxyISE);
  
  Kernel::Clause* simplify(Kernel::Clause* c);
};


class PiSigmaProxyISE
   : public ImmediateSimplificationEngine
{
  
public:
  CLASS_NAME(PiSigmaProxyISE);
  USE_ALLOCATOR(PiSigmaProxyISE);
  
  Kernel::Clause* simplify(Kernel::Clause* c);     
};


class ProxyISE 
  : public ImmediateSimplificationEngine {
  public:
    CLASS_NAME(ProxyISE);
    USE_ALLOCATOR(ProxyISE);
    ClauseIterator simplifyMany(Clause* c);
    Clause* simplify(Clause* c){ NOT_IMPLEMENTED; }
};*/


}

#endif
