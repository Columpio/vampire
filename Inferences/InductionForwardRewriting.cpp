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
 * @file InductionForwardRewriting.cpp
 * Implements class InductionForwardRewriting.
 */

#include "Lib/Metaiterators.hpp"
#include "Lib/PairUtils.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Ordering.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"

#include "Indexing/IndexManager.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Shell/Options.hpp"
#include "Shell/InductionPreprocessor.hpp"

#include "InductionForwardRewriting.hpp"
#include "InductionHelper.hpp"
#include "InductionRemodulation.hpp"

#if VDEBUG
#include <iostream>
using namespace std;
#endif

using namespace Inferences;
using namespace Lib;
using namespace Kernel;
using namespace Saturation;

struct InductionForwardRewriting::GeneralizationsFn {
  GeneralizationsFn(DemodulationLHSIndex *index) : _index(index) {}
  VirtualIterator<pair<pair<Literal *, TermList>, TermQueryResult>> operator()(pair<Literal *, TermList> arg)
  {
    CALL("InductionForwardRewriting::GeneralizationsFn()");
    return pvi(pushPairIntoRightIterator(arg, _index->getGeneralizations(arg.second)));
  }

private:
  DemodulationLHSIndex* _index;
};

struct InductionForwardRewriting::RewriteableSubtermsFn {
  VirtualIterator<pair<Literal *, TermList>> operator()(Literal *lit)
  {
    CALL("InductionForwardRewriting::RewriteableSubtermsFn()");
    NonVariableIterator nvi(lit);
    return pvi(pushPairIntoRightIterator(lit,
                                         getUniquePersistentIteratorFromPtr(&nvi)));
  }
};

struct InductionForwardRewriting::ForwardResultFn {
  ForwardResultFn(Clause *cl, Ordering& ord) : _cl(cl), _ord(ord) {}

  Clause* operator()(pair<pair<Literal *, TermList>, TermQueryResult> arg)
  {
    CALL("InductionForwardRewriting::ForwardResultFn()");

    TermQueryResult &qr = arg.second;
    return InductionForwardRewriting::perform(
      _cl, arg.first.first, arg.first.second, qr.clause,
      qr.literal, qr.term, qr.substitution, _ord);
  }
private:
  Clause *_cl;
  Ordering& _ord;
};

ClauseIterator InductionForwardRewriting::generateClauses(Clause *premise)
{
  CALL("InductionForwardRewriting::generateClauses");

  if (!InductionHelper::isInductionClause(premise) || !InductionHelper::isInductionLiteral((*premise)[0])) {
    return ClauseIterator::getEmpty();
  }

  auto itf1 = premise->iterLits();

  // Get an iterator of pairs of selected literals and rewritable subterms
  // of those literals. Here all subterms of a literal are rewritable.
  auto itf2 = getMapAndFlattenIterator(itf1, RewriteableSubtermsFn());

  // Get clauses with a function definition literal whose lhs is a generalization of the rewritable subterm,
  // returns a pair with the original pair and the generalization result (includes substitution)
  auto itf3 = getMapAndFlattenIterator(itf2, GeneralizationsFn(_index));

  //Perform forward rewriting
  auto it = pvi(getMappingIterator(itf3, ForwardResultFn(premise, _salg->getOrdering())));
  // Remove null elements
  auto it2 = getFilteredIterator(it, NonzeroFn());
  return getTimeCountedIterator(it2, TC_FNDEF_REWRITING);
}

Clause *InductionForwardRewriting::perform(
    Clause *rwClause, Literal *rwLit, TermList rwTerm,
    Clause *eqClause, Literal *eqLit, TermList eqLHS,
    ResultSubstitutionSP subst, Ordering& ord)
{
  CALL("InductionForwardRewriting::perform/2");

  if (SortHelper::getTermSort(rwTerm, rwLit) != SortHelper::getEqualityArgumentSort(eqLit)) {
    // sorts don't match
    return 0;
  }

  ASS(!eqLHS.isVar());

  TermList tgtTerm = EqHelper::getOtherEqualitySide(eqLit, eqLHS);

  TermList tgtTermS;
  if (!subst->isIdentityOnQueryWhenResultBound()) {
    //When we apply substitution to the rhs, we get a term, that is
    //a variant of the term we'd like to get, as new variables are
    //produced in the substitution application.
    TermList lhsSBadVars = subst->applyToResult(eqLHS);
    TermList rhsSBadVars = subst->applyToResult(tgtTerm);
    Renaming rNorm, qNorm, qDenorm;
    rNorm.normalizeVariables(lhsSBadVars);
    qNorm.normalizeVariables(tgtTerm);
    qDenorm.makeInverse(qNorm);
    ASS_EQ(rwTerm, qDenorm.apply(rNorm.apply(lhsSBadVars)));
    tgtTermS = qDenorm.apply(rNorm.apply(rhsSBadVars));
  }
  else {
    tgtTermS = subst->applyToBoundResult(tgtTerm);
  }

  Literal *tgtLitS = EqHelper::replace(rwLit, rwTerm, tgtTermS);
  if (EqHelper::isEqTautology(tgtLitS)) {
    return 0;
  }

  unsigned rwLength = rwClause->length();
  unsigned eqLength = eqClause->length();
  unsigned newLength = rwLength + eqLength - 1;

  Inference inf(GeneratingInference2(InferenceRule::INDUCTION_FORWARD_REWRITING, rwClause, eqClause));
  Clause *res = new (newLength) Clause(newLength, inf);

  static bool doSimS = env.options->simulatenousSuperposition();
  (*res)[0] = tgtLitS;

  unsigned next = 1;
  for (unsigned i = 0; i < rwLength; i++) {
    Literal *curr = (*rwClause)[i];
    if (curr != rwLit) {
      if (doSimS) {
        curr = EqHelper::replace(curr, rwTerm, tgtTermS);
      }

      if (EqHelper::isEqTautology(curr)) {
        res->destroy();
        return 0;
      }

      (*res)[next++] = curr;
    }
  }

  {
    for (unsigned i = 0; i < eqLength; i++) {
      Literal *curr = (*eqClause)[i];
      if (curr != eqLit) {
        Literal *currAfter;
        if (!subst->isIdentityOnQueryWhenResultBound()) {
          // same as above for RHS
          TermList lhsSBadVars = subst->applyToResult(eqLHS);
          Literal *currSBadVars = subst->applyToResult(curr);
          Renaming rNorm, qNorm, qDenorm;
          rNorm.normalizeVariables(lhsSBadVars);
          qNorm.normalizeVariables(curr);
          qDenorm.makeInverse(qNorm);
          ASS_EQ(rwTerm, qDenorm.apply(rNorm.apply(lhsSBadVars)));
          currAfter = qDenorm.apply(rNorm.apply(currSBadVars));
        }
        else {
          currAfter = subst->applyToBoundResult(curr);
        }

        if (EqHelper::isEqTautology(currAfter)) {
          res->destroy();
          return 0;
        }

        (*res)[next++] = currAfter;
      }
    }
  }

  auto rinfos = RemodulationInfo::update(res, tgtLitS,
    static_cast<DHSet<RemodulationInfo>*>(rwClause->getRemodulationInfo()), ord);

  if (rinfos->isEmpty()) {
    delete rinfos;
  } else {
    res->setRemodulationInfo(rinfos);
    res->setInductionLemma(true);
  }
  return res;
}
