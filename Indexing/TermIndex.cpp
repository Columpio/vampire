
/*
 * File TermIndex.cpp.
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
 * @file TermIndex.cpp
 * Implements class TermIndex.
 */

#include "Lib/DHSet.hpp"
#include "Lib/DHMap.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/Ordering.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/ApplicativeHelper.hpp"
#include "Kernel/SortHelper.hpp"

#include "TermIndexingStructure.hpp"
#include "TermIndex.hpp"

using namespace Lib;
using namespace Kernel;
using namespace Inferences;
using namespace Indexing;

TermIndex::~TermIndex()
{
  delete _is;
}

TermQueryResultIterator TermIndex::getUnifications(TermList t,
	  bool retrieveSubstitutions)
{
  return _is->getUnifications(t, retrieveSubstitutions);
}

TermQueryResultIterator TermIndex::getUnificationsWithConstraints(TermList t,
          bool retrieveSubstitutions)
{
  return _is->getUnificationsWithConstraints(t, retrieveSubstitutions);
}

TermQueryResultIterator TermIndex::getGeneralizations(TermList t,
	  bool retrieveSubstitutions)
{
  return _is->getGeneralizations(t, retrieveSubstitutions);
}

TermQueryResultIterator TermIndex::getInstances(TermList t,
	  bool retrieveSubstitutions)
{
  return _is->getInstances(t, retrieveSubstitutions);
}


void SuperpositionSubtermIndex::handleClause(Clause* c, bool adding)
{
  CALL("SuperpositionSubtermIndex::handleClause");

  TimeCounter tc(TC_BACKWARD_SUPERPOSITION_INDEX_MAINTENANCE);

  unsigned selCnt=c->numSelected();
  for (unsigned i=0; i<selCnt; i++) {
    Literal* lit=(*c)[i];
    TermIterator rsti;
    if(!env.options->combinatorySup()){
      rsti = EqHelper::getSubtermIterator(lit,_ord);
    } else {
      rsti = EqHelper::getFoSubtermIterator(lit,_ord);
    }
    while (rsti.hasNext()) {
      if (adding) {
        _is->insert(rsti.next(), lit, c);
      }
      else {
        _is->remove(rsti.next(), lit, c);
      }
    }
  }
}

void SuperpositionLHSIndex::handleClause(Clause* c, bool adding)
{
  CALL("SuperpositionLHSIndex::handleClause");

  TimeCounter tc(TC_FORWARD_SUPERPOSITION_INDEX_MAINTENANCE);

  unsigned selCnt=c->numSelected();
  for (unsigned i=0; i<selCnt; i++) {
    Literal* lit=(*c)[i];
    TermIterator lhsi=EqHelper::getSuperpositionLHSIterator(lit, _ord, _opt);
    while (lhsi.hasNext()) {
      TermList lhs=lhsi.next();
      if (adding) {
	_is->insert(lhs, lit, c);
      }
      else {
	_is->remove(lhs, lit, c);
      }
    }
  }
}


void SubVarSupSubtermIndex::handleClause(Clause* c, bool adding)
{
  CALL("SubVarSupSubtermIndex::handleClause");

  DHMap<unsigned, LiteralList*> varMap;

  unsigned selCnt=c->numSelected();
  for (unsigned i=0; i<selCnt; i++) {
    Literal* lit=(*c)[i];
    TermIterator rvi=EqHelper::getRewritableVarsIterator(lit,_ord);
    LiteralList* ll;
    while(rvi.hasNext()){
      TermList var = rvi.next();
      if(varMap.find(var.var(), ll)){
        LiteralList::push(lit, ll);
      } else {
        ll = new LiteralList(lit);
        varMap.insert(var.var(), ll);
      }
    }
  }

  for(unsigned i=0; i<c->length() && !varMap.isEmpty(); i++){
    UnstableVarIt uvi((*c)[i]);
    while (uvi.hasNext()) {
      TermList var = uvi.next();
      LiteralList* ll;
      if(varMap.find(var.var())){ //TODO not quite what is required. The same variable could be rewritable and unstable
        varMap.pop(var.var(), ll);
        while(ll){
          Literal* lit = ll->head();
          ll = ll->tail();
          if (adding) {
            _is->insert(var, lit, c);
          } else {
            _is->remove(var, lit, c);
          }
        }
      }
    }
  }
}

void SubVarSupLHSIndex::handleClause(Clause* c, bool adding)
{
  CALL("SubVarSupLHSIndex::handleClause");

  unsigned selCnt=c->numSelected();
  for (unsigned i=0; i<selCnt; i++) {
    Literal* lit=(*c)[i];
    TermIterator lhsi=EqHelper::getSubVarSupLHSIterator(lit, _ord);
    while (lhsi.hasNext()) {
      TermList lhs=lhsi.next();
      if (adding) {
        _is->insert(lhs, lit, c);
      }
      else {
        _is->remove(lhs, lit, c);
      }
    }
  }
}


void NarrowingIndex::populateIndex()
{
  CALL("NarrowingIndex::populateIndex");
 
  typedef ApplicativeHelper AH;

  auto srtOf = [] (TermList t) { 
     ASS(t.isTerm());
     return SortHelper::getResultSort(t.term());
  };

  TermList s1 = TermList(0, false);  
  TermList s2 = TermList(1, false);
  TermList s3 = TermList(2, false);
  TermList x = TermList(3, false);
  TermList y = TermList(4, false);
  TermList z = TermList(5, false);
  TermList args[] = {s1, s2, s3};
  
  unsigned s_comb = env.signature->getCombinator(Signature::S_COMB);
  TermList constant = TermList(Term::create(s_comb, 3, args));
  TermList lhsS = AH::createAppTerm(srtOf(constant), constant, x, y, z);
  TermList rhsS = AH::createAppTerm3(Term::arrowSort(s1, s2, s3), x, z, AH::createAppTerm(Term::arrowSort(s1, s2), y, z));
  Literal* sLit = Literal::createEquality(true, lhsS, rhsS, s3);

  unsigned c_comb = env.signature->getCombinator(Signature::C_COMB);
  constant = TermList(Term::create(c_comb, 3, args));
  TermList lhsC = AH::createAppTerm(srtOf(constant), constant, x, y, z); 
  TermList rhsC = AH::createAppTerm3(Term::arrowSort(s1, s2, s3), x, z, y);
  Literal* cLit = Literal::createEquality(true, lhsC, rhsC, s3);
     
  unsigned b_comb = env.signature->getCombinator(Signature::B_COMB);
  constant = TermList(Term::create(b_comb, 3, args));
  TermList lhsB = AH::createAppTerm(srtOf(constant), constant, x, y, z); 
  TermList rhsB = AH::createAppTerm(Term::arrowSort(s2, s3), x, AH::createAppTerm(Term::arrowSort(s1, s2), y, z));
  Literal* bLit = Literal::createEquality(true, lhsB, rhsB, s3);

  unsigned k_comb = env.signature->getCombinator(Signature::K_COMB);
  constant = TermList(Term::create2(k_comb, s1, s2));
  TermList lhsK = AH::createAppTerm3(srtOf(constant), constant, x, y);
  Literal* kLit = Literal::createEquality(true, lhsK, x, s1);

  unsigned i_comb = env.signature->getCombinator(Signature::I_COMB);
  constant = TermList(Term::create1(i_comb, s1));
  TermList lhsI = AH::createAppTerm(srtOf(constant), constant, x);  
  Literal* iLit = Literal::createEquality(true, lhsI, x, s1);
 
  _is->insert(lhsS, sLit, 0);
  _is->insert(lhsC, cLit, 0);
  _is->insert(lhsB, bLit, 0);
  _is->insert(lhsK, kLit, 0);
  _is->insert(lhsI, iLit, 0);  
}

void DemodulationSubtermIndex::handleClause(Clause* c, bool adding)
{
  CALL("DemodulationSubtermIndex::handleClause");

  TimeCounter tc(TC_BACKWARD_DEMODULATION_INDEX_MAINTENANCE);

  static DHSet<TermList> inserted;

  unsigned cLen=c->length();
  for (unsigned i=0; i<cLen; i++) {
    inserted.reset();
    Literal* lit=(*c)[i];
    NonVariableNonTypeIterator nvi(lit);
    while (nvi.hasNext()) {
      TermList t=nvi.next();
      if (!inserted.insert(t)) {//TODO existing error? Terms are inserted once per a literal
        //It is enough to insert a term only once per clause.
        //Also, once we know term was inserted, we know that all its
        //subterms were inserted as well, so we can skip them.
        nvi.right();
        continue;
      }
      if (adding) {
        _is->insert(t, lit, c);
      }
      else {
        _is->remove(t, lit, c);
      }
    }
  }
}


void DemodulationLHSIndex::handleClause(Clause* c, bool adding)
{
  CALL("DemodulationLHSIndex::handleClause");

  if (c->length()!=1) {
    return;
  }

  TimeCounter tc(TC_FORWARD_DEMODULATION_INDEX_MAINTENANCE);

  Literal* lit=(*c)[0];
  TermIterator lhsi=EqHelper::getDemodulationLHSIterator(lit, true, _ord, _opt);
  while (lhsi.hasNext()) {
    if (adding) {
      _is->insert(lhsi.next(), lit, c);
    }
    else {
      _is->remove(lhsi.next(), lit, c);
    }
  }
}
