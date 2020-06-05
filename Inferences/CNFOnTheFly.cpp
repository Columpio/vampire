
/*
 * File ProxyElimination.cpp.
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
 * @file ProxyElimination.cpp
 *
 */

#include "Lib/Environment.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Sorts.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/ApplicativeHelper.hpp"

#include "Shell/Statistics.hpp"
#include "Shell/Skolem.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "CNFOnTheFly.hpp"

namespace Inferences {
using namespace Indexing;

typedef ApplicativeHelper AH;

Clause* NotProxyISE::simplify(Clause* c){
  CALL("NotProxyISE::simplify");

  TermList boolSort = Term::boolSort();
  TermList troo = TermList(Term::foolTrue());
  TermList fols = TermList(Term::foolFalse());

  static TermStack args;
  TermList head;
 
  for(int i = c->length()-1; i>=0; i--){
    Literal* lit = (*c)[i];
    TermList lhs = *lit->nthArgument(0);
    TermList rhs = *lit->nthArgument(1);
    TermList term;
    TermList boolVal;
    if(AH::isBool(lhs)){
      boolVal = lhs;
      term = rhs;
    } else if(AH::isBool(rhs)){
      boolVal = rhs;
      term = lhs;
    } else {
      continue;
    }

    bool positive = AH::isTrue(boolVal) == lit->polarity();

    AH::getHeadAndArgs(term, head, args);
    Signature::Proxy prox = AH::getProxy(head);

    if((prox == Signature::NOT) && (args.size())){
      TermList rhs = positive ? fols : troo;
      Literal* l1 = Literal::createEquality(true, args[0], rhs, boolSort);
      Inference *inf = new Inference1(convert(prox), c);      
      Clause* res = replaceLits(c, lit, l1, inf);
      res->setAge(c->age());
      return res;
    }
  }

  return c;
}

Clause* EqualsProxyISE::simplify(Clause* c){
  CALL("EqualsProxyISE::simplify");

  TermList boolSort = Term::boolSort();
  TermList troo = TermList(Term::foolTrue());
  TermList fols = TermList(Term::foolFalse());

  static TermStack args;
  TermList head;
 
  for(int i = c->length()-1; i >=0; i--){
    Literal* lit = (*c)[i];
    TermList lhs = *lit->nthArgument(0);
    TermList rhs = *lit->nthArgument(1);
    TermList term;
    TermList boolVal;
    if(AH::isBool(lhs)){
      boolVal = lhs;
      term = rhs;
    } else if(AH::isBool(rhs)){
      boolVal = rhs;
      term = lhs;
    } else {
      continue;
    }

    bool positive = AH::isTrue(boolVal) == lit->polarity();

    AH::getHeadAndArgs(term, head, args);
    Signature::Proxy prox = AH::getProxy(head);

    if((prox == Signature::EQUALS) && (args.size() == 2)){
      TermList srt = *SortHelper::getResultSort(head.term()).term()->nthArgument(0);
      Literal* l1 = Literal::createEquality(positive, args[0], args[1], srt);
      Inference *inf = new Inference1(convert(prox), c);
      Clause* res = replaceLits(c, lit, l1, inf);
      res->setAge(c->age());
      return res;
    }
  }

  return c;
}

Clause* PiSigmaProxyISE::simplify(Clause* c){
  CALL("PiSigmaProxyISE::simplify");

  TermList boolSort = Term::boolSort();
  TermList troo = TermList(Term::foolTrue());
  TermList fols = TermList(Term::foolFalse());

  static TermStack args;
  TermList head;
 
  for(int i = c->length() - 1 ; i >= 0; i--){
    Literal* lit = (*c)[i];
    TermList lhs = *lit->nthArgument(0);
    TermList rhs = *lit->nthArgument(1);
    TermList term;
    TermList boolVal;
    if(AH::isBool(lhs)){
      boolVal = lhs;
      term = rhs;
    } else if(AH::isBool(rhs)){
      boolVal = rhs;
      term = lhs;
    } else {
      continue;
    }

    bool positive = AH::isTrue(boolVal) == lit->polarity();

    AH::getHeadAndArgs(term, head, args);
    Signature::Proxy prox = AH::getProxy(head);

    if((prox == Signature::PI || prox == Signature::SIGMA ) && (args.size())){
      TermList rhs = positive ? troo : fols; 
      TermList srt = *SortHelper::getResultSort(head.term()).term()->nthArgument(0);
      TermList newTerm;
      Inference *inf;
      if((prox == Signature::PI && positive) || 
         (prox == Signature::SIGMA && !positive)){
        inf = new Inference1(convert(Signature::PI), c);
        newTerm = piRemoval(args[0], c, srt);
      } else {
        TermList skolemTerm = sigmaRemoval(args[0], srt);
        newTerm = AH::createAppTerm(srt, args[0], skolemTerm);
        inf = new Inference1(convert(Signature::SIGMA), c);
      }
      Literal* l1 = Literal::createEquality(true, newTerm, rhs, boolSort);
      Clause* res = replaceLits(c, lit, l1, inf);
      res->setAge(c->age());
      return res;
    }
  }

  return c;
}

Clause* OrImpAndProxyISE::simplify(Clause* c){
  CALL("rImpAndProxyISE::simplify"); 

  TermList boolSort = Term::boolSort();
  TermList troo = TermList(Term::foolTrue());
  TermList fols = TermList(Term::foolFalse());

  static TermStack args;
  TermList head;
 
  for(int i = c->length() -1; i >=0; i--){
    Literal* lit = (*c)[i];
    TermList lhs = *lit->nthArgument(0);
    TermList rhs = *lit->nthArgument(1);
    TermList term;
    TermList boolVal;
    if(AH::isBool(lhs)){
      boolVal = lhs;
      term = rhs;
    } else if(AH::isBool(rhs)){
      boolVal = rhs;
      term = lhs;
    } else {
      continue;
    }

    bool positive = AH::isTrue(boolVal) == lit->polarity();

    AH::getHeadAndArgs(term, head, args);
    Signature::Proxy prox = AH::getProxy(head);

    if((prox == Signature::OR) && (args.size() == 2)){
      if(positive){
        Literal* l1 = Literal::createEquality(true, args[1], troo, boolSort);
        Literal* l2 = Literal::createEquality(true, args[0], troo, boolSort);
        Inference *inf = new Inference1(convert(prox), c);   
        Clause* res = replaceLits(c, lit, l1, inf, l2);
        res->setAge(c->age());
        return res;
      }
    }
  
    if((prox == Signature::AND) && (args.size() == 2)){
      if(!positive){
        Literal* l1 = Literal::createEquality(true, args[1], fols, boolSort);
        Literal* l2 = Literal::createEquality(true, args[0], fols, boolSort);
        Inference *inf = new Inference1(convert(prox), c);
        Clause* res = replaceLits(c, lit, l1, inf, l2);
        res->setAge(c->age());
        return res;
      }
    }

    if((prox == Signature::IMP) && (args.size() == 2)){
      if(positive){
        Literal* l1 = Literal::createEquality(true, args[1], fols, boolSort);
        Literal* l2 = Literal::createEquality(true, args[0], troo, boolSort);
        Inference *inf = new Inference1(convert(prox), c);   
        Clause* res = replaceLits(c, lit, l1, inf, l2);
        res->setAge(c->age());
        return res;
      }
    }
  }

  return c;
} 

ClauseIterator ProxyISE::simplifyMany(Clause* c){
  CALL("ProxyISE::simplifyMany");

  TermList troo = TermList(Term::foolTrue());
  TermList fols = TermList(Term::foolFalse());
  TermList boolSort = Term::boolSort();

  static TermStack args;
  TermList head;
 
  ClauseStack resultStack;
  unsigned clength = c->length();

  for(unsigned i = 0; i < clength; i++){
    Literal* lit = (*c)[i];
    TermList lhs = *lit->nthArgument(0);
    TermList rhs = *lit->nthArgument(1);
    TermList term;
    TermList boolVal;
    if(AH::isBool(lhs)){
      boolVal = lhs;
      term = rhs;
    } else if(AH::isBool(rhs)){
      boolVal = rhs;
      term = lhs;
    } else if(SortHelper::getEqualityArgumentSort(lit) == boolSort) {
      //equality or diseqality between boolean terms
      Literal* lhsTroo = Literal::createEquality(true, lhs, troo, boolSort);
      Literal* lhsFols = Literal::createEquality(true, lhs, fols, boolSort);
      Literal* rhsTroo = Literal::createEquality(true, rhs, troo, boolSort);
      Literal* rhsFols = Literal::createEquality(true, rhs, fols, boolSort);
      if(lit->polarity()){
        Inference* inf1 = new Inference1(convert(Signature::IFF), c);
        Inference* inf2 = new Inference1(convert(Signature::IFF), c);
        Clause* res1 = replaceLits(c, lit, lhsTroo, inf1, rhsFols);
        Clause* res2 = replaceLits(c, lit, lhsFols, inf2, rhsTroo);
        res1->setAge(c->age()+1);
        res2->setAge(c->age()+1);
        resultStack.push(res1);
        resultStack.push(res2);
      } else {
        Inference* inf1 = new Inference1(convert(Signature::XOR), c);
        Inference* inf2 = new Inference1(convert(Signature::XOR), c);
        Clause* res1 = replaceLits(c, lit, lhsTroo, inf1, rhsTroo);
        Clause* res2 = replaceLits(c, lit, lhsFols, inf2, rhsFols);
        res1->setAge(c->age()+1);
        res2->setAge(c->age()+1);
        resultStack.push(res1);
        resultStack.push(res2);
      }
      goto afterLoop;
    } else {
      continue;
    }

    AH::getHeadAndArgs(term, head, args);
    Signature::Proxy prox = AH::getProxy(head);
    if(prox == Signature::NOT_PROXY){
      continue;
    }

    bool positive = AH::isTrue(boolVal) == lit->polarity();

    if((prox == Signature::OR) && (args.size() == 2)){
      if(!positive){
        Literal* l1 = Literal::createEquality(true, args[1], fols, boolSort);
        Literal* l2 = Literal::createEquality(true, args[0], fols, boolSort);
        Inference* inf1 = new Inference1(convert(prox), c);
        Inference* inf2 = new Inference1(convert(prox), c);
        Clause* res1 = replaceLits(c, lit, l1, inf1);
        Clause* res2 = replaceLits(c, lit, l2, inf2);
        res1->setAge(c->age()+1);
        res2->setAge(c->age()+1);
        resultStack.push(res1);
        resultStack.push(res2);
        goto afterLoop;
      }
    }
  
    if((prox == Signature::AND) && (args.size() == 2)){
      if(positive){
        Literal* l1 = Literal::createEquality(true, args[1], troo, boolSort);
        Literal* l2 = Literal::createEquality(true, args[0], troo, boolSort);
        Inference* inf1 = new Inference1(convert(prox), c); 
        Inference* inf2 = new Inference1(convert(prox), c);     
        Clause* res1 = replaceLits(c, lit, l1, inf1);
        Clause* res2 = replaceLits(c, lit, l2, inf2);        
        res1->setAge(c->age()+1);
        res2->setAge(c->age()+1);
        resultStack.push(res1);
        resultStack.push(res2);
        goto afterLoop;
      }
    }

    if((prox == Signature::IMP) && (args.size() == 2)){
      if(!positive){
        Literal* l1 = Literal::createEquality(true, args[1], troo, boolSort);
        Literal* l2 = Literal::createEquality(true, args[0], fols, boolSort);
        Inference* inf1 = new Inference1(convert(prox), c);
        Inference* inf2 = new Inference1(convert(prox), c);
        Clause* res1 = replaceLits(c, lit, l1, inf1);
        Clause* res2 = replaceLits(c, lit, l2, inf2);        
        res1->setAge(c->age()+1);
        res2->setAge(c->age()+1);
        resultStack.push(res1);
        resultStack.push(res2);
        goto afterLoop;
      }
    }

    if((prox == Signature::IFF || prox == Signature::XOR) && (args.size() == 2)){
      bool polarity = (prox == Signature::IFF) == positive;
      //equality or diseqality between boolean terms
      Literal* lhsTroo = Literal::createEquality(true, args[1], troo, boolSort);
      Literal* lhsFols = Literal::createEquality(true, args[1], fols, boolSort);
      Literal* rhsTroo = Literal::createEquality(true, args[0], troo, boolSort);
      Literal* rhsFols = Literal::createEquality(true, args[0], fols, boolSort);
      if(polarity){
        Inference* inf1 = new Inference1(convert(Signature::IFF), c);
        Inference* inf2 = new Inference1(convert(Signature::IFF), c);
        Clause* res1 = replaceLits(c, lit, lhsTroo, inf1, rhsFols);
        Clause* res2 = replaceLits(c, lit, lhsFols, inf2, rhsTroo);
        res1->setAge(c->age()+1);
        res2->setAge(c->age()+1);
        resultStack.push(res1);
        resultStack.push(res2);
      } else {
        Inference* inf1 = new Inference1(convert(Signature::XOR), c);
        Inference* inf2 = new Inference1(convert(Signature::XOR), c);
        Clause* res1 = replaceLits(c, lit, lhsTroo, inf1, rhsTroo);
        Clause* res2 = replaceLits(c, lit, lhsFols, inf2, rhsFols);
        res1->setAge(c->age()+1);
        res2->setAge(c->age()+1);
        resultStack.push(res1);
        resultStack.push(res2);
      }
      goto afterLoop;
    }
  }

  return ClauseIterator::getEmpty(); 

afterLoop:  

  return pvi(getUniquePersistentIterator(ClauseStack::Iterator(resultStack)));

}

ClauseIterator produceClauses(Clause* c, bool generating, SkolemisingFormulaIndex* index)
{
  CALL("CNFOnTheFly::produceClauses");

  static bool eager = env.options->cnfOnTheFly() == Options::CNFOnTheFly::EAGER;
  static bool simp = env.options->cnfOnTheFly() == Options::CNFOnTheFly::LAZY_SIMP;
  static bool gen = env.options->cnfOnTheFly() == Options::CNFOnTheFly::LAZY_GEN;
  static bool simp_except_not_be_off = env.options->cnfOnTheFly() == Options::CNFOnTheFly::LAZY_SIMP_NOT_GEN_BOOL_EQ_OFF;
  static bool simp_except_not_and_be = env.options->cnfOnTheFly() == Options::CNFOnTheFly::LAZY_SIMP_NOT_GEN_BOOL_EQ_GEN;
  bool not_be = simp_except_not_be_off || (!generating && simp_except_not_and_be);


  if(generating && (eager || simp)){ return ClauseIterator::getEmpty(); }
  if(!generating && gen){ return ClauseIterator::getEmpty(); }

  TermList troo = TermList(Term::foolTrue());
  TermList fols = TermList(Term::foolFalse());
  TermList boolSort = Term::boolSort();

  static TermStack args;
  TermList head;
 
  ClauseStack resultStack;
  unsigned clength = c->length();

  for(unsigned i = 0; i < clength; i++){
    Literal* lit = (*c)[i];
    TermList lhs = *lit->nthArgument(0);
    TermList rhs = *lit->nthArgument(1);
    TermList term;
    TermList boolVal;
    if(AH::isBool(lhs)){
      boolVal = lhs;
      term = rhs;
    } else if(AH::isBool(rhs)){
      boolVal = rhs;
      term = lhs;
    } else if(SortHelper::getEqualityArgumentSort(lit) == boolSort && !not_be) {
      //equality or diseqality between boolean terms
      Literal* lhsTroo = Literal::createEquality(true, lhs, troo, boolSort);
      Literal* lhsFols = Literal::createEquality(true, lhs, fols, boolSort);
      Literal* rhsTroo = Literal::createEquality(true, rhs, troo, boolSort);
      Literal* rhsFols = Literal::createEquality(true, rhs, fols, boolSort);
      if(lit->polarity()){
        Inference* inf1 = new Inference1(convert(Signature::IFF), c);
        Inference* inf2 = new Inference1(convert(Signature::IFF), c);
        Clause* res1 = replaceLits(c, lit, lhsTroo, inf1, rhsFols);
        Clause* res2 = replaceLits(c, lit, lhsFols, inf2, rhsTroo);
        res1->setAge(c->age()+1);
        res2->setAge(c->age()+1);
        resultStack.push(res1);
        resultStack.push(res2);
      } else {
        Inference* inf1 = new Inference1(convert(Signature::XOR), c);
        Inference* inf2 = new Inference1(convert(Signature::XOR), c);
        Clause* res1 = replaceLits(c, lit, lhsTroo, inf1, rhsTroo);
        Clause* res2 = replaceLits(c, lit, lhsFols, inf2, rhsFols);
        res1->setAge(c->age()+1);
        res2->setAge(c->age()+1);
        resultStack.push(res1);
        resultStack.push(res2);
      }
      goto afterLoop;
    } else {
      continue;
    }

    AH::getHeadAndArgs(term, head, args);
    Signature::Proxy prox = AH::getProxy(head);
    if(prox == Signature::NOT_PROXY || prox == Signature::IFF ||
       prox == Signature::XOR){
      continue;
    }

    if(generating && !gen && prox != Signature::NOT){
      continue;
    }

    bool positive = AH::isTrue(boolVal) == lit->polarity();

    if((prox == Signature::OR) && (args.size() == 2)){
      if(positive){
        Literal* l1 = Literal::createEquality(true, args[0], troo, boolSort);
        Literal* l2 = Literal::createEquality(true, args[1], troo, boolSort);
        Inference *inf = new Inference1(convert(prox), c);   
        Clause* res = replaceLits(c, lit, l1, inf, l2);
        res->setAge(c->age());
        resultStack.push(res);
        goto afterLoop;
      } else {
        Literal* l1 = Literal::createEquality(true, args[0], fols, boolSort);
        Literal* l2 = Literal::createEquality(true, args[1], fols, boolSort);
        Inference* inf1 = new Inference1(convert(prox), c);
        Inference* inf2 = new Inference1(convert(prox), c);
        Clause* res1 = replaceLits(c, lit, l1, inf1);
        Clause* res2 = replaceLits(c, lit, l2, inf2);
        res1->setAge(c->age()+1);
        res2->setAge(c->age()+1);
        resultStack.push(res1);
        resultStack.push(res2);
        goto afterLoop;
      }
    }
  
    if((prox == Signature::AND) && (args.size() == 2)){
      if(positive){
        Literal* l1 = Literal::createEquality(true, args[0], troo, boolSort);
        Literal* l2 = Literal::createEquality(true, args[1], troo, boolSort);
        Inference* inf1 = new Inference1(convert(prox), c); 
        Inference* inf2 = new Inference1(convert(prox), c);     
        Clause* res1 = replaceLits(c, lit, l1, inf1);
        Clause* res2 = replaceLits(c, lit, l2, inf2);        
        res1->setAge(c->age()+1);
        res2->setAge(c->age()+1);
        resultStack.push(res1);
        resultStack.push(res2);
        goto afterLoop;
      } else {
        Literal* l1 = Literal::createEquality(true, args[0], fols, boolSort);
        Literal* l2 = Literal::createEquality(true, args[1], fols, boolSort);
        Inference *inf = new Inference1(convert(prox), c);
        Clause* res = replaceLits(c, lit, l1, inf, l2);
        res->setAge(c->age());
        resultStack.push(res);
        goto afterLoop;
      }
    }

    if((prox == Signature::IMP) && (args.size() == 2)){
      if(positive){
        Literal* l1 = Literal::createEquality(true, args[1], fols, boolSort);
        Literal* l2 = Literal::createEquality(true, args[0], troo, boolSort);
        Inference *inf = new Inference1(convert(prox), c);   
        Clause* res = replaceLits(c, lit, l1, inf, l2);
        res->setAge(c->age());
        resultStack.push(res);
        goto afterLoop;
      } else {
        Literal* l2 = Literal::createEquality(true, args[1], troo, boolSort);
        Literal* l1 = Literal::createEquality(true, args[0], fols, boolSort);
        Inference* inf1 = new Inference1(convert(prox), c);
        Inference* inf2 = new Inference1(convert(prox), c);
        Clause* res1 = replaceLits(c, lit, l1, inf1);
        Clause* res2 = replaceLits(c, lit, l2, inf2);        
        res1->setAge(c->age()+1);
        res2->setAge(c->age()+1);
        resultStack.push(res1);
        resultStack.push(res2);
        goto afterLoop;
      }
    }

    if((prox == Signature::EQUALS) && (args.size() == 2)){
      TermList srt = *SortHelper::getResultSort(head.term()).term()->nthArgument(0);
      Literal* l1 = Literal::createEquality(positive, args[0], args[1], srt);
      Inference *inf = new Inference1(convert(prox), c);
      Clause* res = replaceLits(c, lit, l1, inf);
      res->setAge(c->age());
      resultStack.push(res);
      goto afterLoop;
    }

    if((prox == Signature::NOT) && (args.size())){
      TermList rhs = positive ? fols : troo;
      Literal* l1 = Literal::createEquality(true, args[0], rhs, boolSort);
      Inference *inf = new Inference1(convert(prox), c);      
      Clause* res = replaceLits(c, lit, l1, inf);
      res->setAge(c->age());
      resultStack.push(res);
      goto afterLoop;
    }

    if((prox == Signature::PI || prox == Signature::SIGMA ) && (args.size())){
      TermList rhs = positive ? troo : fols; 
      TermList srt = *SortHelper::getResultSort(head.term()).term()->nthArgument(0);
      TermList newTerm;
      Inference *inf;
      if((prox == Signature::PI && positive) || 
         (prox == Signature::SIGMA && !positive)){
        inf = new Inference1(convert(Signature::PI), c);
        newTerm = piRemoval(args[0], c, srt);
      } else {
        bool newTermCreated = false;
        if(index){
          auto results = index->getGeneralizations(term, true);
          if(results.hasNext()){
            TermQueryResult tqr = results.next();
            TermList skolemTerm = tqr.term;
            skolemTerm=tqr.substitution->applyToBoundResult(skolemTerm);
            newTerm = AH::createAppTerm(srt, args[0], skolemTerm);
            newTermCreated = true;
          }
        }
        if(!newTermCreated){
          TermList skolemTerm = sigmaRemoval(args[0], srt);
          if(index){
            index->insertFormula(term, skolemTerm);
          }
          newTerm = AH::createAppTerm(srt, args[0], skolemTerm);
        }
        inf = new Inference1(convert(Signature::SIGMA), c);
      }
      Literal* l1 = Literal::createEquality(true, newTerm, rhs, boolSort);
      Clause* res = replaceLits(c, lit, l1, inf);
      res->setAge(c->age());
      resultStack.push(res);
      goto afterLoop;
    }

  }
  
  return ClauseIterator::getEmpty(); 

afterLoop:  

  return pvi(getUniquePersistentIterator(ClauseStack::Iterator(resultStack)));

}


Clause* replaceLits(Clause *c, Literal *a, Literal *b, Inference *inf, Literal *d, Literal* e)
{
  CALL("CNFOnTheFly::replaceLits");

  int length = c->length();
  if(d){ length++;}
  if(e){ length++;}
  
  Clause* res = new(length) Clause(length, c->inputType(), inf);

  unsigned i = 0;
  while ((*c)[i] != a) { i++; }
  std::memcpy(res->literals(), c->literals(), length * sizeof(Literal*));
  (*res)[i] = b;
  if(d){(*res)[length - 1] = d;} 
  if(e){(*res)[length - 2] = e;}//adding new literals at differrent places...
  
  return res;
}

Inference::Rule convert(Signature::Proxy cnst){
  CALL("CNFOnTheFly::convert");

  switch(cnst){
    case Signature::PI:
      return Inference::VPI_ELIMINATION;
    case Signature::SIGMA:
      return Inference::VSIGMA_ELIMINATION;
    case Signature::EQUALS:
      return Inference::HOL_EQUALITY_ELIMINATION;
    case Signature::NOT:
      return Inference::HOL_NOT_ELIMINATION;
    default:
      return Inference::BINARY_CONN_ELIMINATION;   
  }
}

TermList sigmaRemoval(TermList sigmaTerm, TermList expsrt){
  CALL("CNFOnTheFly::sigmaRemoval");

  static DHMap<unsigned,TermList> varSorts;
  varSorts.reset();

  if(sigmaTerm.isTerm()){
    VariableIterator2 vit(sigmaTerm.term());
    while(vit.hasNext()){
      pair<TermList, TermList> varTypePair = vit.next();
      if(!varSorts.find(varTypePair.first.var())){
        varSorts.insert(varTypePair.first.var(), varTypePair.second);
      }
    }
  } else {
    varSorts.insert(sigmaTerm.var(), expsrt);
    if(expsrt.isTerm()){
      VariableIterator2 vit(expsrt.term());
      while(vit.hasNext()){
        pair<TermList, TermList> varTypePair = vit.next();
        if(!varSorts.find(varTypePair.first.var())){
          varSorts.insert(varTypePair.first.var(), varTypePair.second);
        }
      }
    } else {
      varSorts.insert(expsrt.var(), Term::superSort());
    }
  }

  static Stack<TermList> argSorts;
  static Stack<TermList> termArgs;
  static Stack<TermList> args;
  argSorts.reset();
  termArgs.reset();
  args.reset();
 
  unsigned var;
  TermList varSort; 
  DHMap<unsigned, TermList>::Iterator mapIt(varSorts);
  while(mapIt.hasNext()) {
    mapIt.next(var, varSort);
    if(varSort == Term::superSort()){
      args.push(TermList(var, false));
    } else {
      argSorts.push(varSort);
      termArgs.push(TermList(var, false));
    }
  }
  ASS(termArgs.size() == argSorts.size());

  VList* vl = VList::empty();
  for(int i = args.size() -1; i >= 0 ; i--){
    VList::push(args[i].var(), vl);
  }

  //do{ 
    TermList resultSort = *expsrt.term()->nthArgument(0);
    TermList skSymSort = Term::arrowSort(argSorts, resultSort);
    unsigned fun = Skolem::addSkolemFunction(VList::length(vl), 0, skSymSort, vl);
    TermList head = TermList(Term::create(fun, args.size(), args.begin()));
    TermList skolemTerm = ApplicativeHelper::createAppTerm(skSymSort, head, termArgs);
    //sigmaTerm = ApplicativeHelper::createAppTerm(expsrt, sigmaTerm, skolemTerm);
    //expsrt = *expsrt.term()->nthArgument(1);
    ASS(*expsrt.term()->nthArgument(1) == Term::boolSort())
  //}while(expsrt != Term::boolSort());   

  //cout << "OUT OF sigmaRemoval " + sigmaTerm.toString() << endl;

  return skolemTerm;
}

TermList piRemoval(TermList piTerm, Clause* clause, TermList expsrt){
  
  CALL("CNFOnTheFly::piRemoval");

  unsigned maxVar = clause->maxVar();
  do{ 
    maxVar++;
    TermList newVar = TermList(maxVar, false);
    piTerm = ApplicativeHelper::createAppTerm(expsrt, piTerm, newVar);
    expsrt = *expsrt.term()->nthArgument(1);
  }while(expsrt != Term::boolSort()); 
  
  return piTerm;
}


Clause* IFFXORRewriterISE::simplify(Clause* c){
  CALL("IFFXORRewriterISE::simplify");

  TermList boolSort = Term::boolSort();

  static TermStack args;
  TermList head;
 
  for(unsigned i = 0; i < c->length(); i++){
    Literal* lit = (*c)[i];
    TermList lhs = *lit->nthArgument(0);
    TermList rhs = *lit->nthArgument(1);
    TermList term;
    TermList boolVal;
    if(AH::isBool(lhs)){
      boolVal = lhs;
      term = rhs;
    } else if(AH::isBool(rhs)){
      boolVal = rhs;
      term = lhs;
    } else {
      continue;
    }

    bool positive = AH::isTrue(boolVal) == lit->polarity();

    AH::getHeadAndArgs(term, head, args);
    Signature::Proxy prox = AH::getProxy(head);

    if((prox == Signature::IFF || prox == Signature::XOR) && (args.size() == 2)){
      bool polarity = (prox == Signature::IFF) == positive;
      Literal* l1 = Literal::createEquality(polarity, args[0], args[1], boolSort);
      Inference *inf = new Inference1(convert(prox), c);
      Clause* res = replaceLits(c, lit, l1, inf);
      res->setAge(c->age());
      return res;
    }
  }

  return c;
}

void LazyClausificationGIE::attach(SaturationAlgorithm* salg)
{
  CALL("LazyClausificationGIE::attach");

  GeneratingInferenceEngine::attach(salg);
  _formulaIndex=static_cast<SkolemisingFormulaIndex*> (
    _salg->getIndexManager()->request(SKOLEMISING_FORMULA_INDEX) );
}

void LazyClausificationGIE::detach()
{
  CALL("LazyClausificationGIE::detach");

  _formulaIndex=0;
  _salg->getIndexManager()->release(SKOLEMISING_FORMULA_INDEX);
  GeneratingInferenceEngine::detach();
}

void LazyClausification::attach(SaturationAlgorithm* salg)
{
  CALL("LazyClausification::attach");

  SimplificationEngine::attach(salg);
  _formulaIndex=static_cast<SkolemisingFormulaIndex*> (
   _salg->getIndexManager()->request(SKOLEMISING_FORMULA_INDEX) );
}

void LazyClausification::detach()
{
  CALL("LazyClausification::detach");

  _formulaIndex=0;
  _salg->getIndexManager()->release(SKOLEMISING_FORMULA_INDEX);
  SimplificationEngine::detach();
}

ClauseIterator EagerClausificationISE::simplifyMany(Clause* c)
{
  CALL("EagerClausificationISE::simplifyMany");

  return produceClauses(c, false);
}

ClauseIterator LazyClausificationGIE::generateClauses(Clause* c)
{
  CALL("LazyClausificationGIE::simplifyMany");

  return produceClauses(c, true, _formulaIndex);
}

ClauseIterator LazyClausification::perform(Clause* c)
{
  CALL("LazyClausification::perform");

  return produceClauses(c, false, _formulaIndex);
}


}
