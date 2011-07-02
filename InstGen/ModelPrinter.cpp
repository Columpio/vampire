/**
 * @file ModelPrinter.cpp
 * Implements class ModelPrinter.
 */

#include <algorithm>

#include "ModelPrinter.hpp"

#include "Lib/Environment.hpp"
#include "Lib/IntUnionFind.hpp"

#include "Kernel/Signature.hpp"
#include "Kernel/SortHelper.hpp"

#include "Indexing/GroundingIndex.hpp"

#include "Shell/EqualityProxy.hpp"

#include "IGAlgorithm.hpp"


namespace InstGen
{

using namespace Shell;

ModelPrinter::ModelPrinter(IGAlgorithm& iga)
 : _iga(iga)
{
  CALL("ModelPrinter::ModelPrinter");
}

bool ModelPrinter::isEprProblem()
{
  CALL("ModelPrinter::isEprProblem");

  unsigned funCnt = env.signature->functions();
  for(unsigned i=0; i<funCnt; i++) {
    if(env.signature->functionArity(i)>0) {
      return false;
    }
  }
  return true;
}

bool ModelPrinter::tryOutput(ostream& stm)
{
  CALL("ModelPrinter::tryOutput");

  if(!isEprProblem()) {
    return false;
  }

  collectTrueLits();
  populateDomain();

  return false;
}

bool ModelPrinter::isEquality(Literal* lit)
{
  CALL("ModelPrinter::isEquality");

  return lit->isEquality() || lit->functor()==EqualityProxy::s_proxyPredicate;
}

void ModelPrinter::collectTrueLits()
{
  CALL("ModelPrinter::collectTrueLits");

  ClauseIterator ait = _iga.getActive();
  while(ait.hasNext()) {
    Clause* cl = ait.next();
    unsigned selCnt = cl->selected();
    ASS_G(selCnt, 0);
    for(unsigned i=0; i<selCnt; i++) {
      Literal* lit = (*cl)[i];
      if(isEquality(lit)) {
	_trueEqs.push(lit);
      }
      else {
	_trueLits.push(lit);
      }
    }
  }
}

/**
 * Comparator that ensures instances go before more general clauses in the ordering
 */
struct ModelPrinter::InstLitComparator
{
  bool operator()(Literal* l1, Literal* l2)
  {
    if(l1->weight()!=l2->weight()) {
      return l1->weight()>l2->weight();
    }
    return l1->vars()>l2->vars();
  }
};

void ModelPrinter::generateNewInstances(Literal* base, TermStack& domain, DHSet<Literal*>& instSet, LiteralStack& instAcc)
{
  CALL("ModelPrinter::generateNewInstances");

  unsigned arity = base->arity();
  unsigned domSz= domain.size();

  static DArray<TermList> args;
  static DArray<bool> variables;
  static DArray<unsigned> nextIndexes;
  PredicateType* predType = env.signature->getPredicate(base->functor())->predType();

  args.ensure(arity);
  variables.ensure(arity);
  nextIndexes.ensure(arity);

  for(unsigned i=0; i<arity; i++) {
    TermList baseArg = *base->nthArgument(i);
    bool isVar = baseArg.isVar();
    variables[i] = isVar;
    if(isVar) {
      args[i] = baseArg;
    }
    else {
      nextIndexes[i] = 0;
    }
  }

  unsigned depth = 0;
  for(;;) {
    while(!variables[depth] && depth<arity) {
      depth++;
    }
    bool goingDown;
    if(depth==arity) {
      //now we can generate a literal
      Literal* inst;
      if(base->isEquality()) {
	inst = Literal::createEquality(base->isPositive(), args[0], args[1]);
      }
      else {
	inst = Literal::create(base, args.array());
      }
      bool isNew = !instSet.contains(inst);
      if(isNew) {
	Literal* opInst = Literal::oppositeLiteral(inst);
	isNew = !instSet.contains(opInst);
      }
      if(isNew) {
	instSet.insert(inst);
	instAcc.push(inst);
      }

      goingDown = true;
    }
    else {
      TermList arg;
      do {
        if(nextIndexes[depth]==domSz) {
	  nextIndexes[depth] = 0;

	  goingDown = true;
	  goto done_with_level;
        }
        arg = domain[nextIndexes[depth]];
        nextIndexes[depth]++;
      } while(SortHelper::getResultSort(arg.term())!=predType->arg(depth));
      args[depth] = arg;
      goingDown = false;
    }

  done_with_level:
    if(goingDown) {
      do {
	if(depth==0) {
	  //we're done
	  return;
	}
	depth--;
      } while(!variables[depth]);
    }
    else {
      depth++;
    }
  }
}

void ModelPrinter::getInstances(LiteralStack& trueLits, TermStack& domain, LiteralStack& instanceAcc)
{
  CALL("ModelPrinter::getInstances");

  static DHSet<Literal*> instSet;
  instSet.reset();

  std::sort(trueLits.begin(), trueLits.end(), InstLitComparator());
  LiteralStack::BottomFirstIterator tlIt(trueLits);
  while(tlIt.hasNext()) {
    Literal* lit = tlIt.next();
    generateNewInstances(lit, domain, instSet, instanceAcc);
  }
}

void ModelPrinter::analyzeEquality()
{
  CALL("ModelPrinter::analyzeEquality");

  TermStack eqInstDomain;
  unsigned funCnt = env.signature->functions();
  for(unsigned i=0; i<funCnt; i++) {
    ASS_EQ(env.signature->functionArity(i), 0);
    TermList trm = TermList(Term::create(i, 0, 0));
    eqInstDomain.push(trm);
  }
  LiteralStack eqInsts;
  getInstances(_trueEqs, eqInstDomain, eqInsts);

  IntUnionFind uif(funCnt);

  LiteralStack::Iterator eqit(eqInsts);
  while(eqit.hasNext()) {
    Literal* lit = eqit.next();
    TermList arg1 = *lit->nthArgument(0);
    TermList arg2 = *lit->nthArgument(1);
    ASS(arg1.isTerm());
    ASS(arg2.isTerm());
    unsigned fun1 = arg1.term()->functor();
    unsigned fun2 = arg2.term()->functor();
    uif.doUnion(fun1, fun2);
  }

  uif.evalComponents();
  IntUnionFind::ComponentIterator eqClassIt(uif);
  while(eqClassIt.hasNext()) {
    IntUnionFind::ElementIterator ecElIt = eqClassIt.next();

    ALWAYS(ecElIt.hasNext());
    unsigned firstFunc = ecElIt.next();
    TermList firstTerm = TermList(Term::create(firstFunc, 0, 0));
    string firstTermStr = firstTerm.toString();
    unsigned reprFunc = env.signature->addStringConstant(firstTermStr);
    TermList reprTerm = TermList(Term::create(reprFunc, 0, 0));
    _rewrites.insert(firstTerm, reprTerm);

    while(ecElIt.hasNext()) {
      unsigned elFunc = ecElIt.next();
      TermList elTerm = TermList(Term::create(elFunc, 0, 0));
      _rewrites.insert(elTerm, reprTerm);
    }
  }
}

void ModelPrinter::populateDomain()
{
  CALL("ModelPrinter::populateDomain");
}

}
