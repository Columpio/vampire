#include "InductionHelper.hpp"

#include "Kernel/Formula.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/Substitution.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/Unit.hpp"

using namespace Kernel;

namespace Shell {

TermList TermListReplacement::transformSubterm(TermList trm)
{
  CALL("TermListReplacement::transformSubterm");

  if(trm.isVar() && _o.isVar() && trm.var() == _o.var()) {
    return _r;
  }

  if(trm.isTerm() && _o.isTerm() && trm.term()==_o.term()){
    return _r;
  }
  return trm;
}

TermList TermOccurrenceReplacement::transformSubterm(Kernel::TermList trm)
{
  CALL("TermOccurrenceReplacement::transformSubterm");

  if (trm.isVar() || !_r.find(trm)) {
    return trm;
  }

  if (!_c.find(trm)) {
    _c.insert(trm, 0);
  } else {
    _c.get(trm)++;
  }

  const auto& r = _r.get(trm);
  const auto& o = _o->get(trm);
  if (o->size() == 1 || o->contains(_c.get(trm))) {
    return r;
  }
  return trm;
}

TermList VarShiftReplacement::transformSubterm(TermList trm)
{
  CALL("VarShiftReplacement::transformSubterm");

  if(trm.isVar()) {
    return TermList(trm.var()+_shift, trm.isSpecialVar());
  }
  return trm;
}

TermList VarReplacement::transformSubterm(TermList trm)
{
  CALL("VarReplacement::transformSubterm");

  if(trm.isVar()) {
    if (!_varMap.find(trm.var())) {
      _varMap.insert(trm.var(), _v++);
    }
    return TermList(_varMap.get(trm.var()), false);
  }
  return trm;
}

bool IteratorByInductiveVariables::hasNext()
{
  ASS(_it.hasNext() == _indVarIt.hasNext());

  while (_indVarIt.hasNext() && !_indVarIt.peekAtNext()) {
    _indVarIt.next();
    _it.next();
    _c++;
  }
  return _indVarIt.hasNext();
}

TermList IteratorByInductiveVariables::next()
{
  ASS(hasNext());
  _indVarIt.next();
  return _it.next();
}

unsigned IteratorByInductiveVariables::count()
{
  return _c;
}

RDescription::RDescription(List<TermList>* recursiveCalls, TermList step, Formula* cond)
  : _recursiveCalls(recursiveCalls),
    _step(step),
    _condition(cond)
{}

Lib::vstring RDescription::toString() const
{
  List<TermList>::Iterator it(_recursiveCalls);
  Lib::vstring str = "";
  bool empty = !it.hasNext();
  if (!empty) {
    str+="(";
  }
  while (it.hasNext()) {
    str+=it.next().toString();
    if (it.hasNext()) {
      str+=" & ";
    }
  }
  if (!empty) {
    str+=") => ";
  }
  str+=_step.toString();
  return str;
}

List<TermList>::Iterator RDescription::getRecursiveCalls() const
{
  return List<TermList>::Iterator(_recursiveCalls);
}

TermList RDescription::getStep() const
{
  return _step;
}


RDescriptionInst::RDescriptionInst(List<DHMap<TermList, TermList>>* recursiveCalls,
                                   DHMap<TermList, TermList> step, Formula* cond)
  : _recursiveCalls(recursiveCalls),
    _step(step),
    _condition(cond)
{}

List<DHMap<TermList, TermList>>*& RDescriptionInst::getRecursiveCalls()
{
  return _recursiveCalls;
}

DHMap<TermList, TermList>& RDescriptionInst::getStep()
{
  return _step;
}

vstring RDescriptionInst::toString() const
{
  vstring str = "recursive calls: ";
  List<DHMap<TermList, TermList>>::Iterator lIt(_recursiveCalls);
  while (lIt.hasNext()) {
    DHMap<TermList, TermList>::Iterator iIt(lIt.next());
    while (iIt.hasNext()) {
      TermList k, v;
      iIt.next(k, v);
      str+=k.toString()+" -> "+v.toString()+"; ";
    }
  }
  str+="step: ";
  DHMap<Kernel::TermList, Kernel::TermList>::Iterator stIt(_step);
  while (stIt.hasNext()) {
    TermList k, v;
    stIt.next(k, v);
    str+=k.toString()+" -> "+v.toString()+"; ";
  }
  return str;
}

InductionTemplate::InductionTemplate()
  : _rDescriptions(0),
    _inductionVariables()
{}

void InductionTemplate::addRDescription(RDescription desc)
{
  List<RDescription>::push(desc, _rDescriptions);
}

vstring InductionTemplate::toString() const
{
  vstring str;
  List<RDescription>::Iterator rIt(_rDescriptions);
  str+="RDescriptions:";
  while (rIt.hasNext()) {
    str+=rIt.next().toString();
    if (rIt.hasNext()) {
      str+="; ";
    }
  }
  DArray<bool>::Iterator posIt(_inductionVariables);
  str+=" with inductive positions: (";
  while (posIt.hasNext()) {
    str+=to_string(posIt.next()).c_str();
    if (posIt.hasNext()) {
      str+=",";
    }
  }
  str+=")";
  return str;
}

const DArray<bool>& InductionTemplate::getInductionVariables() const
{
  return _inductionVariables;
}

List<RDescription>::Iterator InductionTemplate::getRDescriptions() const
{
  return List<RDescription>::Iterator(_rDescriptions);
}

void InductionTemplate::postprocess()
{
  ASS(_rDescriptions != nullptr);

  _inductionVariables.init(_rDescriptions->head().getStep().term()->arity(), false);
  List<RDescription>::Iterator rIt(_rDescriptions);
  while (rIt.hasNext()) {
    auto r = rIt.next();
    auto cIt = r.getRecursiveCalls();
    auto step = r.getStep().term();
    while (cIt.hasNext()) {
      Term::Iterator argIt1(cIt.next().term());
      Term::Iterator argIt2(step);
      unsigned i = 0;
      while (argIt1.hasNext()) {
        ASS(argIt2.hasNext());
        auto t1 = argIt1.next();
        auto t2 = argIt2.next();
        if (t1 != t2 && t2.containsSubterm(t1)) {
          _inductionVariables[i] = true;
          // cout << t2.toString() << " properly contains " << t1.toString() << endl;
        } else {
          // cout << t2.toString() << " does not properly contain " << t1.toString() << endl;
        }
        i++;
      }
    }
  }
}

InductionScheme::InductionScheme()
  : _rDescriptionInstances(0),
    _activeOccurrences(0),
    _maxVar(0)
{
}

void InductionScheme::init(Term* t, List<RDescription>::Iterator rdescIt, const Lib::DArray<bool>& indVars)
{
  CALL("InductionScheme::init");

  unsigned var = 0;
  while (rdescIt.hasNext()) {
    DHMap<unsigned, unsigned> varMap;
    auto desc = rdescIt.next();
    DHMap<TermList,TermList> stepSubst;

    IteratorByInductiveVariables termIt(t, indVars);
    IteratorByInductiveVariables stepIt(desc.getStep().term(), indVars);

    bool mismatch = false;
    while (termIt.hasNext()) {
      auto argTerm = termIt.next();
      auto argStep = stepIt.next();
      auto its = InductionHelper::getInductionTerms(argTerm);
      for (auto& indTerm : its) {
        if (stepSubst.find(indTerm)) {
          if (stepSubst.get(indTerm).isTerm() && argStep.isTerm() &&
              stepSubst.get(indTerm).term()->functor() != argStep.term()->functor()) {
            mismatch = true;
            break;
          }
          continue;
        }
        // there may be induction variables which
        // don't change in some cases
        if (argStep.isVar()) {
          continue;
        }
        VarReplacement cr(varMap, var);
        auto res = cr.transform(argStep.term());
        stepSubst.insert(indTerm, TermList(res));
      }
    }
    if (mismatch) {
      // We cannot properly create this case because
      // there is a mismatch between the ctors for
      // a substituted term
      continue;
    }

    auto recCallSubstList = List<DHMap<TermList,TermList>>::empty();
    List<TermList>::Iterator recCallsIt(desc.getRecursiveCalls());
    while (recCallsIt.hasNext()) {
      auto recCall = recCallsIt.next();
      DHMap<TermList,TermList> recCallSubst;

      IteratorByInductiveVariables termIt(t, indVars);
      IteratorByInductiveVariables recCallIt(recCall.term(), indVars);

      while (termIt.hasNext()) {
        auto argTerm = termIt.next();
        auto argRecCall = recCallIt.next();
        auto its = InductionHelper::getInductionTerms(argTerm);
        for (auto& indTerm : its) {
          if (recCallSubst.find(indTerm)) {
            continue;
          }
          if (argRecCall.isVar()) {
            // first we check if this variable corresponds to at least one complex term 
            // in the step (it is an induction variable position but may not be
            // changed in this case)
            IteratorByInductiveVariables stepIt(desc.getStep().term(), indVars);
            bool found = false;
            while (stepIt.hasNext()) {
              auto argStep = stepIt.next();
              if (argStep != argRecCall && argStep.containsSubterm(argRecCall)) {
                found = true;
                break;
              }
            }
            if (found) {
              recCallSubst.insert(indTerm, TermList(varMap.get(argRecCall.var()), false));
            }
          } else {
            VarReplacement cr(varMap, var);
            auto res = cr.transform(argRecCall.term());
            recCallSubst.insert(indTerm, TermList(res));
          }
        }
      }
      List<DHMap<TermList,TermList>>::push(recCallSubst, recCallSubstList);
    }
    addRDescriptionInstance(RDescriptionInst(recCallSubstList, stepSubst, nullptr));
  }
  _maxVar = var;
}

void InductionScheme::addRDescriptionInstance(RDescriptionInst inst)
{
  List<RDescriptionInst>::push(inst, _rDescriptionInstances);
}

void InductionScheme::addActiveOccurrences(DHMap<TermList, DHSet<unsigned>*>* m)
{
  _activeOccurrences = m;
}

void InductionScheme::setMaxVar(unsigned maxVar)
{
  _maxVar = maxVar;
}

List<RDescriptionInst>::RefIterator InductionScheme::getRDescriptionInstances() const
{
  return List<RDescriptionInst>::RefIterator(_rDescriptionInstances);
}

DHMap<TermList, DHSet<unsigned>*>* InductionScheme::getActiveOccurrences() const
{
  return _activeOccurrences;
}

unsigned InductionScheme::getMaxVar() const
{
  return _maxVar;
}

vstring InductionScheme::toString() const
{
  vstring str;
  str+="RDescription instances: ";
  List<RDescriptionInst>::Iterator lIt(_rDescriptionInstances);
  while (lIt.hasNext()) {
    str+=lIt.next().toString()+" ;-- ";
  }
  str+="Active occurrences: ";
  if (_activeOccurrences != nullptr) {
    DHMap<TermList, DHSet<unsigned>*>::Iterator aIt(*_activeOccurrences);
    while (aIt.hasNext()) {
      TermList k;
      DHSet<unsigned>* v;
      aIt.next(k, v);
      if (v->isEmpty()) {
        continue;
      }
      str+="term: "+k.toString()+" positions: ";
      DHSet<unsigned>::Iterator pIt(*v);
      while (pIt.hasNext()) {
        str+=Int::toString(pIt.next())+" ";
      }
    }
  }
  return str;
}

void InductionHelper::preprocess(Problem& prb)
{
  preprocess(prb.units());
}

void InductionHelper::preprocess(UnitList*& units)
{
  UnitList::Iterator it(units);
  while (it.hasNext()) {
    auto unit = it.next();
    if (unit->isClause()){
      continue;
    }

    auto formula = unit->getFormula();
    while (formula->connective() == Connective::FORALL) {
      formula = formula->qarg();
    }

    if (formula->connective() != Connective::LITERAL) {
      continue;
    }

    auto lit = formula->literal();

    if (!lit->isRecFuncDef()) {
      continue;
    }
    auto lhs = lit->nthArgument(0);
    auto rhs = lit->nthArgument(1);
    auto lhterm = lhs->term();
    bool isPred = lhterm->isFormula();
    if (isPred) {
      lhterm = lhterm->getSpecialData()->getFormula()->literal();
    }

    InductionTemplate* templ = new InductionTemplate();
    TermList term(lhterm);
    processBody(*rhs, term, templ);
    templ->postprocess();

    if(env.options->showInduction()){
      env.beginOutput();
      env.out() << "[Induction] recursive function: " << lit->toString() << ", with induction template: " << templ->toString() << endl;
      env.endOutput();
    }
    env.signature->addInductionTemplate(lhterm->functor(), isPred, templ);
  }
}

void InductionHelper::filterFlawedSchemes(List<InductionScheme*>*& schemes,
  DHMap<TermList, DHSet<unsigned>*>* activeOccurrenceMap,
  const DHMap<TermList, unsigned>& occurrenceMap)
{
  CALL("InductionHelper::filterFlawedSchemes");
  Set<InductionScheme*> unflawed;
  List<InductionScheme*>::Iterator schIt(schemes);
  while (schIt.hasNext()) {
    auto scheme = schIt.next();
    auto rdescIt = scheme->getRDescriptionInstances();
    bool flawed = false;
    while (rdescIt.hasNext()) {
      auto rdesc = rdescIt.next();
      DHMap<TermList,TermList>::Iterator stIt(rdesc.getStep());
      while (stIt.hasNext()) {
        auto k = stIt.nextKey();
        if (activeOccurrenceMap->get(k)->size() != occurrenceMap.get(k)) {
          flawed = true;
          break;
        }
      }
    }
    if (!flawed) {
      unflawed.insert(scheme);
    }
  }
  if(env.options->showInduction()){
    env.beginOutput();
    env.out() << "[Induction] " << unflawed.size() << " out of " << List<InductionScheme*>::length(schemes)
              << " induction schemes are unflawed" << endl;
    env.endOutput();
  }
  if (unflawed.size() > 0 && unflawed.size() != List<InductionScheme*>::length(schemes)) {
    if(env.options->showInduction()){
      env.beginOutput();
      env.out() << "[Induction] filtering out flawed schemes" << endl;
      env.endOutput();
    }
    List<InductionScheme*>::Iterator schIt(schemes);
    while (schIt.hasNext()) {
      auto scheme = schIt.next();
      if (!unflawed.contains(scheme)) {
        if(env.options->showInduction()){
          env.beginOutput();
          env.out() << "[Induction] Scheme is flawed and is removed: " << scheme->toString() << endl;
          env.endOutput();
        }
        schemes = List<InductionScheme*>::remove(scheme, schemes);
        // delete scheme;
      }
    }
  }
}

void mergeLitClausePairsInto(DHMap<Literal*, Clause*>* from, DHMap<Literal*, Clause*>* to)
{
  DHMap<Literal*, Clause*>::Iterator it(*from);
  while (it.hasNext()) {
    Literal* lit;
    Clause* cl;
    it.next(lit, cl);
    ASS(!to->find(lit) || to->get(lit) == cl); // if this happens, a more complicated structure is needed
    to->insert(lit, cl);
  }
}

void InductionHelper::filterSchemes(DHMap<InductionScheme*, DHMap<Literal*, Clause*>*>* primarySchemes,
  DHMap<InductionScheme*, DHMap<Literal*, Clause*>*>* secondarySchemes)
{
  filterSchemes(primarySchemes);
  filterSchemes(secondarySchemes);

  // merge secondary schemes into primary ones if possible, remove the rest
  vvector<InductionScheme*> secondaryKeysToRemove;
  DHMap<InductionScheme*, DHMap<Literal*, Clause*>*>::Iterator secIt(*secondarySchemes);
  while (secIt.hasNext()) {
    auto secondary = secIt.nextKey();
    DHMap<InductionScheme*, DHMap<Literal*, Clause*>*>::Iterator prIt(*primarySchemes);
    while (prIt.hasNext()) {
      auto primary = prIt.nextKey();
      if (checkSubsumption(secondary, primary)) {
        if(env.options->showInduction()){
          env.beginOutput();
          env.out() << "[Induction] secondary induction scheme " << secondary->toString() << " is subsumed by primary " << primary->toString() << endl;
          env.endOutput();
        }
        mergeLitClausePairsInto(secondarySchemes->get(secondary), primarySchemes->get(primary));
        break;
      } else if (checkSubsumption(primary, secondary)) {
        if(env.options->showInduction()){
          env.beginOutput();
          env.out() << "[Induction] primary induction scheme " << primary->toString() << " is subsumed by secondary " << secondary->toString() << endl;
          env.endOutput();
        }
        auto val = primarySchemes->get(primary);
        primarySchemes->remove(primary);
        mergeLitClausePairsInto(secondarySchemes->get(secondary), val);
        secondaryKeysToRemove.push_back(secondary);
        primarySchemes->insert(secondary, val);
        break;
      }
    }
  }
  for (const auto& k : secondaryKeysToRemove) {
    delete secondarySchemes->get(k);
    secondarySchemes->remove(k);
  }
}

void removeSubsumedScheme(DHMap<InductionScheme*, DHMap<Literal*, Clause*>*>* schemes, InductionScheme* subsumed, InductionScheme* subsumer) {
  if(env.options->showInduction()){
    env.beginOutput();
    env.out() << "[Induction] induction scheme " << subsumed->toString() << " is subsumed by " << subsumer->toString() << endl;
    env.endOutput();
  }
  mergeLitClausePairsInto(schemes->get(subsumed), schemes->get(subsumer));
  schemes->remove(subsumed);
  delete subsumed;
}

void InductionHelper::filterSchemes(DHMap<InductionScheme*, DHMap<Literal*, Clause*>*>* schemes)
{
  CALL("InductionHelper::filterSchemes");

  // filterFlawedSchemes(schemes, activeOccurrenceMap, occurrenceMap);

  bool changed = false;
  do {
    changed = false;
    DHMap<InductionScheme*, DHMap<Literal*, Clause*>*>::Iterator schIt(*schemes);
    while (schIt.hasNext()) {
      auto scheme = schIt.nextKey();
      auto schIt2 = schIt;

      while (schIt2.hasNext()) {
        auto other = schIt2.nextKey();
        if (checkSubsumption(scheme, other)) {
          removeSubsumedScheme(schemes, scheme, other);
          changed = true;
          break;
        } else if (checkSubsumption(other, scheme)) {
          removeSubsumedScheme(schemes, other, scheme);
          changed = true;
          break;
        } else if (checkSubsumption(scheme, other, true)) {
          if(env.options->showInduction()){
            env.beginOutput();
            env.out() << "[Induction] induction scheme " << scheme->toString() << " can be merged into " << other->toString() << endl;
            env.endOutput();
          }
          // mergeSchemes(scheme, other);
          // schemes = List<InductionScheme*>::remove(scheme, schemes);
          // delete scheme;
          // break;
        } else if (checkSubsumption(other, scheme, true)) {
          if(env.options->showInduction()){
            env.beginOutput();
            env.out() << "[Induction] induction scheme " << other->toString() << " can be merged into " << scheme->toString() << endl;
            env.endOutput();
          }
          // if (schIt.peekAtNext() == other) {
          //   schIt.next();
          // }
          // mergeSchemes(other, scheme);
          // schemes = List<InductionScheme*>::remove(other, schemes);
          // delete other;
        }
      }
      if (changed) {
        break;
      }
    }
  } while (changed); 
}

bool InductionHelper::canInductOn(TermList t)
{
  if (t.isVar()) {
    return false;
  }
  auto fn = t.term()->functor();
  auto symb = t.term()->isLiteral() ? env.signature->getPredicate(fn) : env.signature->getFunction(fn);
  return symb->skolem();
}

bool InductionHelper::isTermAlgebraCons(TermList t) {
  if (t.isVar()) { return false; }
  auto func = t.term()->functor();
  auto symb = t.term()->isLiteral() ? env.signature->getPredicate(func) : env.signature->getFunction(func);
  return symb->termAlgebraCons();
}

OperatorType* getType(TermList t) {
  auto fn = t.term()->functor();
  auto symb = t.term()->isLiteral() ? env.signature->getPredicate(fn) : env.signature->getFunction(fn);
  return t.term()->isLiteral() ? symb->predType() : symb->fnType();
}

vvector<TermList> InductionHelper::getInductionTerms(TermList t)
{
  vvector<TermList> v;
  if (t.isVar()) {
    return v;
  }
  if (canInductOn(t)) {
    v.push_back(t);
    return v;
  }
  if (!isTermAlgebraCons(t)) {
    return v;
  }
  auto type = getType(t);
  //TODO(mhajdu): eventually check whether we really recurse on a specific
  // subterm of the constructor terms
  Stack<pair<TermList, bool>> actStack;
  actStack.push(make_pair(t, true));
  while (actStack.isNonEmpty()) {
    auto kv = actStack.pop();
    auto st = kv.first;
    auto active = kv.second;
    if (st.isVar()) {
      continue;
    }
    if (active && canInductOn(st) && getType(st)->result() == type->result()) {
      v.push_back(st);
    }
    if (active && isTermAlgebraCons(st)) {
      for (unsigned i = 0; i < st.term()->arity(); i++) {
        actStack.push(make_pair(*st.term()->nthArgument(i),true));
      }
    }
  }
  return v;
}

DHSet<TermList> InductionHelper::getInductionTerms(DHMap<InductionScheme*, DHMap<Literal*, Clause*>*>* schemes)
{
  DHSet<TermList> v;
  DHMap<InductionScheme*, DHMap<Literal*, Clause*>*>::Iterator it(*schemes);
  while (it.hasNext()) {
    auto scheme = it.nextKey();
    auto it2 = scheme->getRDescriptionInstances();
    while (it2.hasNext()) {
      auto desc = it2.next();
      auto step = desc.getStep();
      DHMap<TermList,TermList>::Iterator mIt(step);
      while (mIt.hasNext()) {
        auto k = mIt.nextKey();
        v.insert(k);
      }
    }
  }
  return v;
}

void InductionHelper::processBody(TermList& body, TermList& header, InductionTemplate*& templ)
{
  if (body.isVar()) {
    RDescription desc(nullptr, header, nullptr);
    templ->addRDescription(desc);
    return;
  }
  auto term = body.term();
  if (!term->isSpecial() || term->isFormula()) {
    List<TermList>* recursiveCalls(0);
    processCase(header.term()->functor(), body, recursiveCalls);
    RDescription desc(recursiveCalls, header, nullptr);
    templ->addRDescription(desc);
  }
  else if (term->isMatch())
  {
    auto matchedVar = term->nthArgument(0)->var();
    unsigned index = findMatchedArgument(matchedVar, header);
    ASS(index < header.term()->arity());

    for (unsigned i = 1; i < term->arity(); i+=2) {
      auto pattern = term->nthArgument(i);
      auto matchBody = term->nthArgument(i+1);
      TermListReplacement tr(TermList(matchedVar,false), *pattern);
      TermList t(tr.transform(header.term()));
      processBody(*matchBody, t, templ);
    }
  }
}

void InductionHelper::processCase(const unsigned recFun, TermList& body, List<TermList>*& recursiveCalls)
{
  if (!body.isTerm()) {
    return;
  }

  auto term = body.term();
  if (term->functor() == recFun) {
    List<TermList>::push(body, recursiveCalls);
  }

  if (term->isFormula()) {
    auto formula = term->getSpecialData()->getFormula();
    switch (formula->connective()) {
      case LITERAL: {
        TermList lit(formula->literal());
        processCase(recFun, lit, recursiveCalls);
        break;
      }
      case AND:
      case OR: {
        FormulaList::Iterator it(formula->args());
        while (it.hasNext()) {
          // TODO(mhajdu): maybe don't create a new Term here
          TermList ft(Term::createFormula(it.next()));
          processCase(recFun, ft, recursiveCalls);
        }
        break;
      }
      case TRUE:
      case FALSE: {
        break;
      }
#if VDEBUG
      default:
        ASSERTION_VIOLATION;
#endif
    }
  } else {
    Term::Iterator it(term);
    while (it.hasNext()) {
      auto n = it.next();
      processCase(recFun, n, recursiveCalls);
    }
  }
}

unsigned InductionHelper::findMatchedArgument(unsigned matched, TermList& header)
{
  unsigned i = 0;
  Term::Iterator argIt(header.term());
  while (argIt.hasNext()) {
    IntList::Iterator varIt(argIt.next().freeVariables());
    bool found = false;
    while (varIt.hasNext()) {
      auto var = varIt.next();
      if (var == matched) {
        found = true;
        break;
      }
    }
    if (found) {
      break;
    }
    i++;
  }
  return i;
}

vstring substTermsToString(List<Term*>* l) {
  vstring str;
  List<Term*>::Iterator it(l);
  while (it.hasNext()) {
    str+=it.next()->toString()+"; ";
  }
  return str;
}

bool equalsUpToVariableRenaming(TermList t1, TermList t2) {
  if (t1.isVar() && t2.isVar()) {
    return true;
  }
  if (t1.isVar()) {
    return false;
  }
  if (t2.isVar()) {
    return false;
  }

  auto tt1 = t1.term();
  auto tt2 = t2.term();
  if (tt1->functor() != tt2->functor() || tt1->arity() != tt2->arity())
  {
    return false;
  }

  Term::Iterator it1(tt1);
  Term::Iterator it2(tt2);
  while (it1.hasNext()) {
    if (!equalsUpToVariableRenaming(it1.next(), it2.next())) {
      return false;
    }
  }
  return true;
}

bool containsUpToVariableRenaming(TermList container, TermList contained) {
  if (contained.isVar()) {
    return true;
  }
  if (container.isVar()) {
    return false;
  }

  auto t1 = container.term();
  auto t2 = contained.term();
  if (t1->functor() == t2->functor() && t1->arity() == t2->arity())
  {
    bool equal = true;
    Term::Iterator it1(t1);
    Term::Iterator it2(t2);
    while (it1.hasNext()) {
      auto arg1 = it1.next();
      auto arg2 = it2.next();
      if (!equalsUpToVariableRenaming(arg1, arg2)) {
        equal = false;
        break;
      }
    }
    if (equal) {
      return true;
    }
  }

  Term::Iterator it1(container.term());
  while (it1.hasNext()) {
    auto arg1 = it1.next();
    if (containsUpToVariableRenaming(arg1, contained)) {
      return true;
    }
  }
  return false;
}

bool InductionHelper::checkSubsumption(InductionScheme* sch1, InductionScheme* sch2, bool onlyCheckIntersection)
{
  auto rdescIt1 = sch1->getRDescriptionInstances();
  while (rdescIt1.hasNext()) {
    auto rdesc1 = rdescIt1.next();
    auto contained = false;
    auto rdescIt2 = sch2->getRDescriptionInstances();
    while (rdescIt2.hasNext()) {
      auto rdesc2 = rdescIt2.next();
      if ((rdesc2.getRecursiveCalls() == nullptr) != (rdesc1.getRecursiveCalls() == nullptr)) {
        continue;
      }
      auto m2 = rdesc2.getStep();
      bool contained1 = true;
      DHMap<TermList, TermList>::Iterator sIt(rdesc1.getStep());
      while (sIt.hasNext()) {
        TermList k, v;
        sIt.next(k, v);
        if (!m2.find(k)) {
          if (!onlyCheckIntersection) {
            contained1 = false;
          }
          break;
        }
        auto s2 = m2.get(k);
        if (!containsUpToVariableRenaming(s2, v)) {
          contained1 = false;
          break;
        }
      }
      if (contained1) {
        contained = true;
        break;
      }
    }
    if (!contained) {
      return false;
    }
  }
  return true;
}

TermList shiftVarsUp(TermList t, unsigned shift) {
  if (t.isVar()) {
    return TermList(t.var()+shift, t.isSpecialVar());
  }
  VarShiftReplacement vr(shift);
  return TermList(vr.transform(t.term()));
}

void InductionHelper::mergeSchemes(InductionScheme* sch1, InductionScheme*& sch2) {
  auto res = new InductionScheme();
  auto rdescIt1 = sch1->getRDescriptionInstances();
  auto maxVar = sch2->getMaxVar();
  unsigned var = 0;
  while (rdescIt1.hasNext()) {
    auto rdesc1 = rdescIt1.next();
    auto rdescIt2 = sch2->getRDescriptionInstances();
    while (rdescIt2.hasNext()) {
      DHMap<unsigned, unsigned> varMap;
      auto& rdesc2 = rdescIt2.next();
      bool base1 = rdesc1.getRecursiveCalls() == nullptr;
      bool base2 = rdesc2.getRecursiveCalls() == nullptr;
      if (base1 || base2) {
        continue;
      }
      auto m2 = rdesc2.getStep();

      auto desc = rdesc2;
      DHMap<TermList, TermList>::Iterator stIt(rdesc1.getStep());
      while (stIt.hasNext()) {
        TermList k, v;
        stIt.next(k, v);
        if (m2.find(k)) {
          desc.getStep().insert(
            shiftVarsUp(k, maxVar), shiftVarsUp(v, maxVar));
        }
      }
      DHMap<TermList, TermList>::Iterator stIt2(desc.getStep());
      while (stIt2.hasNext()) {
        TermList k;
        auto& v = stIt2.nextRef(k);
        VarReplacement cr(varMap, var);
        v = TermList(cr.transform(v.term()));
      }
      auto mergedRecCalls = List<DHMap<TermList,TermList>>::empty();
      List<DHMap<TermList,TermList>>::Iterator it1(rdesc1.getRecursiveCalls());
      // if (!it1.hasNext()) {
      //   List<DHMap<TermList,TermList>>::Iterator it2(rdesc2.getRecursiveCalls());
      //   while (it2.hasNext()) {
      //     auto recCall2 = it2.next();
      //     DHMap<TermList, TermList>::Iterator recIt(recCall2);
      //     while (recIt.hasNext()) {
      //       TermList k;
      //       auto& v = recIt.nextRef(k);
      //       if (v.isVar()) {
      //         v = TermList(varMap.get(v.var()), false);
      //       } else {
      //         VarReplacement cr(varMap, var);
      //         v = TermList(cr.transform(v.term()));
      //       }
      //     }
      //     List<DHMap<TermList,TermList>>::push(recCall2, mergedRecCalls);
      //   }
      // } else {
        while (it1.hasNext()) {
          auto recCall1 = it1.next();
          List<DHMap<TermList,TermList>>::Iterator it2(rdesc2.getRecursiveCalls());
          // if (!it2.hasNext()) {
          //   DHMap<TermList,TermList> mergedRecCall;
          //   DHMap<TermList,TermList>::Iterator recIt(recCall1);
          //   while (recIt.hasNext()) {
          //     TermList k, v;
          //     recIt.next(k, v);
          //     if (v.isVar()) {
          //       mergedRecCall.insert(
          //         k, TermList(varMap.get(v.var()+maxVar), false));
          //     } else {
          //       VarReplacement cr(varMap, var);
          //       auto t = shiftVarsUp(v, maxVar);
          //       mergedRecCall.insert(
          //         k, TermList(cr.transform(t.term())));
          //     }
          //   }
          //   List<DHMap<TermList,TermList>>::push(mergedRecCall, mergedRecCalls);
          // } else {
            while (it2.hasNext()) {
              auto mergedRecCall = it2.next();
              DHMap<TermList,TermList>::Iterator recIt(mergedRecCall);
              while (recIt.hasNext()) {
                TermList k;
                auto& v = recIt.nextRef(k);
                if (v.isVar()) {
                  v = TermList(varMap.get(v.var()), false);
                } else {
                  VarReplacement cr(varMap, var);
                  v = TermList(cr.transform(v.term()));
                }
              }
              DHMap<TermList,TermList>::Iterator recIt2(mergedRecCall);
              while (recIt2.hasNext()) {
                TermList k, v;
                recIt2.next(k, v);
                if (v.isVar()) {
                  mergedRecCall.insert(
                    k, TermList(varMap.get(v.var()+maxVar), false));
                } else {
                  VarReplacement cr(varMap, var);
                  auto t = shiftVarsUp(v, maxVar);
                  mergedRecCall.insert(
                    k, TermList(cr.transform(t.term())));
                }
              }
              List<DHMap<TermList,TermList>>::push(mergedRecCall, mergedRecCalls);
            }
          // }
        }
      // }
      desc.getRecursiveCalls() = mergedRecCalls;
      res->addRDescriptionInstance(desc);
    }
  }
  res->setMaxVar(var);
  cout << "Merged scheme: " << res->toString() << endl;
  delete sch2;
  sch2 = res;
}

} // Shell
