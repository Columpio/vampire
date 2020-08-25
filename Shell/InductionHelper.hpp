#ifndef __InductionHelper__
#define __InductionHelper__

#include "Forwards.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermTransformer.hpp"
#include "Lib/Set.hpp"
#include "Lib/STL.hpp"

namespace Shell {

using namespace Kernel;

class TermListReplacement : public TermTransformer {
public:
  TermListReplacement(TermList o, TermList r) : _o(o), _r(r) {}
  TermList transformSubterm(TermList trm) override;
private:
  TermList _o;
  TermList _r;
};

class TermOccurrenceReplacement : public Kernel::TermTransformer {
public:
  TermOccurrenceReplacement(const Lib::DHMap<Kernel::TermList, Kernel::TermList>& r,
                            Lib::DHMap<Kernel::TermList, Lib::DHSet<unsigned>*>* o) : _r(r), _o(o), _c() {}
  Kernel::TermList transformSubterm(Kernel::TermList trm) override;

private:
  const Lib::DHMap<Kernel::TermList, Kernel::TermList>& _r;
  Lib::DHMap<Kernel::TermList, Lib::DHSet<unsigned>*>* _o;
  Lib::DHMap<Kernel::TermList, unsigned> _c;
};

class VarShiftReplacement : public Kernel::TermTransformer {
public:
  VarShiftReplacement(unsigned shift) : _shift(shift) {}
  Kernel::TermList transformSubterm(Kernel::TermList trm) override;

private:
  unsigned _shift;
};

class VarReplacement : public Kernel::TermTransformer {
public:
  VarReplacement(Kernel::DHMap<unsigned, unsigned>& varMap, unsigned& v) : _varMap(varMap), _v(v) {}
  Kernel::TermList transformSubterm(Kernel::TermList trm) override;

private:
  Kernel::DHMap<unsigned, unsigned>& _varMap;
  unsigned& _v;
};

class IteratorByInductiveVariables
{
public:
  IteratorByInductiveVariables(Kernel::Term* term,
                               const Lib::DArray<bool>& indVars)
    : _it(term), _indVarIt(indVars), _c(0)
  {}

  bool hasNext();
  Kernel::TermList next();
  unsigned count();

private:
  Kernel::Term::Iterator _it;
  Lib::DArray<bool>::Iterator _indVarIt;
  unsigned _c;
};

class RDescription {
public:
  CLASS_NAME(RDescription);
  USE_ALLOCATOR(RDescription);

  RDescription(Kernel::List<Kernel::TermList>* recursiveCalls,
               Kernel::TermList step,
               Kernel::Formula* cond);

  Lib::vstring toString() const;
  Kernel::List<Kernel::TermList>::Iterator getRecursiveCalls() const;
  Kernel::TermList getStep() const;

private:
  Kernel::List<Kernel::TermList>* _recursiveCalls;
  Kernel::TermList _step;
  Kernel::Formula* _condition;
};

class RDescriptionInst {
public:
  CLASS_NAME(RDescriptionInst);
  USE_ALLOCATOR(RDescriptionInst);

  RDescriptionInst(Kernel::List<Kernel::DHMap<Kernel::TermList, Kernel::TermList>>* recursiveCalls,
                   Kernel::DHMap<Kernel::TermList, Kernel::TermList> step,
                   Kernel::Formula* cond);

  Kernel::List<Kernel::DHMap<Kernel::TermList, Kernel::TermList>>*& getRecursiveCalls();
  Kernel::DHMap<Kernel::TermList, Kernel::TermList>& getStep();

  Lib::vstring toString() const;

private:
  Kernel::List<Kernel::DHMap<Kernel::TermList, Kernel::TermList>>* _recursiveCalls;
  Kernel::DHMap<Kernel::TermList, Kernel::TermList> _step;
  Kernel::Formula* _condition;
};

class InductionTemplate {
public:
  CLASS_NAME(InductionTemplate);
  USE_ALLOCATOR(InductionTemplate);

  InductionTemplate();

  void addRDescription(RDescription desc);
  void postprocess();

  const Lib::DArray<bool>& getInductionVariables() const;
  Kernel::List<RDescription>::Iterator getRDescriptions() const;

  Lib::vstring toString() const;

private:
  Kernel::List<RDescription>* _rDescriptions;
  Lib::DArray<bool> _inductionVariables;
};

class InductionScheme {
public:
  CLASS_NAME(InductionScheme);
  USE_ALLOCATOR(InductionScheme);

  InductionScheme();

  void init(Kernel::Term* term, Kernel::List<RDescription>::Iterator rdescIt, const Lib::DArray<bool>& indVars);
  void addRDescriptionInstance(RDescriptionInst inst);
  void addActiveOccurrences(Lib::DHMap<Kernel::TermList, Lib::DHSet<unsigned>*>* m);
  void setMaxVar(unsigned maxVar);

  Kernel::List<RDescriptionInst>::RefIterator getRDescriptionInstances() const;
  Lib::DHMap<Kernel::TermList, Lib::DHSet<unsigned>*>* getActiveOccurrences() const;
  unsigned getMaxVar() const;

  Lib::vstring toString() const;

private:
  void replaceFreeVars(Kernel::TermList t, unsigned& currVar, Lib::DHMap<unsigned, unsigned>& varMap);

  Kernel::List<RDescriptionInst>* _rDescriptionInstances;
  Lib::DHMap<Kernel::TermList, Lib::DHSet<unsigned>*>* _activeOccurrences;
  unsigned _maxVar;
};

class InductionHelper {
public:
  static void preprocess(Kernel::Problem& prb);
  static void filterSchemes(Lib::DHMap<InductionScheme*, Lib::DHMap<Literal*, Clause*>*>* primarySchemes,
    Lib::DHMap<InductionScheme*, Lib::DHMap<Literal*, Clause*>*>* secondarySchemes);
  static void filterSchemes(Lib::DHMap<InductionScheme*, Lib::DHMap<Literal*, Clause*>*>* schemes);
  static void filterFlawedSchemes(Lib::List<InductionScheme*>*& schemes,
    Lib::DHMap<Kernel::TermList, Lib::DHSet<unsigned>*>* activeOccurrenceMap,
    const DHMap<TermList, unsigned>& occurrenceMap);

  static bool canInductOn(Kernel::TermList t);
  static bool isTermAlgebraCons(Kernel::TermList t);
  static Lib::vvector<Kernel::TermList> getInductionTerms(Kernel::TermList t);
  static Lib::DHSet<Kernel::TermList> getInductionTerms(Lib::DHMap<InductionScheme*, DHMap<Literal*, Clause*>*>* schemes);

private:
  static void preprocess(Kernel::UnitList*& units);
  static void processBody(Kernel::TermList& body, Kernel::TermList& header, InductionTemplate*& templ);

  static void processCase(const unsigned recFun, Kernel::TermList& body, Kernel::List<Kernel::TermList>*& recursiveCalls);
  static unsigned findMatchedArgument(unsigned matched, Kernel::TermList& header);

  static bool checkSubsumption(InductionScheme* sch1, InductionScheme* sch2, bool onlyCheckIntersection = false);
  static Lib::List<Kernel::Term*>* getSubstitutedTerms(Kernel::Term* term, Kernel::Term* step,
                                                  Kernel::Term* recursiveCall, const Lib::DArray<bool>& indVars,
                                                  unsigned& currVar, Kernel::DHMap<pair<Kernel::Term*, unsigned>, Lib::vvector<unsigned>>& varMap);
  static bool checkAllContained(Lib::List<Kernel::Term*>* lst1, Lib::List<Kernel::Term*>* lst2, bool onlyCheckIntersection = false);
  static void mergeSchemes(InductionScheme* sch1, InductionScheme*& sch2);
};

} // Shell

#endif