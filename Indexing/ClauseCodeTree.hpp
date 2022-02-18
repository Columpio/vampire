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
 * @file ClauseCodeTree.hpp
 * Defines class ClauseCodeTree.
 */

#ifndef __ClauseCodeTree__
#define __ClauseCodeTree__

#include "Forwards.hpp"

#include "Debug/RuntimeStatistics.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/SortHelper.hpp"

#include "Lib/Allocator.hpp"
#include "Lib/DArray.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/Hash.hpp"
#include "Lib/List.hpp"
#include "Lib/Stack.hpp"

#include "CodeTree.hpp"


namespace Indexing {

using namespace Lib;
using namespace Kernel;

class ClauseCodeTree : public CodeTree
{
protected:
  static void onCodeOpDestroying(CodeOp* op);
  
public:
  ClauseCodeTree();

  void insert(Clause* cl);
  void remove(Clause* cl);

private:

  //////// insertion //////////

  struct InitialLiteralOrderingComparator;

  void optimizeLiteralOrder(DArray<Literal*>& lits);
  void evalSharing(Literal* lit, CodeOp* startOp, size_t& sharedLen, size_t& unsharedLen, CodeOp*& nextOp);
  static void matchCode(CodeStack& code, CodeOp* startOp, size_t& matchedCnt, CodeOp*& nextOp);

  //////// removal //////////

  bool removeOneOfAlternatives(CodeOp* op, Clause* cl, Stack<CodeOp*>* firstsInBlocks);

  struct RemovingLiteralMatcher
  : public RemovingMatcher
  {
    void init(CodeOp* entry_, LitInfo* linfos_, size_t linfoCnt_,
	ClauseCodeTree* tree_, Stack<CodeOp*>* firstsInBlocks_);

    CLASS_NAME(ClauseCodeTree::RemovingLiteralMatcher);
    USE_ALLOCATOR(RemovingLiteralMatcher);
  };

  //////// retrieval //////////

  /** Context for finding matches of literals
   *
   * Here the actual execution of the code of the tree takes place */
  struct LiteralMatcher
  : public Matcher
  {
    void init(CodeTree* tree, CodeOp* entry_, LitInfo* linfos_, size_t linfoCnt_, bool seekOnlySuccess=false);
    bool next();
    bool doEagerMatching();

    inline bool eagerlyMatched() const { return _eagerlyMatched; }

    inline ILStruct* getILS() { ASS(matched()); return op->getILS(); }

    CLASS_NAME(ClauseCodeTree::LiteralMatcher);
    USE_ALLOCATOR(LiteralMatcher);

  private:
    bool _eagerlyMatched;

    Stack<CodeOp*> eagerResults;

    void recordMatch();
  };

public:
  template<class Array>
  struct ClauseMatcher
  {
    void init(ClauseCodeTree* tree_, Array* query_, bool sres_);
    void deinit();

    Clause* next(int& resolvedQueryLit);

    bool matched() { return lms.isNonEmpty() && lms.top()->success(); }
    CodeOp* getSuccessOp() { ASS(matched()); return lms.top()->op; }

    CLASS_NAME(ClauseCodeTree::ClauseMatcher);
    USE_ALLOCATOR(ClauseMatcher);

  private:
    void enterLiteral(CodeOp* entry, bool seekOnlySuccess);
    void leaveLiteral();
    bool canEnterLiteral(CodeOp* op);

    bool checkCandidate(Clause* cl, int& resolvedQueryLit);
    bool matchGlobalVars(int& resolvedQueryLit);
    bool compatible(ILStruct* bi, MatchInfo* bq, ILStruct* ni, MatchInfo* nq);

    bool existsCompatibleMatch(ILStruct* si, MatchInfo* sq, ILStruct* oi);

    Array* query;
    ClauseCodeTree* tree;
    bool sres;

    static const unsigned sresNoLiteral=static_cast<unsigned>(-1);
    unsigned sresLiteral;

    /**
     * Literal infos that we will attempt to match
     * For each equality we add two lit infos, once with reversed arguments.
     * The order of infos is:
     *
     * Ground literals
     * Non-ground literals
     * [if sres] Ground literals negated
     * [if sres] Non-ground literals negated
     */
    DArray<LitInfo> lInfos;

    Stack<LiteralMatcher*> lms;
  };

private:

  //////// member variables //////////

#if VDEBUG
  unsigned _clauseMatcherCounter;
#endif

};


////////// ClauseMatcher

/**
 * Initialize the ClauseMatcher to retrieve generalizetions
 * of the @b query_ clause.
 * If @b sres_ if true, we perform subsumption resolution
 */
template<class Array>
void ClauseCodeTree::ClauseMatcher<Array>::init(ClauseCodeTree* tree_, Array* query_, bool sres_)
{
  CALL("ClauseCodeTree::ClauseMatcher::init");
  ASS(!tree_->isEmpty());

  query=query_;
  tree=tree_;
  sres=sres_;
  lms.reset();

#if VDEBUG
  ASS_EQ(tree->_clauseMatcherCounter,0);
  tree->_clauseMatcherCounter++;
#endif

  //init LitInfo records
  unsigned clen=query->length();
  unsigned baseLICnt=clen;
  for(unsigned i=0;i<clen;i++) {
    if((*query)[i]->isEquality()) {
      baseLICnt++;
    }
  }
  unsigned liCnt=sres ? (baseLICnt*2) : baseLICnt;
  lInfos.ensure(liCnt);

  //we put ground literals first
  unsigned liIndex=0;
  for(unsigned i=0;i<clen;i++) {
    if(!(*query)[i]->ground()) {
      continue;
    }
    lInfos[liIndex]=LitInfo(query,i);
    lInfos[liIndex].liIndex=liIndex;
    liIndex++;
    if((*query)[i]->isEquality()) {
      lInfos[liIndex]=LitInfo::getReversed(lInfos[liIndex-1]);
      lInfos[liIndex].liIndex=liIndex;
      liIndex++;
    }
  }
  for(unsigned i=0;i<clen;i++) {
    if((*query)[i]->ground()) {
      continue;
    }
    lInfos[liIndex]=LitInfo(query,i);
    lInfos[liIndex].liIndex=liIndex;
    liIndex++;
    if((*query)[i]->isEquality()) {
      lInfos[liIndex]=LitInfo::getReversed(lInfos[liIndex-1]);
      lInfos[liIndex].liIndex=liIndex;
      liIndex++;
    }
  }
  if(sres) {
    for(unsigned i=0;i<baseLICnt;i++) {
      unsigned newIndex=i+baseLICnt;
      lInfos[newIndex]=LitInfo::getOpposite(lInfos[i]);
      lInfos[newIndex].liIndex=newIndex;
    }
    sresLiteral=sresNoLiteral;
  }

  tree->incTimeStamp();
  enterLiteral(tree->getEntryPoint(), clen==0);
}

template<class Array>
void ClauseCodeTree::ClauseMatcher<Array>::deinit()
{
  CALL("ClauseCodeTree::ClauseMatcher::deinit");

  unsigned liCnt=lInfos.size();
  for(unsigned i=0;i<liCnt;i++) {
    lInfos[i].dispose();
  }
  while(lms.isNonEmpty()) {
    LiteralMatcher* lm=lms.pop();
    Recycler::release(lm);
  }

#if VDEBUG
  ASS_EQ(tree->_clauseMatcherCounter,1);
  tree->_clauseMatcherCounter--;
#endif
}

/**
 * Return next clause matching query or 0 if there is not such
 */
template<class Array>
Clause* ClauseCodeTree::ClauseMatcher<Array>::next(int& resolvedQueryLit)
{
  CALL("ClauseCodeTree::ClauseMatcher::next");

  if(lms.isEmpty()) {
    return 0;
  }

  for(;;) {
    LiteralMatcher* lm=lms.top();

    //get next literal from the literal matcher
    bool found=lm->next();

    //if there's none, go one level up (or fail if at the top)
    if(!found) {
      leaveLiteral();
      if(lms.isEmpty()) {
	return 0;
      }
    }
    else if(lm->op->isSuccess()) {
      Clause* candidate=static_cast<Clause*>(lm->op->getSuccessResult());
      RSTAT_MCTR_INC("candidates", lms.size()-1);
      if(checkCandidate(candidate, resolvedQueryLit)) {
	RSTAT_MCTR_INC("candidates (success)", lms.size()-1);
	return candidate;
      }
    }
    else if(canEnterLiteral(lm->op)) {
      ASS(lm->op->isLitEnd());
      ASS_LE(lms.size(), query->length()); //this is due to the seekOnlySuccess part below

      //LIT_END is never the last operation in the CodeBlock,
      //so we can increase here
      CodeOp* newLitEntry=lm->op+1;

      //check that we have cleared the sresLiteral value if it is no longer valid
      ASS(!sres || sresLiteral==sresNoLiteral || sresLiteral<lms.size()-1);

      if(sres && sresLiteral==sresNoLiteral) {
	//we check whether we haven't matched only opposite literals on the previous level
	if(lm->getILS()->noNonOppositeMatches) {
	  sresLiteral=lms.size()-1;
	}
      }

      bool seekOnlySuccess=lms.size()==query->length();
      enterLiteral(newLitEntry, seekOnlySuccess);
    }
  }
}

template<class Array>
inline bool ClauseCodeTree::ClauseMatcher<Array>::canEnterLiteral(CodeOp* op)
{
  CALL("ClauseCodeTree::ClauseMatcher::canEnterLiteral");
  ASS(op->isLitEnd());
  ASS_EQ(lms.top()->op, op);

  ILStruct* ils=op->getILS();
  if(ils->timestamp==tree->_curTimeStamp && ils->visited) {
    return false;
  }

  if(ils->isVarEqLit) {
    TermList idxVarSort = ils->varEqLitSort;
    size_t matchIndex=ils->matchCnt;
    while(matchIndex!=0) {
      matchIndex--;
      MatchInfo* mi=ils->getMatch(matchIndex);
      unsigned liIntex = mi->liIndex;
      Literal* lit = (*query)[lInfos[liIntex].litIndex];
      ASS(lit->isEquality());
      TermList argSort = SortHelper::getEqualityArgumentSort(lit); 
      if(idxVarSort!=argSort) {//TODO check that this is what we want. Perhaps require unification
        ils->deleteMatch(matchIndex); //decreases ils->matchCnt
      }
    }
    if(!ils->matchCnt) {
      return false;
    }
  }

  if(lms.size()>1) {
    //we have already matched and entered some index literals, so we
    //will check for compatibility of variable assignments
    if(ils->varCnt && !lms.top()->eagerlyMatched()) {
      lms.top()->doEagerMatching();
      RSTAT_MST_INC("match count", lms.size()-1, lms.top()->getILS()->matchCnt);
    }
    for(size_t ilIndex=0;ilIndex<lms.size()-1;ilIndex++) {
      ILStruct* prevILS=lms[ilIndex]->getILS();
      if(prevILS->varCnt && !lms[ilIndex]->eagerlyMatched()) {
	lms[ilIndex]->doEagerMatching();
	RSTAT_MST_INC("match count", ilIndex, lms[ilIndex]->getILS()->matchCnt);
      }

      size_t matchIndex=ils->matchCnt;
      while(matchIndex!=0) {
	matchIndex--;
	MatchInfo* mi=ils->getMatch(matchIndex);
	if(!existsCompatibleMatch(ils, mi, prevILS)) {
	  ils->deleteMatch(matchIndex); //decreases ils->matchCnt
	}
      }
      if(!ils->matchCnt) {
	return false;
      }
    }
  }

  return true;
}

/**
 * Enter literal matching starting at @c entry.
 *
 * @param entry the code tree node
 * @param seekOnlySuccess if true, accept only SUCCESS operations
 *   (this is to be used when all literals are matched so we want
 *   to see just clauses that end at this point).
 */
template<class Array>
void ClauseCodeTree::ClauseMatcher<Array>::enterLiteral(CodeOp* entry, bool seekOnlySuccess)
{
  CALL("ClauseCodeTree::ClauseMatcher::enterLiteral");

  if(!seekOnlySuccess) {
    RSTAT_MCTR_INC("enterLiteral levels (non-sos)", lms.size());
  }

  if(lms.isNonEmpty()) {
    LiteralMatcher* prevLM=lms.top();
    ILStruct* ils=prevLM->op->getILS();
    ASS_EQ(ils->timestamp,tree->_curTimeStamp);
    ASS(!ils->visited);
    ASS(!ils->finished);
    ils->visited=true;
  }

  size_t linfoCnt=lInfos.size();
  if(sres && sresLiteral!=sresNoLiteral) {
    ASS_L(sresLiteral,lms.size());
    //we do not need to match index literals with opposite query
    //literals, as one of already matched index literals matched only
    //to opposite literals (and opposite literals cannot be matched
    //on more than one index literal)
    ASS_EQ(linfoCnt%2,0);
    linfoCnt/=2;
  }

  LiteralMatcher* lm;
  Recycler::get(lm);
  lm->init(tree, entry, lInfos.array(), linfoCnt, seekOnlySuccess);
  lms.push(lm);
}

template<class Array>
void ClauseCodeTree::ClauseMatcher<Array>::leaveLiteral()
{
  CALL("ClauseCodeTree::ClauseMatcher::leaveLiteral");
  ASS(lms.isNonEmpty());

  LiteralMatcher* lm=lms.pop();
  Recycler::release(lm);

  if(lms.isNonEmpty()) {
    LiteralMatcher* prevLM=lms.top();
    ILStruct* ils=prevLM->op->getILS();
    ASS_EQ(ils->timestamp,tree->_curTimeStamp);
    ASS(ils->visited);

    ils->finished=true;

    if(sres) {
      //clear the resolved literal flag if we have backtracked from it
      unsigned depth=lms.size()-1;
      if(sresLiteral==depth) {
        sresLiteral=sresNoLiteral;
      }
      ASS(sresLiteral==sresNoLiteral || sresLiteral<depth);
    }
  }
}


//////////////// Multi-literal matching

template<class Array>
bool ClauseCodeTree::ClauseMatcher<Array>::checkCandidate(Clause* cl, int& resolvedQueryLit)
{
  CALL("ClauseCodeTree::ClauseMatcher::checkCandidate");

  unsigned clen=cl->length();
  //the last matcher in mls is the one that yielded the SUCCESS operation
  ASS_EQ(clen, lms.size()-1);
  ASS_EQ(clen, lms[clen-1]->op->getILS()->depth+1);

  if(clen<=1) {
    //if clause doesn't have multiple literals, there is no need
    //for multi-literal matching
    resolvedQueryLit=-1;
    if(sres && clen==1) {
      size_t matchCnt=lms[0]->getILS()->matchCnt;
      for(size_t i=0;i<matchCnt;i++) {
	MatchInfo* mi=lms[0]->getILS()->getMatch(i);
	if(lInfos[mi->liIndex].opposite) {
	  resolvedQueryLit=lInfos[mi->liIndex].litIndex;
	}
	else {
	  //we prefer subsumption to subsumption resolution
	  resolvedQueryLit=-1;
	  break;
	}
      }
    }
    return true;
  }

//  if(matchGlobalVars(resolvedQueryLit)) {
//    return true;
//  }

  bool newMatches=false;
  for(int i=clen-1;i>=0;i--) {
    LiteralMatcher* lm=lms[i];
    if(lm->eagerlyMatched()) {
      break;
    }
    if(lm->getILS()->varCnt==0) {
      //If the index term is ground, at most two literals can be matched on
      //it (the second one is the opposite one in case we're performing the
      //subsumption resolution) We are here, so we have matched one already,
      //and we know that the query clause doesn't contain two equal or opposite
      //literals (or else it would have been simplified by duplicate literal
      //removal or by tautology deletion). Therefore we don't need to try
      //matching the rest of the query clause.
      continue;
    }
    newMatches|=lm->doEagerMatching();
  }

  return matchGlobalVars(resolvedQueryLit);
//  return newMatches && matchGlobalVars(resolvedQueryLit);
}

template<class Array>
bool ClauseCodeTree::ClauseMatcher<Array>::matchGlobalVars(int& resolvedQueryLit)
{
  CALL("ClauseCodeTree::ClauseMatcher::matchGlobalVars");

  //TODO: perform _set_, not _multiset_ subsumption for subsumption resolution

//  bool verbose=query->number()==58746;
//#define VERB_OUT(x) if(verbose) {cout<<x<<endl;}

  unsigned clen=lms.size()-1;

  //remaining[j,0] contains number of matches for j-th index literal
  //remaining[j,i+1] (for j>i) contains number of matches for j-th
  //  index literal compatible with the bindings of i-th literal (and
  //  those before it)
  //remaining[j,j] therefore contains number of matches we have to try
  //  when we get to binding j-th literal
  //  Matches in ILStruct::matches are reordered, so that we always try
  //  the _first_ remaining[j,j] literals
  static TriangularArray<int> remaining(10);
  remaining.setSide(clen);
  for(unsigned j=0;j<clen;j++) {
    ILStruct* ils=lms[j]->getILS();
    remaining.set(j,0,ils->matchCnt);

//    VERB_OUT("matches "<<ils->matches.size()<<" index:"<<j<<" vars:"<<ils->varCnt<<" linfos:"<<lInfos.size());
//    for(unsigned y=0;y<ils->matches.size();y++) {
//      LitInfo* linf=&lInfos[ils->matches[y]->liIndex];
//      VERB_OUT(" match "<<y<<" liIndex:"<<ils->matches[y]->liIndex<<" op: "<<linf->opposite);
//      VERB_OUT(" hdr: "<<(*linf->ft)[0].number());
//    }
//    for(unsigned x=0;x<ils->varCnt;x++) {
//      VERB_OUT(" glob var: "<<ils->sortedGlobalVarNumbers[x]);
//      for(unsigned y=0;y<ils->matches.size();y++) {
//	VERB_OUT(" match "<<y<<" binding: "<<ils->matches[y]->bindings[x]);
//      }
//    }
  }
//  VERB_OUT("secOp:"<<(lms[1]->op-1)->instr()<<" "<<(lms[1]->op-1)->arg());

  static DArray<int> matchIndex;
  matchIndex.ensure(clen);
  unsigned failLev=0;
  for(unsigned i=0;i<clen;i++) {
    matchIndex[i]=-1;
    if(i>0) { failLev=20; }
  bind_next_match:
    matchIndex[i]++;
    if(matchIndex[i]==remaining.get(i,i)) {
      //no more choices at this level, so try going up
      if(i==0) {
	RSTAT_MCTR_INC("zero level fails at", failLev);
	return false;
      }
      i--;
      goto bind_next_match;
    }
    ASS_L(matchIndex[i],remaining.get(i,i));

    ILStruct* bi=lms[i]->getILS(); 		//bound index literal
    MatchInfo* bq=bi->getMatch(matchIndex[i]);	//bound query literal

    //propagate the implications of this binding to next literals
    for(unsigned j=i+1;j<clen;j++) {
      ILStruct* ni=lms[j]->getILS();		//next index literal
      unsigned rem=remaining.get(j,i);
      unsigned k=0;
      while(k<rem) {
	MatchInfo* nq=ni->getMatch(k);		//next query literal
	if(!compatible(bi,bq,ni,nq)) {
	  rem--;
	  swap(ni->getMatch(k),ni->getMatch(rem));
	  continue;
	}
	k++;
      }
      if(rem==0) {
	if(failLev<j) { failLev=j; }
	goto bind_next_match;
      }
      remaining.set(j,i+1,rem);
    }
  }

  resolvedQueryLit=-1;
  if(sres) {
    for(unsigned i=0;i<clen;i++) {
      ILStruct* ils=lms[i]->getILS();
      MatchInfo* mi=ils->getMatch(matchIndex[i]);
      if(lInfos[mi->liIndex].opposite) {
	resolvedQueryLit=lInfos[mi->liIndex].litIndex;
	break;
      }
    }
  }

  return true;
}

template<class Array>
bool ClauseCodeTree::ClauseMatcher<Array>::compatible(ILStruct* bi, MatchInfo* bq, ILStruct* ni, MatchInfo* nq)
{
  CALL("ClauseCodeTree::ClauseMatcher::compatible");

  if( lInfos[bq->liIndex].litIndex==lInfos[nq->liIndex].litIndex ||
      (lInfos[bq->liIndex].opposite && lInfos[nq->liIndex].opposite) ) {
    return false;
  }

  unsigned bvars=bi->varCnt;
  unsigned* bgvn=bi->sortedGlobalVarNumbers;
  TermList* bb=bq->bindings;

  unsigned nvars=ni->varCnt;
  unsigned* ngvn=ni->sortedGlobalVarNumbers;
  TermList* nb=nq->bindings;

  while(bvars && nvars) {
    while(bvars && *bgvn<*ngvn) {
      bvars--;
      bgvn++;
      bb++;
    }
    if(!bvars) {
      break;
    }
    while(nvars && *bgvn>*ngvn) {
      nvars--;
      ngvn++;
      nb++;
    }
    while(bvars && nvars && *bgvn==*ngvn) {
      if(*bb!=*nb) {
	return false;
      }
      bvars--;
      bgvn++;
      bb++;
      nvars--;
      ngvn++;
      nb++;
    }
  }

  return true;
}

template<class Array>
bool ClauseCodeTree::ClauseMatcher<Array>::existsCompatibleMatch(ILStruct* si, MatchInfo* sq, ILStruct* targets)
{
  CALL("ClauseCodeTree::ClauseMatcher::existsCompatibleMatch");

  size_t tcnt=targets->matchCnt;
  for(size_t i=0;i<tcnt;i++) {
    if(compatible(si,sq,targets,targets->getMatch(i))) {
      return true;
    }
  }
  return false;
}

};

#endif // __ClauseCodeTree__
