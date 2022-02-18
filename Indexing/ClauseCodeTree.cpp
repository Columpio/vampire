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
 * @file ClauseCodeTree.cpp
 * Implements class ClauseCodeTree.
 */

#include <utility>

#include "Debug/RuntimeStatistics.hpp"

#include "Lib/BitUtils.hpp"
#include "Lib/Comparison.hpp"
#include "Lib/Int.hpp"
#include "Lib/Recycler.hpp"
#include "Lib/Sort.hpp"
#include "Lib/TriangularArray.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/FlatTerm.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"

#include "ClauseCodeTree.hpp"

#undef RSTAT_COLLECTION
#define RSTAT_COLLECTION 0

namespace Indexing
{

using namespace Lib;
using namespace Kernel;

void ClauseCodeTree::onCodeOpDestroying(CodeOp* op)
{
  CALL("ClauseCodeTree::onCodeOpDestroying");
    
  if (op->isLitEnd()) {
    delete op->getILS(); 
  }
}

ClauseCodeTree::ClauseCodeTree()
{
  _clauseCodeTree=true;
  _onCodeOpDestroying = onCodeOpDestroying;
#if VDEBUG
  _clauseMatcherCounter=0;
#endif
}

//////////////// insertion ////////////////////

void ClauseCodeTree::insert(Clause* cl)
{
  CALL("ClauseCodeTree::insert");

  unsigned clen=cl->length();
  static DArray<Literal*> lits;
  lits.initFromArray(clen, *cl);

  optimizeLiteralOrder(lits);

  static CodeStack code;
  code.reset();

  static CompileContext cctx;
  cctx.init();

  for(unsigned i=0;i<clen;i++) {
    compileTerm(lits[i], code, cctx, true);
  }
  code.push(CodeOp::getSuccess(cl));

  cctx.deinit(this);

  incorporate(code);
  ASS(code.isEmpty());
}

struct ClauseCodeTree::InitialLiteralOrderingComparator
{
  Comparison compare(Literal* l1, Literal* l2)
  {
    if(l1->weight()!=l2->weight()) {
      return Int::compare(l2->weight(), l1->weight());
    }
    return Int::compare(l1, l2);
  }
};

void ClauseCodeTree::optimizeLiteralOrder(DArray<Literal*>& lits)
{
  CALL("ClauseCodeTree::optimizeLiteralOrder");

  unsigned clen=lits.size();
  if(isEmpty() || clen<=1) {
    return;
  }

  lits.sort(InitialLiteralOrderingComparator());

  CodeOp* entry=getEntryPoint();
  for(unsigned startIndex=0;startIndex<clen-1;startIndex++) {
//  for(unsigned startIndex=0;startIndex<1;startIndex++) {

    size_t unshared=1;
    unsigned bestIndex=startIndex;
    size_t bestSharedLen;
    bool bestGround=lits[startIndex]->ground();
    CodeOp* nextOp;
    evalSharing(lits[startIndex], entry, bestSharedLen, unshared, nextOp);
    if(!unshared) {
      goto have_best;
    }

    for(unsigned i=startIndex+1;i<clen;i++) {
      size_t sharedLen;
      evalSharing(lits[i], entry, sharedLen, unshared, nextOp);
      if(!unshared) {
	bestIndex=i;
        goto have_best;
      }

      if(sharedLen>bestSharedLen && (!bestGround || lits[i]->ground()) ) {
//	cout<<lits[i]->toString()<<" is better than "<<lits[bestIndex]->toString()<<endl;
	bestSharedLen=sharedLen;
	bestIndex=i;
	bestGround=lits[i]->ground();
      }
    }

  have_best:
    swap(lits[startIndex],lits[bestIndex]);

    if(unshared) {
      //we haven't matched the whole literal, so we won't proceed with the next one
      return;
    }
    ASS(nextOp);
    entry=nextOp;
  }
}

void ClauseCodeTree::evalSharing(Literal* lit, CodeOp* startOp, size_t& sharedLen, size_t& unsharedLen, CodeOp*& nextOp)
{
  CALL("ClauseCodeTree::evalSharing");

  static CodeStack code;
  static CompileContext cctx;

  code.reset();
  cctx.init();

  compileTerm(lit, code, cctx, true);

  cctx.deinit(this, true);

  matchCode(code, startOp, sharedLen, nextOp);

  unsharedLen=code.size()-sharedLen;

  ASS(code.top().isLitEnd());
  delete code.pop().getILS();
}

/**
 * Match the operations in @b code CodeStack on the code starting at @b startOp.
 *
 * Into @b matchedCnt assign number of matched operations and into @b lastAttemptedOp
 * the last operation on which we have attempted matching. If @b matchedCnt==code.size(),
 * the @b lastAttemptedOp is equal to the last operation in the @b code stack, otherwise
 * it is the first operation on which mismatch occurred and there was no alternative to
 * proceed to (in this case it therefore holds that @b lastAttemptedOp->alternative==0 ).
 */
void ClauseCodeTree::matchCode(CodeStack& code, CodeOp* startOp, size_t& matchedCnt, CodeOp*& nextOp)
{
  CALL("ClauseCodeTree::matchCode");

  size_t clen=code.length();
  CodeOp* treeOp=startOp;

  for(size_t i=0;i<clen;i++) {
    for(;;) {
      if(treeOp->isSearchStruct()) {
	SearchStruct* ss=treeOp->getSearchStruct();
	CodeOp** toPtr;
	if(ss->getTargetOpPtr(code[i], toPtr) && *toPtr) {
	  treeOp=*toPtr;
	  continue;
	}
      }
      else if(code[i].equalsForOpMatching(*treeOp)) {
	break;
      }
      ASS_NEQ(treeOp,treeOp->alternative());
      treeOp=treeOp->alternative();
      if(!treeOp) {
	matchedCnt=i;
	nextOp=0;
	return;
      }
    }

    //the SEARCH_STRUCT operation does not occur in a CodeBlock
    ASS(!treeOp->isSearchStruct());
    //we can safely do increase because as long as we match and something
    //remains in the @b code stack, we aren't at the end of the CodeBlock
    //either (as each code block contains at least one FAIL or SUCCESS
    //operation, and CodeStack contains at most one SUCCESS as the last
    //operation)
    treeOp++;
  }
  //we matched the whole CodeStack
  matchedCnt=clen;
  nextOp=treeOp;
}


//////////////// removal ////////////////////

void ClauseCodeTree::remove(Clause* cl)
{
  CALL("ClauseCodeTree::remove");

  static DArray<LitInfo> lInfos;
  static Stack<CodeOp*> firstsInBlocks;
  static Stack<RemovingLiteralMatcher*> rlms;

  unsigned clen=cl->length();
  lInfos.ensure(clen);
  firstsInBlocks.reset();
  rlms.reset();

  if(!clen) {
    CodeOp* op=getEntryPoint();
    firstsInBlocks.push(op);
    if(!removeOneOfAlternatives(op, cl, &firstsInBlocks)) {
      ASSERTION_VIOLATION;
      INVALID_OPERATION("empty clause to be removed was not found");
    }
    return;
  }

  for(unsigned i=0;i<clen;i++) {
    lInfos[i]=LitInfo(cl,i);
    lInfos[i].liIndex=i;
  }
  incTimeStamp();

  CodeOp* op=getEntryPoint();
  firstsInBlocks.push(op);
  unsigned depth=0;
  for(;;) {
    RemovingLiteralMatcher* rlm;
    Recycler::get(rlm);
    rlm->init(op, lInfos.array(), lInfos.size(), this, &firstsInBlocks);
    rlms.push(rlm);

  iteration_restart:
    if(!rlm->next()) {
      if(depth==0) {
	ASSERTION_VIOLATION;
	INVALID_OPERATION("clause to be removed was not found");
      }
      Recycler::release(rlms.pop());
      depth--;
      rlm=rlms.top();
      goto iteration_restart;
    }

    op=rlm->op;
    ASS(op->isLitEnd());
    ASS_EQ(op->getILS()->depth, depth);

    if(op->getILS()->timestamp==_curTimeStamp) {
      //we have already been here
      goto iteration_restart;
    }
    op->getILS()->timestamp=_curTimeStamp;

    op++;
    if(depth==clen-1) {
      if(removeOneOfAlternatives(op, cl, &firstsInBlocks)) {
	//successfully removed
	break;
      }
      goto iteration_restart;
    }
    ASS_L(depth,clen-1);
    depth++;
  }

  while(rlms.isNonEmpty()) {
    Recycler::release(rlms.pop());
  }
  for(unsigned i=0;i<clen;i++) {
    lInfos[i].dispose();
  }
}

void ClauseCodeTree::RemovingLiteralMatcher::init(CodeOp* entry_, LitInfo* linfos_,
    size_t linfoCnt_, ClauseCodeTree* tree_, Stack<CodeOp*>* firstsInBlocks_)
{
  CALL("ClauseCodeTree::RemovingLiteralMatcher::init");

  RemovingMatcher::init(entry_, linfos_, linfoCnt_, tree_, firstsInBlocks_);

  ALWAYS(prepareLiteral());
}

/**
 * The first operation of the CodeBlock containing @b op
 * must already be on the @b firstsInBlocks stack.
 */
bool ClauseCodeTree::removeOneOfAlternatives(CodeOp* op, Clause* cl, Stack<CodeOp*>* firstsInBlocks)
{
  CALL("ClauseCodeTree::removeOneOfAlternatives");

  unsigned initDepth=firstsInBlocks->size();

  while(!op->isSuccess() || op->getSuccessResult()!=cl) {
    op=op->alternative();
    if(!op) {
      firstsInBlocks->truncate(initDepth);
      return false;
    }
    firstsInBlocks->push(op);
  }
  op->makeFail();
  optimizeMemoryAfterRemoval(firstsInBlocks, op);
  return true;
}

//////////////// retrieval ////////////////////

////////// LiteralMatcher

/**
 * If @b seekOnlySuccess if true, we will look only for immediate SUCCESS operations
 *  and fail if there isn't any at the beginning (possibly also among alternatives).
 */
void ClauseCodeTree::LiteralMatcher::init(CodeTree* tree_, CodeOp* entry_,
					  LitInfo* linfos_, size_t linfoCnt_,
					  bool seekOnlySuccess)
{
  CALL("ClauseCodeTree::LiteralMatcher::init");
  ASS_G(linfoCnt_,0);

  Matcher::init(tree_,entry_);

  linfos=linfos_;
  linfoCnt=linfoCnt_;

  _eagerlyMatched=false;
  eagerResults.reset();

  RSTAT_CTR_INC("LiteralMatcher::init");
  if(seekOnlySuccess) {
    RSTAT_CTR_INC("LiteralMatcher::init - seekOnlySuccess");
    //we are interested only in SUCCESS operations
    //(and those must be at the entry point or its alternatives)

    _eagerlyMatched=true;
    _fresh=false;
    CodeOp* sop=entry;
    while(sop) {
      if(sop->isSuccess()) {
	eagerResults.push(sop);
      }
      sop=sop->alternative();
    }
    return;
  }

  ALWAYS(prepareLiteral());
}

/**
 * Try to find a match, and if one is found, return true
 */
bool ClauseCodeTree::LiteralMatcher::next()
{
  CALL("ClauseCodeTree::LiteralMatcher::next");

  if(eagerlyMatched()) {
    _matched=!eagerResults.isEmpty();
    if(!_matched) {
      return false;
    }
    op=eagerResults.pop();
    return true;
  }

  if(finished()) {
    //all possible matches are exhausted
    return false;
  }

  _matched=execute();
  if(!_matched) {
    return false;
  }

  ASS(op->isLitEnd() || op->isSuccess());
  if(op->isLitEnd()) {
    recordMatch();
  }
  return true;
}

/**
 * Perform eager matching and return true iff new matches were found
 */
bool ClauseCodeTree::LiteralMatcher::doEagerMatching()
{
  CALL("ClauseCodeTree::LiteralMatcher::doEagerMatching");
  ASS(!eagerlyMatched()); //eager matching can be done only once
  ASS(eagerResults.isEmpty());
  ASS(!finished());

  //backup the current op
  CodeOp* currOp=op;

  static Stack<CodeOp*> eagerResultsRevOrder;
  static Stack<CodeOp*> successes;
  eagerResultsRevOrder.reset();
  successes.reset();

  while(execute()) {
    if(op->isLitEnd()) {
      recordMatch();
      eagerResultsRevOrder.push(op);
    }
    else {
      ASS(op->isSuccess());
      successes.push(op);
    }
  }

  //we want to yield results in the order we found them
  //(otherwise the subsumption resolution would be preferred to the
  //subsumption)
  while(eagerResultsRevOrder.isNonEmpty()) {
    eagerResults.push(eagerResultsRevOrder.pop());
  }
  //we want to yield SUCCESS operations first (as after them there may
  //be no need for further clause retrieval)
  while(successes.isNonEmpty()) {
    eagerResults.push(successes.pop());
  }

  _eagerlyMatched=true;

  op=currOp; //restore the current op

  return eagerResults.isNonEmpty();
}

void ClauseCodeTree::LiteralMatcher::recordMatch()
{
  CALL("ClauseCodeTree::LiteralMatcher::recordMatch");
  ASS(matched());

  ILStruct* ils=op->getILS();
  ils->ensureFreshness(tree->_curTimeStamp);
  if(ils->finished) {
    //no need to record matches which we already know will not lead to anything
    return;
  }
  if(!ils->matchCnt && linfos[curLInfo].opposite) {
    //if we're matching opposite matches, we have already tried all non-opposite ones
    ils->noNonOppositeMatches=true;
  }
  ils->addMatch(linfos[curLInfo].liIndex, bindings);
}

}
