/**
 * @file CLTBMode.cpp
 * Implements class CLTBMode.
 * @since 03/06/2013 updated to conform to the CASC-J6 specification
 * @author Andrei Voronkov
 */
#include <fstream>
#include <cstdlib>
#include <csignal>
#include <sstream>

#include "Lib/Portability.hpp"

#if !COMPILER_MSVC

#include "Lib/DHSet.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Exception.hpp"
#include "Lib/Int.hpp"
#include "Lib/StringUtils.hpp"
#include "Lib/System.hpp"
#include "Lib/TimeCounter.hpp"
#include "Lib/Timer.hpp"
#include "Lib/ScopedPtr.hpp"

#include "Lib/Sys/Multiprocessing.hpp"
#include "Lib/Sys/SyncPipe.hpp"

#include "Shell/Options.hpp"
#include "Shell/Normalisation.hpp"
#include "Saturation/ProvingHelper.hpp"
#include "Shell/Statistics.hpp"
#include "Shell/UIHelper.hpp"

#include "Parse/TPTP.hpp"

#include "CASCMode.hpp"

#include "CLTBMode.hpp"

#define SLOWNESS 1.15

using namespace CASC;
using namespace std;
using namespace Lib;
using namespace Lib::Sys;
using namespace Saturation;

/**
 * The function that does all the job: reads the input files and runs
 * Vampires to solve problems.
 * @since 05/06/2013 Vienna, adapted for CASC-J6
 * @author Andrei Voronkov
 */
void CLTBMode::perform()
{
  CALL("CLTBMode::perform");

  if (env.options->inputFile() == "") {
    USER_ERROR("Input file must be specified for ltb mode");
  }
  // to prevent from terminating by time limit
  env.options->setTimeLimitInSeconds(100000);

  //UIHelper::szsOutput = true;
  env.options->setProof(Options::Proof::TPTP);
  env.options->setStatistics(Options::Statistics::NONE);

  vstring line;
  vstring inputFile = env.options->inputFile();
  std::size_t found = inputFile.find_last_of("/");
  vstring inputDirectory = ".";
  if(found != vstring::npos){
    inputDirectory = inputFile.substr(0,found); 
  }

  ifstream in(inputFile.c_str());
  if (in.fail()) {
    USER_ERROR("Cannot open input file: " + env.options->inputFile());
  }

  //support several batches in one file
  bool firstBatch=true;
  while (!in.eof()) {
    vostringstream singleInst;
    bool ready = false;
    while (!in.eof()) {
      getline(in, line);
      singleInst << line << endl;
      if (line == "% SZS end BatchProblems") {
	ready = true;
	break;
      }
    }
    if (!ready) {
      break;
    }
    CLTBMode ltbm;
    vistringstream childInp(singleInst.str());
    ltbm.solveBatch(childInp,firstBatch,inputDirectory);
    firstBatch=false;
  }
} // CLTBMode::perform

/**
 * This function processes a single batch in a batch file. It makes the following
 * steps: 
 * <ol><li>read the batch file</li>
 * <li>load the common axioms and put them into a SInE selector</li>
 * <li>spawn child processes that try to prove a problem by calling
 *     CLTBProblem::searchForProof(). These processes are run sequentially and the time
 *     limit for each one is computed depending on the per-problem time limit,
 *     batch time limit, and time spent on this batch so far. The termination
 *     time for the proof search for a problem will be passed to
 *     CLTBProblem::searchForProof() as an argument.</li></ol>
 * @author Andrei Voronkov
 * @since 04/06/2013 flight Manchester-Frankfurt
 */
void CLTBMode::solveBatch(istream& batchFile, bool first,vstring inputDirectory)
{
  CALL("CLTBMode::solveBatch(istream& batchfile)");

  // this is the time in milliseconds since the start when this batch file should terminate
  _timeUsedByPreviousBatches = env.timer->elapsedMilliseconds();
  coutLineOutput() << "Starting Vampire on the batch file " << "\n";
  int terminationTime = readInput(batchFile,first);
  loadIncludes();

  _biasedLearning = false;
  if (env.options->ltbLearning() != Options::LTBLearning::OFF){
    _learnedFormulasMaxCount = 1;
    _biasedLearning = (env.options->ltbLearning() == Options::LTBLearning::BIASED);
    doTraining();
  }

  int solvedProblems = 0;
  int remainingProblems = _problemFiles.size();
  StringPairStack::BottomFirstIterator probs(_problemFiles);
  while (probs.hasNext()) {
    StringPair res=probs.next();

    vstring probFile= inputDirectory+"/"+res.first;
    vstring outFile= res.second;
    vstring outDir = env.options->ltbDirectory();
    if(!outDir.empty()){
      std::size_t found = outFile.find_last_of("/");
      if(found != vstring::npos){
        outFile = outFile.substr(found);
      }
      outFile= outDir+"/"+outFile;
    }

    // calculate the next problem time limit in milliseconds
    int elapsedTime = env.timer->elapsedMilliseconds();
    int timeRemainingForThisBatch = terminationTime - elapsedTime;
    coutLineOutput() << "time remaining for this batch " << timeRemainingForThisBatch << endl;
    int remainingBatchTimeForThisProblem = timeRemainingForThisBatch / remainingProblems;
    coutLineOutput() << "remaining batch time for this problem " << remainingBatchTimeForThisProblem << endl;
    int nextProblemTimeLimit;
    if (!_problemTimeLimit) {
      nextProblemTimeLimit = remainingBatchTimeForThisProblem;
    }
    else if (remainingBatchTimeForThisProblem > _problemTimeLimit) {
      nextProblemTimeLimit = _problemTimeLimit;
    }
    else {
      nextProblemTimeLimit = remainingBatchTimeForThisProblem;
    }
    // time in milliseconds when the current problem should terminate
    int problemTerminationTime = elapsedTime + nextProblemTimeLimit;
    coutLineOutput() << "problem termination time " << problemTerminationTime << endl;

    env.beginOutput();
    env.out() << flush << "%" << endl;
    lineOutput() << "SZS status Started for " << probFile << endl << flush;
    env.endOutput();

    pid_t child = Multiprocessing::instance()->fork();
    if (!child) {
      // child process
      CLTBProblem prob(this, probFile, outFile);
      try {
        prob.searchForProof(problemTerminationTime,nextProblemTimeLimit,_category);
      } catch (Exception& exc) {
        cerr << "% Exception at proof search level" << endl;
        exc.cry(cerr);
        System::terminateImmediately(1); //we didn't find the proof, so we return nonzero status code
      }
      // searchForProof() function should never return
      ASSERTION_VIOLATION;
    }

    env.beginOutput();
    lineOutput() << "solver pid " << child << endl;
    env.endOutput();
    int resValue;
    // wait until the child terminates
    try {
      pid_t finishedChild = Multiprocessing::instance()->waitForChildTermination(resValue);
      ASS_EQ(finishedChild, child);
    }
    catch(SystemFailException& ex) {
      cerr << "% SystemFailException at batch level" << endl;
      ex.cry(cerr);
    }

    // output the result depending on the termination code
    env.beginOutput();
    if (!resValue) {
      lineOutput() << "SZS status Theorem for " << probFile << endl;
      solvedProblems++;

      if (env.options->ltbLearning() != Options::LTBLearning::OFF){
        // As we solved it we can learn from the proof
        learnFromSolutionFile(outFile);
      }
    }
    else {
      lineOutput() << "SZS status GaveUp for " << probFile << endl;
    }
    env.out() << flush << '%' << endl;
    lineOutput() << "% SZS status Ended for " << probFile << endl << flush;
    env.endOutput();

    Timer::syncClock();

    remainingProblems--;
  }
  env.beginOutput();
  lineOutput() << "Solved " << solvedProblems << " out of " << _problemFiles.size() << endl;
  env.endOutput();
} // CLTBMode::solveBatch(batchFile)

void CLTBMode::loadIncludes()
{
  CALL("CLTBMode::loadIncludes");

  UnitList* theoryAxioms=0;
  {
    TimeCounter tc(TC_PARSING);
    env.statistics->phase=Statistics::PARSING;

    StringList::Iterator iit(_theoryIncludes);
    while (iit.hasNext()) {
      vstring fname=env.options->includeFileName(iit.next());

      ifstream inp(fname.c_str());
      if (inp.fail()) {
        USER_ERROR("Cannot open included file: "+fname);
      }
      Parse::TPTP parser(inp);
      parser.parse();
      UnitList* funits = parser.units();
      if (parser.containsConjecture()) {
	USER_ERROR("Axiom file " + fname + " contains a conjecture.");
      }

      UnitList::Iterator fuit(funits);
      while (fuit.hasNext()) {
	fuit.next()->markIncluded();
      }
      theoryAxioms=UnitList::concat(funits,theoryAxioms);
    }
  }

  _baseProblem = new Problem(theoryAxioms);
  //ensure we scan the theory axioms for property here, so we don't need to
  //do it afterward in each problem
  _baseProblem->getProperty();
  env.statistics->phase=Statistics::UNKNOWN_PHASE;
} // CLTBMode::loadIncludes


void CLTBMode::learnFromSolutionFile(vstring& solnFileName)
{
  CALL("CLTBMode::learnFromSolutionFile");

    ifstream soln(solnFileName.c_str());
    if (soln.fail()) {
      return; // ignore if we cannot get the solution file
      //USER_ERROR("Cannot open problem file: " + solnFileName);
    }
    cout << "Reading solutions " << solnFileName << endl;

    ScopedPtr<DHMap<Unit*,Parse::TPTP::SourceRecord*> > sources;
    sources = new DHMap<Unit*,Parse::TPTP::SourceRecord*>();

    Parse::TPTP parser(soln);
    parser.setUnitSourceMap(sources.ptr());
    parser.setFilterReserved();
    UnitList* solnUnits = 0;
    try {
      bool outputAxiomValue = env.options->outputAxiomNames();
      env.options->setOutputAxiomNames(true);
      parser.parse();
      env.options->setOutputAxiomNames(outputAxiomValue);
      solnUnits = parser.units();
    } catch (Lib::Exception& ex) {
      cout << "Couldn't parse " << "solnFileName" << endl;
      ex.cry(cout);

      //save memory by deleting the already loaded units:
      UnitList* units = parser.units();
      UnitList::Iterator it(units);
      while (it.hasNext()) {
        Unit* unit = it.next();
        unit->destroy();
      }
      units->destroy();
    }

    UnitList::DelIterator it(solnUnits);
    while (it.hasNext()) {
      Unit* unit = it.next();
      if (unit->inputType()==Unit::AXIOM){
        if (sources->find(unit)){
          if (sources->get(unit)->isFile()){
            vstring name = static_cast<Parse::TPTP::FileSourceRecord*>(sources->get(unit))->nameInFile;
            if (_learnedFormulas.insert(name)){
              // new name
              if (_biasedLearning){
                _learnedFormulasCount.insert(name,1);
              }
            }else{
              if (_biasedLearning){
                ASS_REP(_learnedFormulas.contains(name),name);
                ASS_REP(_learnedFormulasCount.find(name),name);
                // not new
                _learnedFormulasCount.get(name)++;
                if (_learnedFormulasCount.get(name) > _learnedFormulasMaxCount){
                  _learnedFormulasMaxCount = _learnedFormulasCount.get(name);
                }
              //cout << name << "," << _learnedFormulasCount.get(name) << endl;
              }
            }

          }
        }
        else{
          // The Der outputs seem to not do the file thing for input axioms
          // I think it is safe to include the names of these axioms as learned
          // If not I expect we will be unsound
          vstring name;
          if (Parse::TPTP::findAxiomName(unit,name)){
            if (_learnedFormulas.insert(name)){
              // new name
              if (_biasedLearning){
                _learnedFormulasCount.insert(name,1);
              }
            }else{
              if (_biasedLearning){
                ASS_REP(_learnedFormulas.contains(name),name);
                ASS_REP(_learnedFormulasCount.find(name),name);
                // not new
                _learnedFormulasCount.get(name)++;
                if (_learnedFormulasCount.get(name) > _learnedFormulasMaxCount){
                  _learnedFormulasMaxCount = _learnedFormulasCount.get(name);
                }
              //cout << name << "," << _learnedFormulasCount.get(name) << endl;
              }
            }
          }
        }
      }
      it.del();
    }

}


void CLTBMode::doTraining()
{
  CALL("CLTBMode::doTraining");

  env.beginOutput();
  env.out() << "Training in LTB currently unsupported" << endl;
  env.endOutput();
  return;

  Stack<vstring> solutions;
  System::readDir(_trainingDirectory+"/Solutions",solutions);


  Stack<vstring>::Iterator it(solutions);
  while (it.hasNext()) {
    TimeCounter tc(TC_PARSING);
    env.statistics->phase=Statistics::PARSING;

    vstring& solnFileName = it.next();
    learnFromSolutionFile(solnFileName);

  }

  // Idea is to solve training problems and look in proofs for common clauses derived from axioms
  // these can then be loaded into later proof attempts with weight zero to ensure they are processed quickly 
  //
  // training could insert these axioms directly into the base problem object and mark their input type such that
  // they get weight zero in Vampire
  //
  // do to training let's
  // prove the training problems in the same way as the real problems - this will write output to a file per problem
  // this output should contain the proofs
  // read in these files and parse the proofs, building up the clauses to add to the base problem
  // add clauses to the base problem

} // CLTBMode::doTraining

/**
 * Read a single batch file from @b in. Return the time in milliseconds since
 * the start, when the process should terminate. If the batch contains no overall
 * time limit, return a very large integer value.
 * Set _problemTimeLimit to the per-problem time limit from
 * the batch file.
 * @since 04/06/2013 flight Manchester-Frankfurt
 * @author Andrei Voronkov
 */
int CLTBMode::readInput(istream& in, bool first)
{
  CALL("CLTBMode::readInput");

  vstring line, word;

  if(first){
    getline(in,line);
    if (line.find("division.category") != vstring::npos){
        StringStack ls;
        StringUtils::splitStr(line.c_str(),' ',ls);
        _category = getCategory(ls[1]);
        coutLineOutput() << "read category " << ls[1] << endl;
  
        if (_category == Category::UNKNOWN) {
          USER_ERROR("Unrecognized category");
        }
    }
    else{ USER_ERROR("division category not found"); } 
  
    // Get training directory
    getline(in,line);
    if (line.find("training_directory") != vstring::npos){
        StringStack ls;
        StringUtils::splitStr(line.c_str(),' ',ls);
        _trainingDirectory = ls[1];
    }
    else{ USER_ERROR("training_directory not found"); }

  }

  getline(in,line);
  if (line!="% SZS start BatchConfiguration") {
    USER_ERROR("\"% SZS start BatchConfiguration\" expected, \""+line+"\" found.");
  }

  getline(in, line);

  _questionAnswering = false;
  _problemTimeLimit = -1;
  int batchTimeLimit = -1;

  StringStack lineSegments;
  while (!in.eof() && line!="% SZS end BatchConfiguration") {
    lineSegments.reset();
    StringUtils::splitStr(line.c_str(), ' ', lineSegments);
    vstring param = lineSegments[0];
    // not used here now
/*
    if (param == "division.category") {
      if (lineSegments.size()!=2) {
	USER_ERROR("unexpected \""+param+"\" specification: \""+line+"\"");
      }
      _category = lineSegments[1];      
    }
    else
*/
     if (param == "output.required" || param == "output.desired") {
      if (lineSegments.find("Answer")) {
	_questionAnswering = true;
      }
    }
    else if (param == "execution.order") {
      // we ignore this for now and always execute in order
    }
    else
     if (param == "limit.time.problem.wc") {

      if (lineSegments.size() != 2 ||
	  !Int::stringToInt(lineSegments[1], _problemTimeLimit)) {
	USER_ERROR("unexpected \""+param+"\" specification: \""+line+"\"");
      }      
      _problemTimeLimit = 1000 * _problemTimeLimit;
    }
    else if (param == "limit.time.overall.wc") {
      if (lineSegments.size() != 2 ||
	  !Int::stringToInt(lineSegments[1], batchTimeLimit)) {
	USER_ERROR("unexpected \"" + param + "\" specification: \""+ line +"\"");
      }
      batchTimeLimit = 1000 * batchTimeLimit;
    }
    else {
      USER_ERROR("unknown batch configuration parameter: \""+line+"\"");
    }

    getline(in, line);
  }

  if (line != "% SZS end BatchConfiguration") {
    USER_ERROR("\"% SZS end BatchConfiguration\" expected, \"" + line + "\" found.");
  }
  if (_questionAnswering) {
    env.options->setQuestionAnswering(Options::QuestionAnsweringMode::ANSWER_LITERAL);
  }

  getline(in, line);
  if (line!="% SZS start BatchIncludes") {
    USER_ERROR("\"% SZS start BatchIncludes\" expected, \""+line+"\" found.");
  }

  _theoryIncludes=0;
  for (getline(in, line); line[0]!='%' && !in.eof(); getline(in, line)) {
    size_t first=line.find_first_of('\'');
    size_t last=line.find_last_of('\'');
    if (first == vstring::npos || first == last) {
      USER_ERROR("Include specification must contain the file name enclosed in the ' characters:\""+line+"\".");
    }
    ASS_G(last,first);
    vstring fname=line.substr(first+1, last-first-1);
    StringList::push(fname, _theoryIncludes);
  }

  while (!in.eof() && line == "") { getline(in, line); }
  if (line!="% SZS end BatchIncludes") {
    USER_ERROR("\"% SZS end BatchIncludes\" expected, \""+line+"\" found.");
  }
  getline(in, line);
  if (line!="% SZS start BatchProblems") {
    USER_ERROR("\"% SZS start BatchProblems\" expected, \""+line+"\" found.");
  }

  for (getline(in, line); line[0]!='%' && !in.eof(); getline(in, line)) {
    size_t spc=line.find(' ');
    size_t lastSpc=line.find(' ', spc+1);
    if (spc == vstring::npos || spc == 0 || spc == line.length()-1) {
      USER_ERROR("Two file names separated by a single space expected:\""+line+"\".");
    }
    vstring inp=line.substr(0,spc);
    vstring outp=line.substr(spc+1, lastSpc-spc-1);
    _problemFiles.push(make_pair(inp, outp));
  }

  while (!in.eof() && line == "") {
    getline(in, line);
  }
  if (line!="% SZS end BatchProblems") {
    USER_ERROR("\"% SZS end BatchProblems\" expected, \""+line+"\" found.");
  }

  if (batchTimeLimit == -1) { // batch time limit is undefined
    if (_problemTimeLimit == -1) {
      USER_ERROR("either the problem time limit or the batch time limit must be specified");
    }
    // to avoid overflows when added to the current elapsed time, make it less than INT_MAX
    return INT_MAX / 8;
  }

  // batch time limit is defined
  if (_problemTimeLimit == -1) {
    _problemTimeLimit = 0;
  }
  return _timeUsedByPreviousBatches + batchTimeLimit;
} // CLTBMode::readInput

vstring CLTBProblem::problemFinishedString = "##Problem finished##vn;3-d-ca-12=1;'";

CLTBProblem::CLTBProblem(CLTBMode* parent, vstring problemFile, vstring outFile)
  : parent(parent), problemFile(problemFile), outFile(outFile),
    prb(*parent->_baseProblem), _syncSemaphore(1)
{
  //add the privileges into the semaphore
  _syncSemaphore.set(0,1);
}

static void fillSchedule(CLTBProblem::Schedule& sched,Shell::Property* property) {
    sched.push("lrs+1011_3:1_bd=off:bsr=on:cond=fast:gs=on:gsem=on:lwlo=on:nwc=10:stl=34:sd=1:ss=axioms:st=3.0:spl=off:sp=occurrence:updr=off:uhcvi=on_1");
    sched.push("dis+1003_5_cond=on:fsr=off:fde=none:gs=on:gsem=off:nwc=1:sos=on:sdd=large:sser=off:sfr=on:ssfp=100000:ssfq=1.0:ssnc=all_dependent:sp=reverse_arity:urr=ec_only:uhcvi=on_3");
    sched.push("dis+2_5_bd=off:cond=fast:gs=on:lcm=reverse:nwc=1:sd=3:ss=axioms:sos=on:spl=off:sp=occurrence:updr=off:uhcvi=on_3");
    sched.push("dis+1002_3_cond=on:ep=RS:fsr=off:gs=on:gsaa=full_model:gsem=off:nm=0:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:ssfp=4000:ssfq=1.4:smm=off:ssnc=none:updr=off_3");
    sched.push("lrs+10_3_bd=off:cond=fast:fsr=off:nwc=1:stl=34:sd=2:ss=axioms:st=1.5:sos=on:sac=on:sdd=large:sfr=on:ssfp=100000:ssfq=1.4:ssnc=none:sp=occurrence:urr=on:updr=off:uhcvi=on_4");
    sched.push("lrs+1004_4_cond=on:fde=unused:gsp=input_only:gs=on:nwc=1:stl=34:sd=3:ss=axioms:st=5.0:sos=on:spl=off:sp=occurrence:urr=on:updr=off_5");
    sched.push("lrs+11_4:1_br=off:cond=on:fsr=off:fde=unused:gsp=input_only:gs=on:gsssp=full:lcm=predicate:nm=0:nwc=1:stl=34:sd=1:ss=axioms:spl=off:sp=occurrence:urr=on_5");
    sched.push("lrs-11_8:1_bsr=on:cond=on:fde=none:lcm=reverse:nm=0:nwc=1.5:stl=34:sd=2:ss=priority:spl=off:sp=occurrence_8");
    sched.push("dis+2_4_bd=off:cond=fast:fsr=off:fde=none:gs=on:gsem=on:lcm=reverse:lwlo=on:nwc=1:sd=3:ss=axioms:st=1.5:sos=on:spl=off:sp=occurrence:uhcvi=on_9");
    sched.push("dis+11_3_ep=RSTC:fsr=off:fde=none:gs=on:gsaa=from_current:gsem=off:gsssp=full:nwc=1:sd=1:ss=axioms:st=2.0:sos=on:sac=on:sdd=large:sfr=on:ssfp=40000:ssfq=1.2:smm=sco:ssnc=none:sp=reverse_arity:urr=on:uhcvi=on_9");
    sched.push("dis+10_3:1_ep=RST:gsp=input_only:gs=on:gsem=on:lcm=reverse:nwc=1.1:sd=2:ss=priority:st=2.0:sos=on:sac=on:sdd=large:sser=off:ssfp=10000:ssfq=1.1:ssnc=none:sp=reverse_arity_19");
    sched.push("dis+11_2:1_br=off:ep=RST:fde=unused:gsp=input_only:gs=on:gsaa=from_current:gsem=off:nwc=1:sd=1:ss=priority:st=1.2:sos=all:sdd=large:sser=off:ssfp=100000:ssfq=1.1:ssnc=none:sp=occurrence:urr=on_33");
    sched.push("lrs+1011_4:1_bd=off:bsr=unit_only:ccuc=small_ones:fsr=off:fde=unused:gs=on:gsssp=full:nm=64:nwc=4:stl=34:sd=1:ss=priority:sac=on:sscc=model:sdd=large:sser=off:sfr=on:ssfp=100000:ssfq=1.2:ssnc=all:uhcvi=on_33");
    sched.push("lrs+10_5_bd=off:cond=fast:fde=unused:gsp=input_only:gs=on:gsem=on:gsssp=full:nwc=1:stl=34:sd=2:ss=axioms:sos=on:spl=off:urr=on:updr=off:uhcvi=on_35");
    sched.push("dis+1002_1_ep=RST:gs=on:gsaa=full_model:gsem=on:nm=64:nwc=1:sd=7:ss=axioms:st=1.2:sos=on:sser=off:ssfp=40000:ssfq=1.2:ssnc=none:updr=off:uhcvi=on_39");
    sched.push("lrs-4_5:4_bd=off:bs=unit_only:bsr=on:cond=on:fde=none:gs=on:gsaa=full_model:gsem=off:nm=0:nwc=1.1:nicw=on:stl=34:sd=1:ss=axioms:st=2.0:sos=on:sac=on:sfr=on:ssfp=10000:ssfq=1.0:smm=off:ssnc=none:sp=reverse_arity:urr=on:updr=off_41");
    sched.push("ins+11_3_ep=RST:fde=unused:gsp=input_only:igbrr=0.4:igrr=1/8:igrpq=1.5:igs=1:igwr=on:lcm=predicate:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:spl=off:updr=off:dm=on:uhcvi=on_41");
               sched.push("dis+1011_5_fsr=off:fde=unused:nm=64:nwc=3:sd=2:ss=priority:spl=off:sp=occurrence:uhcvi=on_17");
               sched.push("dis+1002_5_cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=off:gsssp=full:nwc=1:sd=1:ss=axioms:st=5.0:sos=on:sac=on:sdd=large:ssfp=40000:ssfq=1.1:smm=off:ssnc=none:sp=reverse_arity:updr=off_21");
               sched.push("dis+1002_4_cond=on:gs=on:gsem=off:nwc=1:sd=1:ss=axioms:sos=on:sac=on:sfr=on:ssfp=1000:ssfq=1.2:smm=sco:ssnc=none:sp=occurrence:uhcvi=on_21");
               sched.push("dis+1011_1_bsr=on:ccuc=first:nm=0:nwc=4:sd=2:ss=priority:sscc=model:sdd=large:sfr=on:smm=off:ssnc=none:updr=off:uhcvi=on_21");
               sched.push("lrs-2_3_ep=RS:gs=on:gsaa=from_current:nwc=1:stl=34:sd=2:ss=axioms:sos=on:sac=on:sfr=on:ssfp=40000:ssfq=1.0:smm=off:ssnc=none:sp=reverse_arity:uhcvi=on_23");
               sched.push("dis+1011_1_fsr=off:fde=unused:nm=64:nwc=1.7:sd=2:ss=priority:spl=off:updr=off_24");
               sched.push("lrs+1011_3:2_bd=off:cond=on:gsp=input_only:gs=on:gsem=on:nm=0:nwc=4:stl=34:sd=1:ss=axioms:sser=off:sfr=on:ssfp=40000:ssfq=1.1:ssnc=all_dependent:sp=reverse_arity:updr=off_24");
               sched.push("dis+1011_3:2_bsr=unit_only:cond=fast:nwc=3:nicw=on:sd=3:ss=priority:sdd=off:sfr=on:ssfp=10000:ssfq=1.2:uhcvi=on_25");
               sched.push("dis+1011_3_fde=unused:nm=64:nwc=1:sd=2:ss=axioms:st=5.0:sdd=off:sser=off:ssfp=10000:ssfq=1.0:sp=occurrence_25");
               sched.push("dis+1002_4_ep=RST:fsr=off:gs=on:gsem=off:lwlo=on:nwc=1:sd=4:ss=axioms:st=1.5:sos=on:sser=off:sfr=on:ssfp=40000:ssfq=1.2:ssnc=none_28");
               sched.push("dis+1002_5_bd=off:fde=none:gs=on:gsaa=from_current:nwc=1:sd=2:ss=axioms:st=2.0:sos=on:sdd=off:sfr=on:ssfp=40000:ssfq=1.0:smm=sco:ssnc=none:updr=off_28");
               sched.push("lrs+1010_1_cond=on:fde=none:gs=on:gsem=off:nwc=1:stl=34:sd=1:ss=axioms:st=3.0:sos=on:sac=on:ssfp=10000:ssfq=1.1:smm=sco:ssnc=none:urr=on:updr=off_36");
               sched.push("ott-11_8:1_bd=preordered:ccuc=first:er=known:fsr=off:fde=unused:gsp=input_only:lcm=predicate:nm=0:nwc=2:sd=3:ss=axioms:sscc=on:ssfp=10000:ssfq=2.0:smm=sco:sp=occurrence:updr=off_1");
               sched.push("dis+1_2:1_cond=on:fsr=off:fde=none:gs=on:gsem=on:lwlo=on:nwc=1.3:sd=2:ss=axioms:spl=off:sp=reverse_arity:urr=on_1");
               sched.push("dis+10_5_cond=on:fsr=off:fde=none:gs=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=on:spl=off_2");
               sched.push("dis+11_3_cond=fast:fsr=off:nwc=1:sd=1:ss=axioms:st=5.0:sdd=off:sfr=on:ssfp=4000:ssfq=1.1:ssnc=none:sp=occurrence:updr=off_2");
               sched.push("lrs+11_8_br=off:cond=on:fde=none:gs=on:gsem=on:gsssp=full:nwc=1:nicw=on:stl=34:sd=1:ss=axioms:st=5.0:sos=all:sac=on:sdd=off:ssfp=100000:ssfq=1.4:smm=off:ssnc=all:sp=reverse_arity:urr=on:uhcvi=on_2");
               sched.push("dis-2_3_gs=on:gsem=on:lcm=reverse:nwc=1:sos=on:ssfp=40000:ssfq=2.0:smm=off:ssnc=none:sp=reverse_arity:uhcvi=on_2");
               sched.push("dis+11_4_bd=off:fsr=off:fde=unused:gs=on:gsaa=full_model:gsem=on:nwc=1:sd=1:ss=axioms:sac=on:sdd=large:ssfp=1000:ssfq=2.0:smm=sco:ssnc=none:sp=reverse_arity_2");
               sched.push("dis+11_4_ep=RS:fde=none:gs=on:gsaa=full_model:gsem=off:nwc=1:sd=1:ss=priority:st=1.2:sos=all:sac=on:ssfp=10000:ssfq=1.1:smm=sco:ssnc=none:sp=reverse_arity:uhcvi=on_2");
               sched.push("dis+1010_2_bs=on:cond=fast:ep=RSTC:fde=unused:lwlo=on:nwc=1:sos=on:sac=on:sdd=off:sfr=on:ssfp=10000:ssfq=1.4:sp=reverse_arity:uhcvi=on_3");
               sched.push("dis+10_5_ep=RST:fsr=off:gs=on:gsssp=full:lwlo=on:nm=0:nwc=1:sd=4:ss=axioms:sos=on:sfr=on:ssfp=40000:ssfq=1.1:smm=off:ssnc=none:uhcvi=on_3");
               sched.push("ins+11_4_bd=off:fsr=off:gsp=input_only:gs=on:gsem=off:igbrr=0.6:igpr=on:igrr=1/128:igrp=700:igrpq=1.2:igs=1004:igwr=on:lcm=predicate:nwc=1:sd=2:ss=axioms:st=5.0:sos=on:spl=off:uhcvi=on_3");
               sched.push("dis+10_5_fsr=off:fde=unused:gs=on:gsem=on:gsssp=full:lcm=reverse:nwc=1:sd=2:ss=axioms:sos=on:sdd=large:sfr=on:ssfp=1000:ssfq=1.1:smm=sco:ssnc=none:sp=occurrence:updr=off:uhcvi=on_3");
               sched.push("dis-1_1_cond=fast:gsp=input_only:gs=on:gsaa=from_current:gsem=off:gsssp=full:nwc=1.3:sd=1:ss=axioms:st=1.2:sos=on:sdd=off:ssfp=1000:ssfq=2.0:smm=sco:sp=occurrence:updr=off_3");
               sched.push("lrs-10_4:1_cond=on:fsr=off:fde=unused:gsp=input_only:gs=on:gsem=on:nwc=1:stl=34:sd=3:ss=axioms:sos=on:spl=off:urr=on_3");
               sched.push("lrs+1011_1_cond=on:fsr=off:gs=on:nwc=1:stl=34:sd=4:ss=priority:st=1.2:sos=on:spl=off:sp=reverse_arity:urr=on_4");
               sched.push("lrs+10_8:1_bsr=unit_only:br=off:cond=on:fsr=off:gsp=input_only:gs=on:gsaa=from_current:nm=0:nwc=1:stl=34:sd=2:ss=axioms:st=1.2:sos=on:sac=on:sdd=large:sfr=on:ssfp=1000:ssfq=1.1:smm=sco:ssnc=none:sp=reverse_arity:urr=on:updr=off:uhcvi=on_4");
               sched.push("lrs+11_5_fde=none:gsp=input_only:gs=on:gsem=on:nwc=1:stl=34:sd=3:ss=axioms:st=3.0:sos=on:spl=off:sp=occurrence:urr=on_4");
               sched.push("ins+11_10_cond=fast:fsr=off:gs=on:gsem=on:igbrr=0.5:igrr=1/2:igrpq=1.3:igs=1003:igwr=on:nwc=1:sd=2:ss=axioms:sos=on:spl=off:sp=reverse_arity_4");
               sched.push("lrs+11_5:1_br=off:cond=fast:fde=unused:gsp=input_only:gs=on:gsem=on:gsssp=full:lcm=predicate:nm=0:nwc=1:nicw=on:stl=34:sd=1:ss=axioms:st=1.2:sac=on:sdd=large:sfr=on:ssfp=40000:ssfq=1.4:smm=sco:ssnc=all:urr=on_4");
               sched.push("dis+1004_3:1_bsr=unit_only:ep=R:fde=unused:gs=on:gsssp=full:nm=0:nwc=1:sos=all:sac=on:sfr=on:ssfp=10000:ssfq=2.0:ssnc=all:sp=reverse_arity:urr=on:updr=off_4");
               sched.push("dis+1010_5_cond=fast:fde=unused:gs=on:gsem=on:nm=0:nwc=1:sd=2:ss=axioms:st=3.0:sos=on:spl=off:sp=occurrence:updr=off:uhcvi=on_5");
               sched.push("dis+10_14_cond=fast:gs=on:gsaa=full_model:gsem=off:gsssp=full:nwc=1.5:sd=1:ss=axioms:st=1.5:ssfp=40000:ssfq=1.1:smm=sco:ssnc=none:sp=occurrence:updr=off_5");
               sched.push("dis+1010_1_cond=fast:fsr=off:nwc=1.3:sd=2:ss=axioms:st=1.5:sos=on:sscc=model:sdd=off:ssfp=4000:ssfq=2.0:uhcvi=on_5");
               sched.push("dis+1002_3_ep=RST:fde=unused:gs=on:gsaa=full_model:gsem=off:nwc=1:sd=1:ss=axioms:st=2.0:sos=on:ssfp=100000:ssfq=1.1:ssnc=none:sp=occurrence:uhcvi=on_5");
               sched.push("dis+1002_2:3_fde=none:gsp=input_only:nm=0:nwc=1:sd=3:ss=axioms:sos=on:sac=on:ssfp=100000:ssfq=1.0:smm=sco:ssnc=none:sp=occurrence:updr=off_5");
               sched.push("lrs+10_2:3_bsr=unit_only:cond=on:fde=none:gs=on:nwc=1:stl=34:sd=2:ss=axioms:sos=on:spl=off:sp=reverse_arity_5");
               sched.push("dis-11_1_cond=fast:nm=0:nwc=1:sd=2:ss=axioms:sac=on:sscc=model:sfr=on:ssfp=100000:ssfq=1.2:smm=off:ssnc=all_dependent:sp=reverse_arity:uhcvi=on_6");
               sched.push("lrs+11_3_br=off:cond=fast:gs=on:gsem=off:nwc=1:stl=34:sd=3:ss=priority:st=1.5:sos=all:sac=on:sfr=on:ssfp=1000:ssfq=2.0:smm=sco:ssnc=none:sp=occurrence:urr=on:uhcvi=on_6");
               sched.push("lrs-2_1_cond=on:fde=unused:gs=on:gsaa=from_current:gsssp=full:lcm=predicate:nwc=1:stl=34:sd=4:ss=axioms:st=3.0:sos=on:sac=on:sfr=on:ssfp=10000:ssfq=1.1:ssnc=none:updr=off_6");
               sched.push("lrs+10_3:1_fde=unused:lcm=reverse:nwc=1:stl=34:sd=3:ss=priority:st=2.0:sos=all:spl=off:sp=occurrence:uhcvi=on_8");
               sched.push("lrs+1_1_bs=on:bsr=on:br=off:cond=fast:fsr=off:gs=on:gsem=off:lwlo=on:nwc=3:stl=34:sd=3:ss=priority:sdd=large:sfr=on:ssfp=40000:ssfq=1.4:smm=off:ssnc=none:sp=occurrence:urr=on:updr=off_9");
               sched.push("dis+11_12_cond=fast:nwc=1:sd=1:ss=axioms:st=1.5:sos=on:spl=off:sp=reverse_arity:uhcvi=on_9");
               sched.push("lrs+10_5:4_bd=off:ccuc=small_ones:cond=on:fde=none:gs=on:gsaa=from_current:gsem=off:nm=0:nwc=1:stl=34:sd=2:ss=priority:sos=on:sscc=model:sdd=large:sser=off:ssfp=100000:ssfq=1.4:ssnc=none:urr=on_9");
               sched.push("dis-10_2:3_cond=on:fde=none:nwc=1:sd=2:ss=axioms:st=2.0:sos=on:spl=off:updr=off:uhcvi=on_11");
               sched.push("dis+10_5_bsr=unit_only:cond=on:ep=RS:fde=unused:nm=0:nwc=1:sd=1:ss=axioms:sos=all:spl=off_12");
               sched.push("lrs+10_4:1_bd=off:cond=fast:fde=unused:lcm=reverse:nm=0:nwc=1.2:stl=34:sd=2:ss=axioms:sos=all:spl=off_14");
               sched.push("dis+10_2:1_cond=fast:ep=RST:fsr=off:fde=unused:gsp=input_only:gs=on:gsaa=full_model:gsem=off:nm=0:nwc=1:sd=1:ss=axioms:st=5.0:sos=on:sac=on:sdd=off:sfr=on:ssfp=100000:ssfq=1.4:smm=sco:ssnc=none:urr=on:updr=off:uhcvi=on_16");
               sched.push("ott+1010_3:1_bs=unit_only:bsr=unit_only:br=off:ccuc=first:cond=fast:fde=unused:gs=on:gsem=on:nwc=1:sd=2:ss=axioms:sos=on:sac=on:ssac=none:sscc=on:sser=off:ssfp=1000:ssfq=2.0:ssnc=all_dependent:sp=reverse_arity:urr=on:updr=off_18");
               sched.push("lrs+1011_8:1_cond=on:fde=none:gsp=input_only:lwlo=on:nwc=1:stl=34:sd=2:ss=axioms:sos=all:spl=off:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_69");
               sched.push("lrs-4_5:4_cond=on:gs=on:gsem=on:gsssp=full:nm=64:nwc=1:stl=34:sd=2:ss=axioms:st=2.0:sos=on:sac=on:ssfp=100000:ssfq=1.1:smm=sco:ssnc=none:urr=on_2");
               sched.push("dis+1004_3:1_cond=fast:fde=unused:nm=0:nwc=1:sd=1:ss=axioms:st=1.2:sos=on:spl=off:sp=reverse_arity:updr=off:uhcvi=on_2");
               sched.push("ott+1010_3:1_cond=fast:fde=unused:nm=64:nwc=1.7:sd=3:ss=priority:spl=off:sp=occurrence:updr=off_3");
               sched.push("dis+1010_4_cond=on:fde=unused:gs=on:gsem=on:nm=0:nwc=1:sd=2:ss=axioms:st=3.0:sos=on:spl=off:updr=off_3");
               sched.push("dis+10_5:4_ep=R:gs=on:gsaa=from_current:nm=64:nwc=1:sd=1:ss=axioms:sos=on:sdd=large:sser=off:ssfp=4000:ssfq=1.1:ssnc=none:updr=off:uhcvi=on_9");
               sched.push("ins+11_5_cond=fast:ep=RST:gs=on:gsem=on:igbrr=0.4:igpr=on:igrr=1/64:igrp=4000:igrpq=1.3:igwr=on:lcm=reverse:nwc=1:sd=2:ss=axioms:st=1.2:sos=on:spl=off:sp=occurrence:dm=on:uhcvi=on_10");
               sched.push("ott+11_2:1_cond=fast:nm=0:nwc=2.5:sd=2:ss=priority:st=1.2:spl=off:sp=occurrence:urr=on:updr=off_27");
               sched.push("lrs+10_3_ep=RS:gs=on:gsem=off:nm=1024:nwc=1:stl=34:sd=2:ss=priority:sos=all:spl=off_28");
               sched.push("lrs+1003_8:1_br=off:cond=on:fde=none:gs=on:gsem=off:nm=0:nwc=1:stl=34:sd=1:ss=axioms:sos=on:sdd=off:sfr=on:ssfp=40000:ssfq=1.1:smm=off:ssnc=none:sp=occurrence:urr=on_28");
               sched.push("lrs+1003_4_bd=off:bsr=unit_only:cond=on:gs=on:gsem=off:nm=0:nwc=1:stl=34:sd=2:ss=axioms:sos=on:spl=off:sp=occurrence:urr=on:updr=off_29");
               sched.push("dis+1002_4_cond=fast:ep=RST:fde=unused:gs=on:gsaa=from_current:gsem=off:nm=0:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:sac=on:sdd=large:ssfp=100000:ssfq=1.0:smm=sco:ssnc=none:updr=off:uhcvi=on_34");
               sched.push("ott+2_2:1_bd=off:bsr=unit_only:cond=on:gs=on:nwc=1:sd=3:ss=priority:st=1.5:sos=on:spl=off:sp=occurrence:updr=off_36");
               sched.push("ott+1011_1_cond=on:fsr=off:fde=none:gs=on:gsem=off:nm=0:nwc=10:sd=1:ss=axioms:st=2.0:spl=off:sp=occurrence:urr=on:updr=off_40");
               sched.push("ott+2_2:1_cond=fast:fsr=off:fde=unused:gs=on:gsem=off:nm=0:nwc=1:sd=1:ss=axioms:st=5.0:sos=all:spl=off:sp=occurrence:updr=off:uhcvi=on_41");

} // fillSchedule



/**
 * This function solves a single problem. It makes the following steps:
 * <ol><li>find the main and the fallback schedules depending on the problem
 *          properties</li>
 *     <li>run the main schedule using runSchedule()</li>
 *     <li>if the proof is not found, checks if all the remaining time
 *         was used: if not, it runs the fallback strategy using
 *         runSchedule() with the updated time limit</li></ol>
 * Once the problem is proved, the runSchedule() function does not return
 * and the process terminates.
 *
 * If a slice contains sine_selection value different from off, theory axioms
 * will be selected using SInE from the common axioms included in the batch file
 * (all problem axioms, including the included ones, will be used as a base
 * for this selection).
 *
 * If the sine_selection is off, all the common axioms will be just added to the
 * problem axioms. All this is done in the @b runSlice(Options&) function.
 * @param terminationTime the time in milliseconds since the prover starts when
 *        the strategy should terminate
 * @param timeLimit in milliseconds
 * @author Krystof Hoder
 * @since 04/06/2013 flight Frankfurt-Vienna, updated for CASC-J6
 * @author Andrei Voronkov
 */
void CLTBProblem::performStrategy(int terminationTime,int timeLimit, const Category category, Shell::Property* property)
{
  CALL("CLTBProblem::performStrategy");
  cout << "% Hi Geoff, go and have some cold beer while I am trying to solve this very hard problem!\n";

  Schedule quick;
  Schedule fallback;

    fillSchedule(quick,property);
    CASC::CASCMode::getSchedules(*property,fallback,fallback);
    
  StrategySet usedSlices;
  if (runSchedule(quick,usedSlices,false,terminationTime)) {
    return;
  }
  if (env.timer->elapsedMilliseconds() >= terminationTime) {
    return;
  }
  runSchedule(fallback,usedSlices,true,terminationTime);
} // CLTBProblem::performStrategy

/**
 * This function solves a single problem. It parses the problem, spawns a
 * writer process for output and creates a pipe to communicate with it.
 * Then it calls performStrategy(terminationTime) that performs the
 * actual proof search.
 * @param terminationTime the time in milliseconds since the prover start
 * @param timeLimit time limit in milliseconds
 * @since 04/06/2013 flight Manchester-Frankfurt
 * @author Andrei Voronkov
 */
void CLTBProblem::searchForProof(int terminationTime,int timeLimit,const Category category)
{
  CALL("CLTBProblem::searchForProof");

  System::registerForSIGHUPOnParentDeath();

  env.timer->makeChildrenIncluded();
  TimeCounter::reinitialize();

  env.options->setInputFile(problemFile);

  Stack<unsigned> cutoffs;
  if (env.options->ltbLearning() != Options::LTBLearning::OFF){
    env.clausePriorities = new DHMap<const Unit*,unsigned>();

    if (parent->_biasedLearning){
      unsigned cutoff = parent->_learnedFormulasMaxCount/2;
      while (cutoff>0){
        cutoffs.push(cutoff);
        //cout << "create cutoff " << cutoff << endl;
        cutoff /= 2;
      }

      env.maxClausePriority = cutoffs.length();
    }
  }

  // this local scope will delete a potentially large parser
  {
    TimeCounter tc(TC_PARSING);
    env.statistics->phase=Statistics::PARSING;

    // Ensure the parser is recording axiom names
    bool outputAxiomValue = env.options->outputAxiomNames();
    env.options->setOutputAxiomNames(true);

    ifstream inp(problemFile.c_str());
    if (inp.fail()) {
      USER_ERROR("Cannot open problem file: " + problemFile);
    }
    Parse::TPTP parser(inp);
    List<vstring>::Iterator iit(parent->_theoryIncludes);
    while (iit.hasNext()) {
      parser.addForbiddenInclude(iit.next());
    }
    parser.parse();
    UnitList* probUnits = parser.units();
    UIHelper::setConjecturePresence(parser.containsConjecture());
    prb.addUnits(probUnits);

    // Now we iterate over all units in the problem and populate
    // clausePriorities from learnedFormulas
    if (env.options->ltbLearning() != Options::LTBLearning::OFF){
      unsigned learnedAdded = 0;
      UnitList::Iterator uit(prb.units());
      while (uit.hasNext()){
        Unit* u = uit.next();
        if (u->inputType()!=Unit::AXIOM) continue;
        vstring name;
        if (Parse::TPTP::findAxiomName(u,name)){
          if (parent->_learnedFormulas.contains(name)){
            learnedAdded++;
            unsigned priority = 1;
            if (parent->_biasedLearning){
              ASS(parent->_learnedFormulasCount.find(name));
              unsigned count = parent->_learnedFormulasCount.get(name);
              for(;;priority++){
                if (cutoffs[priority-1] <= count) break;
              }
            }
            env.clausePriorities->insert(u,priority);
            //cout << "insert " << name << " with " << priority << endl;
          }
        }
        else{ 
          ASSERTION_VIOLATION; 
        }
      }
      cout << "Marked " << learnedAdded << " as learned formulas" << endl;
    }
    env.options->setOutputAxiomNames(outputAxiomValue);
  }

  Shell::Property* property = prb.getProperty();
  if (property->atoms()<=1000000) {
    TimeCounter tc(TC_PREPROCESSING);
    env.statistics->phase=Statistics::NORMALIZATION;
    Normalisation norm;
    norm.normalise(prb);
  }

  env.statistics->phase=Statistics::UNKNOWN_PHASE;

  // now all the cpu usage will be in children, we'll just be waiting for them
  Timer::setTimeLimitEnforcement(false);

  //UIHelper::szsOutput=true;

  performStrategy(terminationTime,timeLimit,category,property);
  exitOnNoSuccess();
  ASSERTION_VIOLATION; // the exitOnNoSuccess() function should never return
} // CLTBProblem::perform

/**
 * This function exits the problem master process if the problem
 * was not solved
 *
 * The unsuccessful problem master process does not have to
 * necessarily call this function to exit.
 */
void CLTBProblem::exitOnNoSuccess()
{
  CALL("CLTBProblem::exitOnNoSuccess");

  env.beginOutput();
  CLTBMode::lineOutput() << "Proof not found in time " << Timer::msToSecondsString(env.timer->elapsedMilliseconds()) << endl;
  if (env.remainingTime()/100>0) {
    CLTBMode::lineOutput() << "SZS status GaveUp for " << env.options->problemName() << endl;
  }
  else {
    //From time to time we may also be terminating in the timeLimitReached()
    //function in Lib/Timer.cpp in case the time runs out. We, however, output
    //the same string there as well.
    CLTBMode::lineOutput() << "SZS status Timeout for " << env.options->problemName() << endl;
  }
  env.endOutput();

  CLTBMode::coutLineOutput() << "problem proof search terminated (fail)" << endl << flush;
  System::terminateImmediately(1); //we didn't find the proof, so we return nonzero status code
} // CLTBProblem::exitOnNoSuccess

static unsigned milliToDeci(unsigned timeInMiliseconds) {
  return timeInMiliseconds/100;
}

/**
 * Run a schedule. Terminate the process with 0 exit status
 * if a proof was found, otherwise return false. This function available cores:
 * If the total number of cores @b n is 8 or more, then @b n-2, otherwise @b n-1.
 * It spawns processes by calling runSlice()
 * @author Andrei Voronkov
 * @since 04/06/2013 flight Frankfurt-Vienna, updated for CASC-J6
 */
bool CLTBProblem::runSchedule(Schedule& schedule,StrategySet& used,bool fallback,int terminationTime)
{
  CALL("CLTBProblem::runSchedule");

  // compute the number of parallel processes depending on the
  // number of available cores
  int parallelProcesses;
  unsigned coreNumber = System::getNumberOfCores();
  if (coreNumber <= 1) {
    parallelProcesses = 1;
  }
  else if (coreNumber>=8) {
    parallelProcesses = coreNumber-2;
  }
  else {
    parallelProcesses = coreNumber;
  }

  int processesLeft = parallelProcesses;
  Schedule::BottomFirstIterator it(schedule);
 
  int slices = schedule.length();
  while (it.hasNext()) {
    while (processesLeft) {
      CLTBMode::coutLineOutput() << "Slices left: " << slices-- << endl;
      CLTBMode::coutLineOutput() << "Processes available: " << processesLeft << endl << flush;
      ASS_G(processesLeft,0);

      int elapsedTime = env.timer->elapsedMilliseconds();
      if (elapsedTime >= terminationTime) {
	// time limit reached
        goto finish_up;
      }

      vstring sliceCode = it.next();
      vstring chopped;

      // slice time in milliseconds
      int sliceTime = SLOWNESS * getSliceTime(sliceCode,chopped);
      if (used.contains(chopped)) {
	// this slice was already used
	continue;
      }
      used.insert(chopped);
      int remainingTime = terminationTime - elapsedTime;
      if (sliceTime > remainingTime) {
	sliceTime = remainingTime;
      }

      ASS_GE(sliceTime,0);
      if (milliToDeci((unsigned)sliceTime) == 0) {
        // can be still zero, due to rounding
        // and zero time limit means no time limit -> the child might never return!

        // time limit reached
        goto finish_up;
      }

      pid_t childId=Multiprocessing::instance()->fork();
      ASS_NEQ(childId,-1);
      if (!childId) {
        //we're in a proving child
        try {
          runSlice(sliceCode,sliceTime); //start proving
        } catch (Exception& exc) {
          cerr << "% Exception at run slice level" << endl;
          exc.cry(cerr);
          System::terminateImmediately(1); //we didn't find the proof, so we return nonzero status code
        }
        ASSERTION_VIOLATION; //the runSlice function should never return
      }
      Timer::syncClock();
      ASS(childIds.insert(childId));
      CLTBMode::coutLineOutput() << "slice pid "<< childId << " slice: " << sliceCode
				 << " time: " << (sliceTime/100)/10.0 << endl << flush;
      processesLeft--;
      if (!it.hasNext()) {
	break;
      }
    }

    CLTBMode::coutLineOutput() << "No processes available: " << endl << flush;
    if (processesLeft==0) {
      waitForChildAndExitWhenProofFound();
      // proof search failed
      processesLeft++;
    }
  }

  finish_up:

  while (parallelProcesses!=processesLeft) {
    ASS_L(processesLeft, parallelProcesses);
    waitForChildAndExitWhenProofFound();
    // proof search failed
    processesLeft++;
    Timer::syncClock();
  }
  return false;
} // CLTBProblem::runSchedule

/**
 * Wait for termination of a child and terminate the process with a zero status
 * if a proof was found. If the child didn't find the proof, just return.
 */
void CLTBProblem::waitForChildAndExitWhenProofFound()
{
  CALL("CLTBProblem::waitForChildAndExitWhenProofFound");
  ASS(!childIds.isEmpty());

  int resValue;
  pid_t finishedChild = Multiprocessing::instance()->waitForChildTermination(resValue);
#if VDEBUG
  ALWAYS(childIds.remove(finishedChild));
#endif
  if (!resValue) {
    // we have found the proof. It has been already written down by the writter child,
    // so we can just terminate
    CLTBMode::coutLineOutput() << "terminated slice pid " << finishedChild << " (success)" << endl << flush;
    System::terminateImmediately(0);
  }
  // proof not found
  CLTBMode::coutLineOutput() << "terminated slice pid " << finishedChild << " (fail)" << endl << flush;
} // waitForChildAndExitWhenProofFound

ofstream* CLTBProblem::writerFileStream = 0;

void CLTBProblem::terminatingSignalHandler(int sigNum)
{
  try {
    if (writerFileStream) {
      writerFileStream->close();
    }
  } catch (Lib::SystemFailException& ex) {
    cerr << "Process " << getpid() << " received SystemFailException in terminatingSignalHandler" << endl;
    ex.cry(cerr);
    cerr << " and will now die" << endl;
  }
  System::terminateImmediately(0);
}

/**
 * Run a slice given by its code using the specified time limit.
 * @since 04/06/2013 flight Frankfurt-Vienna
 * @author Andrei Voronkov
 */
void CLTBProblem::runSlice(vstring sliceCode, unsigned timeLimitInMilliseconds)
{
  CALL("CLTBProblem::runSlice");

  Options opt = *env.options;
  opt.readFromEncodedOptions(sliceCode);
  opt.setTimeLimitInDeciseconds(milliToDeci(timeLimitInMilliseconds));
  int stl = opt.simulatedTimeLimit();
  if (stl) {
    opt.setSimulatedTimeLimit(int(stl * SLOWNESS));
  }
  runSlice(opt);
} // runSlice

/**
 * Run a slice given by its options
 * @since 04/06/2013 flight Frankfurt-Vienna
 * @author Andrei Voronkov
 */
void CLTBProblem::runSlice(Options& strategyOpt)
{
  CALL("CLTBProblem::runSlice(Option&)");

  System::registerForSIGHUPOnParentDeath();
  UIHelper::cascModeChild=true;

  int resultValue=1;
  env.timer->reset();
  env.timer->start();
  TimeCounter::reinitialize();
  Timer::setTimeLimitEnforcement(true);

  Options opt = strategyOpt;
  //we have already performed the normalization
  opt.setNormalize(false);
  opt.setForcedOptionValues();
  opt.checkGlobalOptionConstraints();
  opt.setProblemName(problemFile);
  *env.options = opt; //just temporarily until we get rid of dependencies on env.options in solving

//  if (env.options->sineSelection()!=Options::SS_OFF) {
//    //add selected axioms from the theory
//    parent->theorySelector.perform(probUnits);
//
//    env.options->setSineSelection(Options::SS_OFF);
//    env.options->forceIncompleteness();
//  }
//  else {
//    //if there wasn't any sine selection, just put in all theory axioms
//    probUnits=UnitList::concat(probUnits, parent->theoryAxioms);
//  }

  env.beginOutput();
  CLTBMode::lineOutput() << opt.testId() << " on " << opt.problemName() << endl;
  env.endOutput();

  ProvingHelper::runVampire(prb, opt);

  //set return value to zero if we were successful
  if (env.statistics->terminationReason == Statistics::REFUTATION) {
    resultValue=0;
  }

  System::ignoreSIGHUP(); // don't interrupt now, we need to finish printing the proof !

  if (!resultValue) { // write the proof to a file
    ScopedSemaphoreLocker locker(_syncSemaphore);
    locker.lock();
    ofstream out(outFile.c_str());
    UIHelper::outputResult(out);
    out.close();
  } else { // write other result to output
    env.beginOutput();
    UIHelper::outputResult(env.out());
    env.endOutput();
  }

  exit(resultValue);
} // CLTBProblem::runSlice

/**
 * Return the intended slice time in milliseconds and assign the slice
 * vstring with chopped time limit to @b chopped.
 * @since 04/06/2013 flight Frankfurt-Vienna
 * @author Andrei Voronkov
 */
unsigned CLTBProblem::getSliceTime(vstring sliceCode,vstring& chopped)
{
  CALL("CASCMode::getSliceTime");

  unsigned pos = sliceCode.find_last_of('_');
  vstring sliceTimeStr = sliceCode.substr(pos+1);
  chopped.assign(sliceCode.substr(0,pos));
  unsigned sliceTime;
  ALWAYS(Int::stringToUnsignedInt(sliceTimeStr,sliceTime));
  ASS_G(sliceTime,0); //strategies with zero time don't make sense

  unsigned time = sliceTime + 1;
  if (time < 10) {
    time++;
  }
  // convert deciseconds to milliseconds
  return time * 100;
} // getSliceTime

/**
 * Start line output by writing the TPTP comment sign and the current
 * elapsed time in milliseconds to env.out(). Returns env.out()
 * @since 05/06/2013 Vienna
 * @author Andrei Voronkov
 */
ostream& CLTBMode::lineOutput()
{
  CALL("CLTBMode::lineOutput");
  return env.out() << "% (" << getpid() << ',' << (env.timer->elapsedMilliseconds()/100)/10.0 << ") ";
} // CLTBMode::lineOutput

/**
 * Start line output by writing the TPTP comment sign and the current
 * elapsed time in milliseconds to cout. Returns cout
 * @since 05/06/2013 Vienna
 * @author Andrei Voronkov
 */
ostream& CLTBMode::coutLineOutput()
{
  CALL("CLTBMode::lineOutput");
  return cout << "% (" << getpid() << ',' << (env.timer->elapsedMilliseconds()/100)/10.0 << ") ";
} // CLTBMode::coutLineOutput

#endif //!COMPILER_MSVC
