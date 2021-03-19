
  /*
   * File SimplificationTester.hpp.
   *
   * This file is part of the source code of the software program
   * Vampire. It is protected by applicable
   * copyright laws.
   *
   * This source code is distributed under the licence found here
   * https://vprover.github.io/license.html
   * and in the source directory
   */

#ifndef __TEST__SIMPLIFICATION_TESTER_HPP__
#define __TEST__SIMPLIFICATION_TESTER_HPP__

/**
 * This file provides macros and classes used to write nice tests for simplification rules.
 *
 * Check out UnitTests/tGaussianElimination.cpp, to see how it is to be used.
 */

#include "Test/TestUtils.hpp"
#include "Test/ClausePattern.hpp"
#include "Kernel/Clause.hpp"
#include "Lib/Coproduct.hpp"

namespace Test {

namespace Simplification {

class SimplificationTester
{
public:
  virtual Kernel::Clause* simplify(Kernel::Clause*) const = 0;

  virtual bool eq(Kernel::Clause const* lhs, Kernel::Clause const* rhs) const 
  { return TestUtils::eqModAC(lhs, rhs); }
};

class Success
{
  Kernel::Clause* _input;
  Option<ClausePattern> _expected;

public:
  Success() {}

  Success input(Kernel::Clause* x) 
  {
    _input = x;
    return *this;
  }

  Success expected(ClausePattern x)
  {
    _expected = Option<ClausePattern>(x); 
    return *this;
  }

  void run(const SimplificationTester& simpl) {
    auto res = simpl.simplify(_input);

    if (!res) {
      cout  << endl;
      cout << "[     case ]: " << pretty(*_input) << endl;
      cout << "[       is ]: NULL (indicates the clause is a tautology)" << endl;
      cout << "[ expected ]: " << pretty(_expected) << endl;
      exit(-1);

    } else if (!_expected.unwrap().matches(simpl, res)) {
      cout  << endl;
      cout << "[     case ]: " << pretty(*_input) << endl;
      cout << "[       is ]: " << pretty(*res) << endl;
      cout << "[ expected ]: " << pretty(_expected) << endl;
      exit(-1);

    }
  }
};


class NotApplicable
{
  Kernel::Clause* _input;
public:
  NotApplicable() {}

  NotApplicable input(Kernel::Clause* x) 
  {
    _input = x;
    return *this;
  }


  void run(const SimplificationTester& simpl) {
    auto res = simpl.simplify(_input);
    if (res != _input ) {
      cout  << endl;
      cout << "[     case ]: " << pretty(*_input) << endl;
      cout << "[       is ]: " << pretty(*res) << endl;
      cout << "[ expected ]: < nop >" << endl;
      exit(-1);
    }
  }
};

#define REGISTER_SIMPL_TESTER(t) using SimplTester = t;

#define TEST_SIMPLIFY(name, ...)                                                                                        \
        TEST_SIMPLIFY_WITH_SUGAR(name, MY_SYNTAX_SUGAR, __VA_ARGS__) 

#define TEST_SIMPLIFY_WITH_SUGAR(name, syntax_sugar, ...)                                                               \
  TEST_FUN(name) {                                                                                                      \
    SimplTester simpl;                                                                                                  \
    _Pragma("GCC diagnostic push")                                                                                      \
    _Pragma("GCC diagnostic ignored \"-Wunused\"")                                                                      \
      syntax_sugar                                                                                                      \
    _Pragma("GCC diagnostic pop")                                                                                       \
    __VA_ARGS__.run(simpl);                                                                                             \
  }                                                                                                                     \

} // namespace Simplification

} // namespace Test

#endif // __TEST__SIMPLIFICATION_TESTER_HPP__
