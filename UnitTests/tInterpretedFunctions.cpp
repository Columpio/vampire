
/*
 * File tInterpretedFunctions.cpp.
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

#include "Forwards.hpp"
#include "Lib/Environment.hpp"

#include "Indexing/TermSharing.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/Sorts.hpp"

#include "Kernel/InterpretedLiteralEvaluator.hpp"

#include "Test/UnitTesting.hpp"
#include "Test/SyntaxSugar.hpp"

#define UNIT_ID interpFunc
UT_CREATE;

using namespace std;
using namespace Lib;
using namespace Kernel;
using namespace Shell;

#define TEST_FAIL exit(-1);
#define OUT cout
// #define TEST_FAIL OUT << "FAIL" << endl;

namespace __Dumper {
  template<class... As>
  struct Dumper {
    static void dump(As... as);
  };

  template<>
  struct Dumper<> {
    static void dump() { }
  };

  template<class A, class... As>
  struct Dumper<A, As...> {
    static void dump(A a, As... as) {
      OUT << a;
      Dumper<As...>::dump(as...);
    }
  };
}

template<class... As>
void dump_all(As... as) {
  __Dumper::Dumper<As...>::dump(as...);
}

template<class... As>
void check(bool b, const char* msg, As... vs) {
  if (!b) {
    // OUT << endl;
    // OUT << msg << ": ";
    // dump_all(vs...);
    // OUT << endl;
    TEST_FAIL
  }
}

#define __CHECK(op, is, expected, msg, test_case) \
  if (!(( is ) op ( expected ))) { \
    OUT << endl; \
    OUT << msg << endl; \
    OUT << "[   case   ] " << test_case << endl; \
    OUT << "[    is    ] " << #is << " = " << is << endl; \
    OUT << "[ expected ] " << #is << " " #op << " " << expected << endl; \
    OUT << endl; \
    TEST_FAIL \
  } \

#define CHECK_NE(...) \
  __CHECK(!=, __VA_ARGS__)

#define CHECK_EQ(...) \
  __CHECK(==, __VA_ARGS__)

void check_no_succ(Literal& orig) {

  auto eval = InterpretedLiteralEvaluator();

  bool constant;
  Literal* result = NULL;
  bool constantTrue;

  auto sideConditions = Stack<Literal*>();
  Literal* src = Literal::create(&orig, orig.polarity());
  auto success = eval.evaluate(src,constant,result,constantTrue, sideConditions);

  CHECK_EQ(success, false, "unexpectedly evaluation was successful", orig.toString());
}


void check_eval(Literal& orig, bool expected) {

  auto eval = InterpretedLiteralEvaluator();

  bool constant;
  Literal* result = NULL;
  bool constantTrue;

  auto sideConditions = Stack<Literal*>();
  Literal* src = Literal::create(&orig, orig.polarity());
  auto success = eval.evaluate(src,constant,result,constantTrue, sideConditions);

  CHECK_EQ(success, true, "evaluation failed", orig.toString());
  CHECK_EQ(sideConditions.isEmpty(), true, "non-empty side condictions", orig.toString());
  CHECK_NE(result, NULL, "result not set", orig.toString());
  CHECK_EQ(constant, true, "result not evaluated to constant", orig.toString());
  CHECK_EQ(constantTrue, expected, "result not evaluated to constant", orig.toString());
}

bool operator==(const Literal& lhs, const Literal& rhs) {
  return Indexing::TermSharing::equals(&lhs, &rhs);
}

void check_eval(Literal& orig, const Literal& expected) {
  auto eval = InterpretedLiteralEvaluator();

  bool constant;
  Literal* result = nullptr;
  bool constantTrue;

  auto sideConditions = Stack<Literal*>();
  auto success = eval.evaluate(&orig,constant,result,constantTrue, sideConditions);

  CHECK_EQ(success, true, "evaluation failed", orig.toString());
  CHECK_EQ(sideConditions.isEmpty(), true, "non-empty side condictions", orig.toString());
  CHECK_NE(result, NULL, "result not set", orig.toString());
  CHECK_EQ(*result, expected, "unexpected evaluation result", orig.toString());
}

#define ADDITIONAL_FUNCTIONS \
      _Pragma("GCC diagnostic push") \
      _Pragma("GCC diagnostic ignored \"-Wunused\"") \
        THEORY_SYNTAX_SUGAR_FUN(f, 1) \
      _Pragma("GCC diagnostic pop") \

/** Tests for evalutions that should only be successful for reals/rationals and not for integers. */
#define FRACTIONAL_TEST(name, formula, expected) \
    TEST_FUN(name ## _ ## INT) { \
      THEORY_SYNTAX_SUGAR(INT); \
      ADDITIONAL_FUNCTIONS \
      check_no_succ(( formula )); \
    }\
    TEST_FUN(name ## _ ## REAL) { \
      THEORY_SYNTAX_SUGAR(REAL); \
      ADDITIONAL_FUNCTIONS \
      check_eval(( formula ), ( expected )); \
    }\
    TEST_FUN(name ## _ ## RAT) { \
      THEORY_SYNTAX_SUGAR(RAT); \
      ADDITIONAL_FUNCTIONS \
      check_eval(( formula ), ( expected )); \
    } \

#define ALL_NUMBERS_TEST(name, formula, expected) \
    TEST_FUN(name ## _ ## INT) { \
      THEORY_SYNTAX_SUGAR(INT); \
      ADDITIONAL_FUNCTIONS \
      check_eval(( formula ), ( expected )); \
    } \
    TEST_FUN(name ## _ ## REAL) { \
      THEORY_SYNTAX_SUGAR(REAL); \
      ADDITIONAL_FUNCTIONS \
      check_eval(( formula ), ( expected )); \
    } \
    TEST_FUN(name ## _ ## RAT) { \
      THEORY_SYNTAX_SUGAR(RAT); \
      ADDITIONAL_FUNCTIONS \
      check_eval(( formula ), ( expected )); \
    } \

//TODO continue here
TEST_FUN(partial_eval_add_1) { 
  THEORY_SYNTAX_SUGAR(INT)
  check_eval(
      eq(add(2, add(x, add(3, 7))), y),
      eq(add(12, x), y)
    );
}

TEST_FUN(partial_eval_add_2) { 
  THEORY_SYNTAX_SUGAR(INT)
  check_eval(
      eq(add(2, add(add(8, x), add(3, 7))), y),
      eq(add(20, x), y)
    );
}

TEST_FUN(partial_eval_add_3) { 
  THEORY_SYNTAX_SUGAR(INT)
  check_eval(
      eq(add(2, add(add(minus(8), x), add(3, 7))), y),
      eq(add(4, x), y)
    );
}

TEST_FUN(partial_eval_add_4) { 
  THEORY_SYNTAX_SUGAR(INT)
  check_eval(
      eq(minus(add(2, add(add(8, x), add(3, 7)))), y),
      eq(add(-20, minus(x)), y)
    );
}

#if 0 // NOT (YET) SUPPORTED

TEST_FUN(partial_eval_add_mul_1) { 
  THEORY_SYNTAX_SUGAR(INT)
    /* -21 + 7 * (3 + x) = y */
  check_eval(
      eq(x, add(-21, mul(7, add(3,y)))),
      eq(x, mul(7,y))
    );
}

TEST_FUN(partial_eval_add_mul_2) { 
  THEORY_SYNTAX_SUGAR(INT)
  check_eval(
      eq(mul(7,x), add(-21, mul(7, add(3,x)))),
      true
    );
}

#endif

ALL_NUMBERS_TEST(simpl_times_zero_0
    , eq(a, mul(0, y))
    , eq(a, 0)
    );


ALL_NUMBERS_TEST(simpl_times_zero_1
    , eq(x, mul(0, y))
    , eq(x, 0)
    );

ALL_NUMBERS_TEST(simpl_times_zero_2
    , eq(3, add(mul(0, x), 4))
    , false
    );

TEST_FUN(literal_to_const_1) {
  THEORY_SYNTAX_SUGAR(REAL)
  // Interpret 2.5*2=5
  check_eval(
      eq(mul(frac(5,2), 2), 5),
      true 
    );
}

TEST_FUN(literal_to_const_2) {
  THEORY_SYNTAX_SUGAR(REAL)
  check_eval(
      eq(mul(frac(5,2), 2), 6),
      false 
    );
}

TEST_FUN(literal_to_const_3) {
  THEORY_SYNTAX_SUGAR(INT)

  // Interpret 3*2 < 5
  check_eval(
      lt(mul(3,2),5),
      false
    );

  // Interpret 3*2 < 5
  check_eval(
      neg(lt(mul(3,2),5)),
      true
    );

}

TEST_FUN(literal_to_const_4) {
  THEORY_SYNTAX_SUGAR(REAL)

  // Interpret 3*2 > 5
  check_eval(
      gt(mul(3,2),5),
      true
    );

}

TEST_FUN(literal_to_const_5) {
  THEORY_SYNTAX_SUGAR(REAL)
  // Interpret 3*2 > 13
  check_eval(
      gt(mul(3,2),13),
      false
    );
}

TEST_FUN(literal_to_const_6) {
  THEORY_SYNTAX_SUGAR(INT)
  check_eval(
      lt(0, 0),
      false
    );  
  check_eval(
      neg(lt(0, 0)),
      true
    );
}

#ifdef TEST_EVAL


TEST_FUN(literal_to_const_7) { 
  THEORY_SYNTAX_SUGAR(REAL)
  // Interpret 13*a > 13*a
  check_eval(
      gt(add(mul(3,a), x),add(mul(3, a), x)),
      false
    );
}

TEST_FUN(literal_to_const_8) {
  THEORY_SYNTAX_SUGAR(REAL)

  // Interpret 3*a > 13*a
  check_eval(
      gt(mul(3,a),mul(13, a)),
      false
    );
}

TEST_FUN(literal_to_const_9) {
  THEORY_SYNTAX_SUGAR(REAL)

  // Interpret 18*a > 13*a
  check_eval(
      gt(mul(18,a),mul(13, a)),
      true
    );
}

// Interpret 5.0 = 2.0 * y(5.0)
TEST_FUN(rebalance_uninterpreted) {
  THEORY_SYNTAX_SUGAR(REAL)

  check_eval(
      eq(5, mul(2,f(5))),
      eq(f(5), frac(5,2))
    );

}

// Interpret x = -x
TEST_FUN(minus_x_eq_x) {
  THEORY_SYNTAX_SUGAR(REAL)

  check_eval(
      eq(x, minus(x)),
      eq(x, 0)
    );
}

TEST_FUN(minus_x_neq_x) {
  THEORY_SYNTAX_SUGAR(REAL)

  check_eval(
      neq(x, minus(x)),
      neq(x, 0)
    );

};

// Interpret k*x = 0
TEST_FUN(k_x_eq_0) {
  THEORY_SYNTAX_SUGAR(REAL)

  check_eval(
      eq(mul(5,x), 0),
      eq(x, 0)
    );

  check_eval(
      eq(mul(5,a), 0),
      eq(a, 0)
    );

};

#endif

TEST_FUN(normalize_less_1) {
  THEORY_SYNTAX_SUGAR(INT)
  check_eval(
      /* 5 < 2 * x */
      lt(5, mul(2,x)),
      /* 0 < 2 * x - 5 */
      lt(0, add(-5, mul(2,x)))
    );
}

TEST_FUN(normalize_less_2) {
  THEORY_SYNTAX_SUGAR(INT)
  check_eval(
      /* 5 < a * x */
      lt(5, mul(a,x)),
      /* 0 < a * x - 5 */
      lt(0, add(-5, mul(a,x)))
    );
}

TEST_FUN(normalize_less_3) {
  THEORY_SYNTAX_SUGAR(INT)
  check_eval(
      /* b < a * x */
      lt(b, mul(a,x)),
     /* 0 < a * x - b */
      lt(0, add(mul(a,x), minus(b)))
    );

}

TEST_FUN(normalize_less_4) {
  THEORY_SYNTAX_SUGAR(INT)
  check_eval(
      /* b < a */
      lt(b, a),
      /* 0 < a - b */
      lt(0, add(a, minus(b)))
    );
}


TEST_FUN(normalize_less_5) {
  THEORY_SYNTAX_SUGAR(INT)
  check_eval(
      /* b < a */
      lt(x,y),
      /* 0 < a - b */
      lt(0, add(y, minus(x)))
    );
}

TEST_FUN(normalize_less_equal_1) {
  THEORY_SYNTAX_SUGAR(INT)
  check_eval(
      /* ~(x < 5) */
      neg(lt(x, 5)),
      /* 0 <  x - 4 */
      lt(0, add(-4, x))
    );
}

TEST_FUN(normalize_less_equal_2) {
  THEORY_SYNTAX_SUGAR(INT)
    /* 0 <= x + 1*/
  check_eval(
      neg(lt(x, a)),
      /* !(x < a) 
       * <-> a <= x 
       * <-> a - 1 < x 
       * <-> 0 < x + 1 - a
       */
      lt(0, add(add(1, x), minus(a)))
      );
}

TEST_FUN(test_normalize_stable) {
  THEORY_SYNTAX_SUGAR(INT)
    /* 0 <= x + 1*/
  // check_eval(
  //     leq(0, add(x, 1)),
  //     leq(0, add(x, 1))
      // );
  check_no_succ(
      lt(0, add(1, x))
      );
}

#ifdef TEST_EVAL
TEST_FUN(x_eq_kx_1) {
  THEORY_SYNTAX_SUGAR(INT)
  check_eval(
      eq(x, mul(x, 3)),
      eq(0, x)
      );
}

TEST_FUN(x_eq_k_plus_x_1) {
  THEORY_SYNTAX_SUGAR(INT)
  check_eval(
      eq(x, add(x, y)),
      eq(y, 0)
      );
}


TEST_FUN(x_eq_k_plus_x_2) {
  THEORY_SYNTAX_SUGAR(INT)
  check_eval(
      eq(x, add(x, 1)),
      false
      );
}

TEST_FUN(k_eq_x_plus_x_1) {
  THEORY_SYNTAX_SUGAR(INT)
  check_eval(
      eq(mul(2, a), add(x, x)),
      eq(a, x)
      );
}

// Interpret -x > x
TEST_FUN(x_gt_minus_x) {
  THEORY_SYNTAX_SUGAR(REAL)

  check_eval(
      gt(x, minus(x)),
      gt(x, 0)
    );

  check_eval(
      gt(minus(x), x),
      gt(0, x)
    );
};


#endif


// x = -(-x)
TEST_FUN(eval_double_minus_1) {
  THEORY_SYNTAX_SUGAR(INT)

  check_eval(
      eq(x, minus(minus(x))),
      true);
  check_eval(
      neg(eq(x, minus(minus(x)))),
      false);
};

// x < -(-x)
TEST_FUN(eval_double_minus_2) {
  THEORY_SYNTAX_SUGAR(INT)
  check_eval(
      lt(x, minus(minus(x))),
      false);
  check_eval(
      neg(lt(x, minus(minus(x)))),
      true);
};

ALL_NUMBERS_TEST(eval_inverse_1 
    , eq(1, add(x, minus(x)))
    , false
    )

// a = -(-x)
TEST_FUN(eval_double_minus_3) {
  THEORY_SYNTAX_SUGAR(INT)
  check_eval(
      eq(a, minus(minus(x))),
      eq(a, x));
};


// 4 = -(-x + 4)
// ==> 4 = x + (-4)
TEST_FUN(eval_double_minus_4) {
  THEORY_SYNTAX_SUGAR(INT)
  check_eval(
      eq(4, minus(add(minus(x), 4))),
      eq(4, add(-4, x)) );
};

TEST_FUN(eval_remove_identity_1) {
  THEORY_SYNTAX_SUGAR(INT)
  check_eval(
      lt(0, add(0, minus(x))),
      lt(0, minus(x))
      );
};

TEST_FUN(eval_remove_identity_2) {
  THEORY_SYNTAX_SUGAR(INT)
      ADDITIONAL_FUNCTIONS \
  check_eval(
      eq(0, f(add(0, minus(mul(x, mul(1, y)))))),
      eq(0, f(minus(mul(x,y))))
      );
};


// TODO: cases x = k * x <-> k = 1 | x = 0 
// TODO: cases x = k + x <-> k = 0 
// TODO: cases x + x = k <->  = k/2
