/*********************                                                        */
/*! \file symbol_table.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Christopher L. Conway, Francois Bobot
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Convenience class for scoping variable and type declarations.
 **
 ** Convenience class for scoping variable and type declarations.
 **/

#include "cvc4_public.h"

#ifndef __CVC4__SYMBOL_TABLE_H
#define __CVC4__SYMBOL_TABLE_H

#include <memory>
#include <string>
#include <vector>

#include "base/exception.h"
#include "expr/expr.h"
#include "expr/type.h"

namespace CVC4 {

class CVC4_PUBLIC ScopeException : public Exception {};

/**
 * A convenience class for handling scoped declarations. Implements the usual
 * nested scoping rules for declarations, with separate bindings for expressions
 * and types.
 */
class CVC4_PUBLIC SymbolTable {
 public:
  /** Create a symbol table. */
  SymbolTable();
  ~SymbolTable();

  /**
   * Bind an expression to a name in the current scope level.  If
   * <code>name</code> is already bound to an expression in the current
   * level, then the binding is replaced. If <code>name</code> is bound
   * in a previous level, then the binding is "covered" by this one
   * until the current scope is popped. If levelZero is true the name
   * shouldn't be already bound.
   *
   * @param name an identifier
   * @param obj the expression to bind to <code>name</code>
   * @param levelZero set if the binding must be done at level 0
   */
  void bind(const std::string& name, Expr obj, bool levelZero = false) throw();

  /**
   * Bind a function body to a name in the current scope.  If
   * <code>name</code> is already bound to an expression in the current
   * level, then the binding is replaced. If <code>name</code> is bound
   * in a previous level, then the binding is "covered" by this one
   * until the current scope is popped.  Same as bind() but registers
   * this as a function (so that isBoundDefinedFunction() returns true).
   *
   * @param name an identifier
   * @param obj the expression to bind to <code>name</code>
   * @param levelZero set if the binding must be done at level 0
   */
  void bindDefinedFunction(const std::string& name, Expr obj,
                           bool levelZero = false) throw();

  /**
   * Bind a type to a name in the current scope.  If <code>name</code>
   * is already bound to a type in the current level, then the binding
   * is replaced. If <code>name</code> is bound in a previous level,
   * then the binding is "covered" by this one until the current scope
   * is popped.
   *
   * @param name an identifier
   * @param t the type to bind to <code>name</code>
   * @param levelZero set if the binding must be done at level 0
   */
  void bindType(const std::string& name, Type t,
                bool levelZero = false) throw();

  /**
   * Bind a type to a name in the current scope.  If <code>name</code>
   * is already bound to a type or type constructor in the current
   * level, then the binding is replaced. If <code>name</code> is
   * bound in a previous level, then the binding is "covered" by this
   * one until the current scope is popped.
   *
   * @param name an identifier
   * @param params the parameters to the type
   * @param t the type to bind to <code>name</code>
   * @param levelZero true to bind it globally (default is to bind it
   * locally within the current scope)
   */
  void bindType(const std::string& name, const std::vector<Type>& params,
                Type t, bool levelZero = false) throw();

  /**
   * Check whether a name is bound to an expression with either bind()
   * or bindDefinedFunction().
   *
   * @param name the identifier to check.
   * @returns true iff name is bound in the current scope.
   */
  bool isBound(const std::string& name) const throw();

  /**
   * Check whether a name was bound to a function with bindDefinedFunction().
   */
  bool isBoundDefinedFunction(const std::string& name) const throw();

  /**
   * Check whether an Expr was bound to a function (i.e., was the
   * second arg to bindDefinedFunction()).
   */
  bool isBoundDefinedFunction(Expr func) const throw();

  /**
   * Check whether a name is bound to a type (or type constructor).
   *
   * @param name the identifier to check.
   * @returns true iff name is bound to a type in the current scope.
   */
  bool isBoundType(const std::string& name) const throw();

  /**
   * Lookup a bound expression.
   *
   * @param name the identifier to lookup
   * @returns the expression bound to <code>name</code> in the current scope.
   */
  Expr lookup(const std::string& name) const throw();

  /**
   * Lookup a bound type.
   *
   * @param name the type identifier to lookup
   * @returns the type bound to <code>name</code> in the current scope.
   */
  Type lookupType(const std::string& name) const throw();

  /**
   * Lookup a bound parameterized type.
   *
   * @param name the type-constructor identifier to lookup
   * @param params the types to use to parameterize the type
   * @returns the type bound to <code>name(<i>params</i>)</code> in
   * the current scope.
   */
  Type lookupType(const std::string& name,
                  const std::vector<Type>& params) const throw();

  /**
   * Lookup the arity of a bound parameterized type.
   */
  size_t lookupArity(const std::string& name);

  /**
   * Pop a scope level. Deletes all bindings since the last call to
   * <code>pushScope</code>. Calls to <code>pushScope</code> and
   * <code>popScope</code> must be "properly nested." I.e., a call to
   * <code>popScope</code> is only legal if the number of prior calls to
   * <code>pushScope</code> on this <code>SymbolTable</code> is strictly
   * greater than then number of prior calls to <code>popScope</code>. */
  void popScope() throw(ScopeException);

  /** Push a scope level. */
  void pushScope() throw();

  /** Get the current level of this symbol table. */
  size_t getLevel() const throw();

  /** Reset everything. */
  void reset();

 private:
  // Copying and assignment have not yet been implemented.
  SymbolTable(const SymbolTable&);
  SymbolTable& operator=(SymbolTable&);

  class Implementation;
  std::unique_ptr<Implementation> d_implementation;
}; /* class SymbolTable */

}  // namespace CVC4

#endif /* __CVC4__SYMBOL_TABLE_H */
