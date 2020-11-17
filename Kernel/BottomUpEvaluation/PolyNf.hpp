#ifndef __BOTTOM_UP_EVALUATION__POLY_NF_HPP__
#define __BOTTOM_UP_EVALUATION__POLY_NF_HPP__

#include "Kernel/BottomUpEvaluation.hpp"

namespace Lib {

POLYMORPHIC_FUNCTION(bool    , hasNext  , const& t,) { return t.hasNext();   }
POLYMORPHIC_FUNCTION(Kernel::PolyNf  , next     ,      & t,) { return t.next();      }
POLYMORPHIC_FUNCTION(unsigned, nChildren, const& t,) { return t.nChildren(); }
POLYMORPHIC_FUNCTION(Kernel::PolyNf  , self     , const& t,) { return Kernel::PolyNf(t._self);       }

template<>
struct BottomUpChildIter<Kernel::PolyNf>
{
  struct PolynomialBottomUpChildIter 
  {
    Kernel::AnyPoly _self;
    unsigned _idx1;
    unsigned _idx2;
    unsigned _nChildren;

    PolynomialBottomUpChildIter(Kernel::AnyPoly self) : _self(self), _idx1(0), _idx2(0), _nChildren(0)
    {
      while (_idx1 < _self.nSummands() && _self.nFactors(_idx1) == 0) {
        _idx1++;
      }
      for (unsigned i = 0; i < _self.nSummands(); i++) {
        _nChildren += self.nFactors(i);
      }
    }

    bool hasNext() const
    { return _idx1 < _self.nSummands(); }

    Kernel::PolyNf next() 
    { 
      auto out = _self.termAt(_idx1, _idx2++);
      if (_idx2 >= _self.nFactors(_idx1)) {
        _idx1++;
        while (_idx1 < _self.nSummands() && _self.nFactors(_idx1) == 0) {
          _idx1++;
        }
        _idx2 = 0;
      }
      return out;
    }

    unsigned nChildren() const
    { return _nChildren; }

    friend ostream& operator<<(ostream& out, PolynomialBottomUpChildIter const& self) 
    { return out << self._self << "@(" << self._idx1 << ", " << self._idx2 << ")"; }
  };

  struct FuncTermBottomUpChildIter 
  {

    Perfect<Kernel::FuncTerm> _self;
    unsigned _idx;

    FuncTermBottomUpChildIter(Perfect<Kernel::FuncTerm> self) : _self(self), _idx(0) {}

    bool hasNext() const
    { return _idx < _self->arity(); }

    Kernel::PolyNf next() 
    { return _self->arg(_idx++); }

    unsigned nChildren() const
    { return _self->arity(); }

    friend ostream& operator<<(ostream& out, FuncTermBottomUpChildIter const& self) 
    { return out << self._self << "@" << self._idx; }
  };


  struct VariableBottomUpChildIter 
  {
    Kernel::Variable _self;
    VariableBottomUpChildIter(Kernel::Variable self) : _self(self) {}

    bool hasNext() const
    { return false; }

    Kernel::PolyNf next() 
    { ASSERTION_VIOLATION }

    unsigned nChildren() const
    { return 0; }

    friend ostream& operator<<(ostream& out, VariableBottomUpChildIter const& self) 
    { return out << self._self; }
  };

  using Inner = Coproduct<FuncTermBottomUpChildIter, VariableBottomUpChildIter, PolynomialBottomUpChildIter>;
  Inner _self;

  BottomUpChildIter(Kernel::PolyNf self) : _self(self.match(
        [&](Perfect<Kernel::FuncTerm> self) { return Inner(FuncTermBottomUpChildIter( self ));            },
        [&](Kernel::Variable                  self) { return Inner(VariableBottomUpChildIter( self ));            },
        [&](Kernel::AnyPoly           self) { return Inner(PolynomialBottomUpChildIter(std::move(self))); }
      ))
  {}

  Kernel::PolyNf next() 
  { ASS(hasNext()); return _self.apply(Polymorphic::next{}); }

  bool hasNext() const 
  { return _self.apply(Polymorphic::hasNext{}); }

  unsigned nChildren() const 
  { return _self.apply(Polymorphic::nChildren{}); }

  Kernel::PolyNf self() const 
  { return _self.apply(Polymorphic::self{}); }

  friend ostream& operator<<(ostream& out, BottomUpChildIter const& self) 
  { return out << self._self; }
};

} // namespace Lib

#endif//__BOTTOM_UP_EVALUATION__POLY_NF_HPP__
