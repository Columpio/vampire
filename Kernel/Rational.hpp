/*
 * Rational.hpp
 *
 *  Created on: Apr 15, 2013
 *      Author: ioan
 */

#ifndef RATIONAL_HPP_
#define RATIONAL_HPP_

#if GNUMP

#include "Forwards.hpp"

#include "Lib/Exception.hpp"
#include "Lib/Int.hpp"

#include <cmath>

namespace Kernel{

namespace __Aux_Number{

/**
 * Class designed in order to represent rational numbers. This should be used as
 * an alternative to the NativeNumber (long double) representation of numbers for
 * bound propagation.
 *
 * Some conventions about this class:
 * 	- the number is negative => only the numerator (_num) is negative
 * 	- the denominator is always different than 0
 * 	- canonical takes care of the placing the sign at the numerator
 */
class Rational{

public:
	class NumberImprecisionException {
		public:
		NumberImprecisionException() {}
	};

	Rational(): _num(1), _den(1){}
	Rational(long long value){_num = static_cast<double>(value); _den=1;}

	Rational(double num, double den){
		ASS(den!=0);
		if (den < 0 && num >0 ){
			_num = -_num;
		}
		if (den < 0 && num < 0) {
			_num = -_num;
			_den = -_den;
		}
		if ( num == 0 ) {
			_num = 0;
			_den = 1;
		}

	}

	~Rational(){}
	Rational& operator=(const Rational& o){
		(*this)._den = o._den;
		(*this)._num = o._num;
		return static_cast<Rational&>(*this);
	}

	//assign in place
	Rational& assign(double num, double den){
		_den=den;
		_num=num;
		return static_cast<Rational&>(*this);
	}

	Rational operator+(const Rational& o) const;
	//unary minus
	Rational operator-() const;
	Rational operator-(const Rational& o) const;

	Rational operator*(const Rational& o) const;
	Rational operator/(const Rational& o) const;

	Rational& operator+=(const Rational& o);
	Rational& operator-=(const Rational& o);
	Rational& operator*=(const Rational& o);
	Rational& operator/=(const Rational& o);

	Rational& operator++();
	Rational& operator--();

	//comparators
	bool operator==(const Rational& o) const {
		CALL("Rational::operator==");
		//assumes that the rational numbers are canonicalized
		return ((*this)._num == o._num && (*this)._den == o._den);

	}

	//comparison with the same type of values
	//one could also add comparison with integers/long longs
	bool operator>(const Rational& o) const;
	bool operator<(const Rational& o) const;
	bool operator>=(const Rational& o) const;
	bool operator<=(const Rational& o) const;


	double toDouble() const{
		return static_cast<double>((*this)._num/(*this)._den);
	}
	//useful numbers
	static const Rational& zero(){static Rational res(0,1); return res;}
	static const Rational& one(){static Rational res(1,1); return res;}
	static const Rational& minusOne(){static Rational res(-1,1); return res;}
	static const Rational& two(){static Rational res(2,1);return res;}

	bool isPositive() const{ return *this >= zero();}
	bool isPositiveNonZero() const{return *this > zero();}

	bool isNegative() const{ return *this <= zero();}
	bool isNegativeNonZero() const{ return *this < zero();}

	bool isZero() const{ return *this == zero(); }

	Rational abs() const{
		if ((*this).isNegative()){
			return Rational( -(*this)._num, (*this)._den);
		}
		return static_cast<Rational>(*this);
	}

	long long Numerator() const {return _num;}
	long long Denomination() const {return _den;}

	//cast operators
	operator double() const {return double(_num / _den);}
	operator float() const {return float(_num / _den);}

	friend ostream& operator<< (ostream &out, Rational &val){
		out << val._num << " / " << val._den;
		return out;
	}

protected:
	bool sameDenominator(const Rational& a , const Rational& b) const{
		CALL("Rational::sameDenominator");
		return (a._den == b._den);
	}

	Rational inverse() const{
		CALL("Rational::inverse");
		if (isZero()){
			return zero();
		}
		Rational result(_den, _num);
		return result;
	}
	Rational canonical();

private:
	//numerator and denominator
	long long _num;
	//keeping the denominator as unsigned long long might get us in trouble for overflow
	//detection. This is due to the size of this representation.
	unsigned long long _den;
};

unsigned long long GCD(long long n1, unsigned long long n2);

//overflow check functions
inline bool additionOverflow(long long n1, long long n2);
inline bool subtractionOverflow(long long n1, long long n2);
inline bool multiplicationOverflow(long long n1, long long n2);
inline bool divisionOverflow(long long numerator, long long denominator);
inline bool moduloOverflow(long long numerator, long long denominator);

} //__Aux_Number
} //Kernel
#endif //GNUMP
#endif /* RATIONAL_HPP_ */
