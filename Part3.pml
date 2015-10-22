// Definitions of atomic propositions necessary for formulating LTL.
#define xOdd (x % 2 == 1)
#define ySmallerEqualX (y<=x)
#define yEqualsX (y==x)

// x is always odd.
ltl a { []xOdd }
// X will always be even infinitely often.
// Opposite of "It is possible that from a certain point onwards x is always odd."
ltl b { []<>!xOdd}
// There will always be a point from which onwards x will always be even.
// Opposite of "It is possible that from a certain point onwards x is infinitely often odd."
ltl c { []<>[]! xOdd}
// It is always true that y ≤ x.
ltl d { [] ySmallerEqualX }
// It is always true that when y = x it follows that at some point y != x
ltl e { [](yEqualsX -> (<>!yEqualsX)) }


/* The following code has been given as a part of practical specification.*/

byte x=1;
byte y=0;

active proctype P1(){
	do
	:: x=x+2
	od;
}

active proctype P2(){
	do
	:: x=x+1
	od;
}

active proctype P3(){
	do
	:: y<x ->y=x
	od;
}
