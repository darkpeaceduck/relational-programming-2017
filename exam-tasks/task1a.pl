
/* check + instaning D */
sumd(A, B, C, D):-
	D is (A + B + C) mod 10.
	
/* check + instaning A */
suma(A, B, C, D):-
	A is (D + 10 - B - C) mod 10.



	
/*gen - unknown res and one operand */	
gen(A, B, C, D):-
	number(A),
	not(number(B)),
	number(D),
	suma(B, A, C, D).

gen(A, B, C, D):-
	not(number(A)),
	number(B),
	number(D),
	suma(A, B, C, D).

	
/* gena  - make instances  with no overflow*/
ha(A, B, C, D):-
	not(number(A)),
	number(B),
	not(number(D)),
	A = 0,
	D is (A + B + C),
	D < 10.
	
	
gena(A, B, C, D):-
	gen(A, B, C, D).
		
gena(A, B, C, D):-
	not(number(A)),
	not(number(B)),
	number(D),
	A = 0,
	B is D - C,
	B >= 0.
	
gena(A, B, C, D):-
	not(number(A)),
	number(B),
	not(number(D)),
	ha(A, B, C, D).
	
gena(A, B, C, D):-
	number(A),
	not(number(B)),
	not(number(D)),
	ha(B, A, C, D).
	
gena(A, B, C, D):-
	not(number(A)),
	not(number(B)),
	not(number(D)),
	A = 0,
	B = 0,
	sumd(A, B, C, D).
	
gena(A, B, C, D):-
	number(A),
	number(B),
	sumd(A, B, C, D).


/* genb make instances  with overflow*/	
hb(A, B, C, D):-
	not(number(A)),
	number(B),
	not(number(D)),
	A = 9,
	D is (A + B + C) mod 10,
	(A + B + C) >= 10.
	
genb(A, B, C, D):-
	gen(A, B, C, D).
	
	
genb(A, B, C, D):-
	not(number(A)),
	not(number(B)),
	number(D),
	A = 9,
	B is (D + 10 - C - A),
	B < 10.
	
genb(A, B, C, D):-
	not(number(A)),
	number(B),
	not(number(D)),
	hb(A, B, C, D).
	
genb(A, B, C, D):-
	number(A),
	not(number(B)),
	not(number(D)),
	hb(B, A, C, D).
	
genb(A, B, C, D):-
	not(number(A)),
	not(number(B)),
	not(number(D)),
	A = 9,
	B = 9,
	sumd(A, B, C, D).

genb(A, B, C, D):-
	number(A),
	number(B),
	sumd(A, B, C, D).	
	
	
/* STATE = OPERAND1, OPERAND2, RES, OVERFLOW */
state([], [], [], 0).
state([H|T], [H2|T2], [H3|T3], A):-
	gena(H, H2, A, H3),
	Q is (H + H2 + A) div 10,
	state(T, T2,T3, Q).
	
state([H|T], [H2|T2], [H3|T3], A):-
	genb(H, H2, A, H3),
	Q is (H + H2 + A) div 10,
	state(T, T2,T3, Q).
	

goal(A, B, C):- 
	reverse(A, Ar),
	reverse(B, Br),
	reverse(C, Cr),
	state(Ar, Br, Cr, 0).
