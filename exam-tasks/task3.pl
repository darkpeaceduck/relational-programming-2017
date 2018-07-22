/* state(total, pos, fuel, stations, result) */

list_set(L, I, E, LR):-
	nth0(I, L, _, R),
	nth0(I, LR, E, R).
	
list_get(L, I, E):-
	nth0(I, L, E).

list_build(L, 0):-
	L = [].	

list_build(L, S):-
	SI is S - 1,
	list_build(R, SI),
	L = [0 | R].
	
state(Total, Total, _, _).

state(Total, Pos, _,_):-
	Pos > Total,
	!,fail.
	
state(_, Pos, _,_):-
	Pos < 0,
	!,fail.

state(_, Pos , Fuel,_):-
	Fuel == 0,
	Pos > 0,
	!,fail.
	

state(Total, Pos, Fuel, St):-
	PP is Pos + 1,
	F is Fuel - 1,
	state(Total, PP , F, St).
	
state(Total, Pos, Fuel, St):-
	PP is Pos - 1,
	F is Fuel - 1,
	state(Total, PP , F, St).
	
state(Total, Pos, Fuel, St):-
	list_get(St, Pos, V),
	V > 0,
	VN is V - 1,
	FN is Fuel + 1,
	list_set(St, Pos, VN, STN),
	state(Total, Pos, FN, STN).
	
state(Total, Pos, Fuel, St):-
	Pos > 0,
	Fuel > 0,
	list_get(St, Pos, V),
	VN is V + 1,
	FN is Fuel - 1,
	list_set(St, Pos, VN, STN),
	state(Total, Pos, FN, STN).