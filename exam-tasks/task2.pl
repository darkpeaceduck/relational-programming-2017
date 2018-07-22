

opposite(right,  left).
opposite(left,  right).

/* STATE = (man, wolf, goat, cabbage, last transporting) */

/* failure rules */
state(Man, Wolf, Goat, _, _):-
  Wolf=Goat, not(Goat=Man), 
  !, fail.
state(Man, _, Goat, Cabbage, _):-
  Cabbage=Goat, not(Goat=Man), 
  !, fail.

/* success rule */
state(right, right, right, right, _):-
  write('Result (in reversing order, but symmetric solution in straight order):'),
  nl. 

/* transporting rules */
state(right, Wolf, Goat, Cabbage, Last):-
  not(Last=nothing), 

  state(left, Wolf, Goat, Cabbage, nothing), 
  write('Going to left (empty boat)'), nl.

state(Together, Together, Goat, Cabbage, Last):-
  not(Last=wolf), opposite(Together, Other), 
  
  state(Other, Other, Goat, Cabbage, wolf), 
  write('Taking wolf to '), write(Other), nl.

state(Together, Wolf, Together, Cabbage, Last):-
  not(Last=goat), opposite(Together, Other), 
 
  state(Other, Wolf, Other, Cabbage, goat), 
  write('Taking goat to '), write(Other), nl.

state(Together, Wolf, Goat, Together, Last):-
  not(Last=cabbage), opposite(Together, Other), 
 
  state(Other, Wolf, Goat, Other, cabbage), 
  write('Taking cabbage to '), write(Other), nl.

state(left, Wolf, Goat, Cabbage, Last):-
  not(Last=nothing), 
  state(right, Wolf, Goat, Cabbage, nothing), 
  write('Going to right (empty boat) '), nl.


/* task goal */
goal:-state(left, left, left, left, nothing).