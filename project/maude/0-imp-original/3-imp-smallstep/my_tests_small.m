in ../../../builtins.maude
in ../imp-syntax.maude
in ../../state.maude

in imp-semantics-smallstep

in ../imp-programs.maude

mod TEST is including IMP-SEMANTICS-SMALLSTEP + IMP-PROGRAMS .  endm

--- set trace on .

--- rew < 1 , .State > .
--- rew < errorBool , .State > .
rew o < 8 + 2 , .State > .
rew o < ( 8 ) / ( 2 / 1 ) , .State > .
rew * < ( 8 ) / ( 2 / 1 ) , .State > .
rew * < ( 8 ) / ( 2 / 1 ) + ( 3 + ( 3 + 3 ) ) , .State > .

--- SmallStep-On-Errors
rew o < errorAr, x |-> 3 > .
rew * < errorAr, x |-> 3 > .
rew o < errorAr, .State > .
rew * < errorAr, .State > .

rew o < errorBool, x |-> 3 > .
rew * < errorBool, x |-> 3 > .
rew o < errorBool, .State > .
rew * < errorBool, .State > .

rew o < errorStmt, x |-> 3 > .
rew * < errorStmt, x |-> 3 > .
rew o < errorStmt, .State > .
rew * < errorStmt, .State > .

--- SmallStep-Lookup
rew o < x, x |-> 3 > .
--- rew o < x, x |-> errorAr > .

--- SmallStep-DIV
rew o < 4 / 2 , .State > .
rew o < 4 / 0 , .State > .
rew o < 4 / 0 , x |-> 2 > .
rew * < 4 / 0 , x |-> 2 > .
rew * < errorAr, x |-> 3 > .
rew o < ( 8 / 2 ) / ( 2 / 1 ) , .State > .
rew * < ( 8 / 2 ) / ( 2 / 1 ) , .State > .
rew o < errorAr / 1 , .State > .
rew * < errorAr / 1 , .State > .
rew o < 1 / errorAr , .State > .
rew * < 1 / errorAr , .State > .
rew o < ( 4 / 0 ) / 1 , .State > .
rew o < ( 4 / 0 ) / 1 , x |-> 3 > .
rew o < 4 / ( 1 / 0 ) , .State > .
rew * < ( 4 / 0 ) / 1 , .State > .
rew o < x / 0 , .State > .
rew o < x / 1 , x |-> 4 > .
rew * < x / 1 , x |-> 4 > .
rew * < ( x / 0 ) / x , .State > .
rew * < x / ( x / 0 ) , .State > .

--- SmallStep-ADD
rew o < 1 + ( 1 + 2 ) , .State > .
rew * < 1 + ( 1 + 2 ) , .State > .
rew o < ( 1 / 0 ) + 1 , .State > .
rew o < 1 + ( 1 / 0 ) , .State > .
rew * < 1 + ( 1 + 2 ) + (2 / (3 / 0 ) + 0 ), .State > .
rew o < x + ( x / 0 ) , .State > .
rew o < x + ( x / 0 ) , x |-> 3 > .
rew * < x + ( x / 0 ) , x |-> 3 > .
rew * < x + ( x / 0 ) , .State > .
rew * < ( x / 0 ) + x , .State > .

--- SmallStep-LEQ-ARG
rew o < 1 <= 2 , .State > .
rew * < 1 <= 2 , .State > .
rew o < 1 / 0 <= 2 , .State > .
rew o < 1 <= 2 / 0 , .State > .
rew * < 1 / 0 <= 2 , .State > .
rew * < 1 <= 2 / 0 , .State > .
rew * < 1 <= ( 2 / 0 ) + 2 + ( 3 / 2 + 4 ) , .State > .
rew * < x <= 2 / 0 , x |-> 3 > .
rew o < x <= 2 / 0 , x |-> 3 > .

--- SmallStep-Not-Arg
rew o < ! true, .State > .
rew o < ! false, .State > .
rew * < ! false, .State > .
rew * < ! true, .State > .
rew * < ! 2 / 0 <= 3, .State > .
rew * < ! 2 <= 3 / 0, .State > .
rew o < ! 2 <= 3 / 0, .State > .

--- SmallStep-AND
rew o < true && true, .State > .
rew o < false && true, .State > .
rew o < true && false, .State > .
rew o < false && false, .State > .
rew o < 0 <= 0 / 0 && true, .State > .
rew o < 0 <= 0 / 0 && false, .State > .
rew o < false && 0 <= 0 / 0 , .State > .
rew * < true && 0 <= 0 / 0 , .State > .
rew o < true && 0 <= 0 / 0 , .State > .
rew o < 0 <= 0 / 0,.State > .
rew * < ( true && 0 <= 0 / 0 + 0 / 0 + 0 / 0 ) && true, .State > .

--- SmallStep-Block
rew o < {errorStmt}, x |-> 3 > .
rew * < {errorStmt}, x |-> 3 > .
rew o < errorStmt, x |-> 3 > .
rew o < errorStmt, .State > .
rew o < {{{errorStmt}}}, x |-> 3 > .
rew * < {{{errorStmt}}}, x |-> 3 > .
rew o < { x =  2 ; } , x |-> 0 > .

--- SmallSteo-Assign
rew o < x =  2 ; , x |-> 0 > .
rew * < x =  2 ; , x |-> 0 > .
rew o < x =  2 / 0 ; , x |-> 0 > .
rew * < x =  2 / 0 ; , x |-> 0 > .
rew o < x =  errorAr ; , x |-> 0 > .
rew * < x =  x / 0 + x + x + ( 6 / 2 ) ; , x |-> 0 > .
rew o < x =  x / 0 ; , x |-> 0 > .
rew * < x =  x / 0 ; , x |-> 0 > .

--- SmallStep-SEQ
rew * < {{}} {{}} , .State > .
rew * < { x = 1 ; } { x = 2 ; }  , x |-> 0 > .
--- rew * < { { x =  1 ; } } { {} }, x |-> 0 > .
---rew * < x ; {} > .
---rew * < { { x =  1 ; } } { {} }, x |-> 0 y |-> 0 > .
--- rew * < { x =  1 ; } { y = 2 ; }, ( x |-> 0 y |-> 0 ) > .
--- rew * < { int n , m ; , .State } > .
rew * < { x = 1 / 0 ; } { x = 2 ; }  , x |-> 0 > .
rew * < { x = 1 ; } { x = 2 / 0 ; }  , x |-> 0 > .
rew * < { x = 1 ; } {{ x = 2 / 0 ; }}  , x |-> 0 > .
rew o < { x = 1 ; } { x = 2 ; }  , x |-> 0 > .
rew o < x = 1 ; { x = 2 ; }  , x |-> 0 > .
rew * < {} errorStmt, .State > .

--- SmallStep-IF
rew * < if ( 1 / 0 <= 3 ) {} else {}, .State > .
rew * < if ( 1 / 0 <= 3 ) { x = 1 ; } else { x = 2 ; }, x |-> 0 > .
rew * < if ( true ) { x = 1 / 0 ; } else { x = 2 ; }, x |-> 0 > .
rew * < if ( false ) { x = 1 ; } else { x = 1 / 0 ; }, x |-> 0 > .
rew * < if ( 1 / 0 <= 3 ) { x = 1 / 0 ; } else { x = 2 / 0 ; }, x |-> 0 > .

--- SmallStep-While
rew * < while (x <= 2) {x = x + 1 ; }, x |-> 0 > .
rew * < while (x <= 2) {x = x / 0 ; }, x |-> 0 > .
rew * < while (x <= 2 / 0) {x = x + 1 ; }, x |-> 0 > .

--- SmalStep-PGM
rew o < int a ; {} > .
rew * < int a ; {} > .
rew o < int a , b , c ; {}  > .
rew * < int a , b , c ; { a = a / 0 ; } > .

q
