in ../../../builtins.maude
in ../imp-syntax.maude
in ../../state.maude

in imp-semantics-bigstep

in ../imp-programs.maude

mod TEST is including IMP-SEMANTICS-BIGSTEP + IMP-PROGRAMS .  endm

--- set trace on .

---rewrite < 1 / 0 , .State > .
---rewrite < 1 / 1 , .State > .

--- Sorts/configurations
rew < Error > .
rew < 2 + 2 + ( 3 / 2), Error > .
rew < true && ! true, Error > .
rew < { x = 3 ; } , Error > .
rew < 1 / z , Error > .
rew < 1 / z , .State > .

--- BigStep-Int Tests
rew < 1, .State > .
rew < 1, Error > .

--- BigSte-lookup Tests
rew < x, x |-> 3 > .
rew < x, Error > .

--- BigStep-ADD Tests
rew < 3 + 3, .State > .
rew < 3 + 3, Error > .
rew < 3 + 3 / 0 , .State > .
rew < 3 / 0 + 3 , .State > .
rew < (3 + 3) / 0 + 3 , .State > .
rew < 3 + (3 / 0 + 3) , .State > .

--- BigStep-DIV Tests
rew < 6 / 2 , .State > .
rew < 6 / 2 , Error > .
rew < 3 / 0 , .State > .
rew < ( 6 / 2 ) / 1 , .State > .
rew < ( 6 / 2 ) / 0 , .State > .
rew < ( 6 / 0 ) / 1 , .State > .
rew < 3 / 0 , Error > .

--- BigStep-Bool Tests
rew < true , .State > .
rew < false , .State > .
rew < true , Error > .
rew < false , Error > .

--- BigStep-LEQ Tests
rew < 1 <= 2, .State > .
rew < 2 <= 1, .State > .
rew < 1 <= 2, Error > .
rew < 2 <= 1, Error > .
rew < 1 / 0 <= 1, .State > .
rew < 1 <= 1 / 0, .State > .
rew < 1 / 0 <= 1, Error > .
rew < 1 <= 1 / 0, Error > .
rew < 1 / 0 + 1 + ( 4 / 2 ) <= 1, Error > .
rew < x / 2 <= 1, Error > .
rew < 2 <= x / 3, Error > .
rew < 2 <= x / 0, .State > .
rew < x / 0 <= 2, .State > .

--- BigStep-NotT-True
rew < ! true, .State > .
rew < ! true, Error > .
rew < ! 1 / 0 <= 1 , .State > .
rew < ! 1 / 1 <= 1 , Error > .
rew < ! 1 / 1 <= 1 / 0 , Error > .

--- BigStep-Not-False
rew < ! false, .State > .
rew < ! false, Error > .
rew < ! 1 / 0 <= 1 , .State > .
rew < ! 4 / 1 <= 1 , Error > .
rew < ! 1 / 1 <= 1 / 0 , Error > .

--- BigStep-And-False
rew < false && 2 <= 3, .State > .
rew < false && 2 / 0 <= 3, .State > .
rew < false && true, .State > .
rew < false && x <= 3, .State > .
rew < false && x / 0 <= 3, .State > .
rew < false && x / 0 <= 3, Error > .

--- BigStep-And-True
rew < true && true, .State > .
rew < true && false, .State > .
rew < true && 2 <= 3, .State > .
rew < true && 2 / 0 <= 3, .State > .
rew < true && x / 0 <= 3, x |-> 3 > .
rew < true && true, Error > .
rew < true && x / 0 <= 3, Error > .

--- BigStep-Empty-Block
rew < {}, .State > .
rew < {}, x |-> 3 > .
rew < {}, Error > .
rew < {} , x |-> undefined > .

--- BigStep-Block
rew < { { } } , .State > .
rew < { x = 3 ; }, x |-> 0 > .
rew < { { } } , Error > .
rew < { { { x = 3 ; } } }, Error > .
--- rew < { x = 3 / 0 ; }, .State > . --- TODO
--- rew < { x = 3 ; }, Error > . --- TODO

--- BigStep-ASGN
---rew < { x = 1 ; } , x |-> undefined > .
rew < { x = 4 ;}, x |-> 69 > .
rew < { x = 4 / 0 ;}, x |-> 69 > .
rew < { x = 1 ; } , x |-> undefined > .

--- BigStep-SEQ
rew < { x = 1 ; } { x = 2 ; }  , x |-> 0 > .
rew < { x = 1 / 0 ; } { x = 2 ; }  , x |-> 0 > .
rew < { x = 1 ; } { x = 2 / 0 ; }  , x |-> 0 > .

--- BigStep-IF-True
rew < if (true) {} else {} , .State > .
rew < if (true) {} else {} , Error > .
rew < if (true) { x = 2 ; } else { } , x |-> 0 > .
rew < if (true) { x = 2 / 0 ; } else { } , x |-> 0 > .
rew < if ( 1 / 0 <= 3 ) { x = 2 / 0 ; } else { } , x |-> 0 > .
rew < if (true) { x = 2 ; } else { x = 33 / 0 ; } , Error > .

--- BigStep-IF-True
rew < if ( 1 / 0 <= 3 ) { x = 2 / 0 ; } else { } , x |-> 0 > .
rew < if (false) { x = 2 / 0 ; } else { x = 33 ; } , x |-> 0 > .
rew < if (false) { x = 2 ; } else { x = 33 / 0 ; } , x |-> 0 > .
rew < if (false) { x = 2 ; } else { x = 33 / 0 ; } , Error > .
rew < if (false) {} else {} , Error > .

--- BigStep-While-False Tests
rew < while (false) { x = 96 ; }, x |-> 0 > .
rew < while (1 / 0 <= 0) { x = 96 ; }, x |-> 0 > .
rew < while (false) { x = 96 ; }, Error > .

--- BigStep-While-True Tests
rew < while (x <= 3) {x = x + 1 ; } , x |-> 0 > .
rew < { while (x <= 3) {x = x + 1 ; } } { x = x / 0 ; }, x |-> 0 > .

--- BigStep-PGM
rew < int a ; {} > .
rew < int a , b , c ; { a = a / 0 ; } > .

q
