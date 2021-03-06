# cs522_project

----

* Design of Syntax and Big & Small step semantics in Coq
  * Imp Syntax, state and configurations
    * For States, we return a function that wraps up the string identifier returning the new value or the old value of other identifiers
    * Created an inductive type for 
      * Configurations in Big and Small step
      * Blocks for the Imp syntax
    * Semantics
      * For both big step and small step since Coq the way we encoded rewriting was with relations. This avoids the prohibition of non-termination in Coq. Note doing it with functions would have not been possible because of the previous sentence.
    * Statement of equivalence
      * Program configuration rewrites to empty block configuration with final state
      * Big step takes only 1 step, small step needs some N steps
    * For evaluation of Imp Syntax we have both a recursive aeval and beval
* Top level: Big Step program is equivalent to some N steps of Small Step Program
* This proof reduces down pretty quickly to Statement configuration equivalence
* Statement configuration equivalence breaks into 4 inductive cases (based on the constructors): 
  * assignment
    * AExp is the same and state update is the same
  * sequence
  * while
    * BExp (boolean guard eval) is the same, and block evaluation is the same
  * if/else
* Since all constructors depend on AExp/BExp the proof boils down to two key lemmas:
  * Evaluating an arithmetic expression is equal to evaluating them in each of the Small and Big Step semantics
  * Similarly for boolean expressions
* Also, several lemmas to overcome small step awkwardness
  * Added an idea of confluence for small step rewrites
    * A -> B => A -> C => B -> C
  * Some basic intuition about the success of, for example, evaluating an assignment
    * If the expression can successfully rewrite to a concrete value, then the assignment can rewrite to empty block with updated state and vice versa
    * If the sequence can successfully rewrite to empty block with some new state, then the first statement must have successfully rewritten to some intermediate state and the second statement rewritten from that state to empty block with the new state, and vice versa

----

Note the lf_brando lf_kenny files can be ignored. They are tutorials and book exercises on theorem proving.

