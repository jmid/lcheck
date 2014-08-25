LCheck
======

LCheck is a module for quickchecking lattice-based code.

The module falls in two:

 - A functor for quickchecking lattice properties

 - two embedded DSLs for quickchecking operations over lattices



An example:
-----------

Suppose you want to ensure that the module L below actually implements
a lattice:

    module L = struct
      let name = "example lattice"
      type elem = Top | Bot
      let leq a b = match a,b with
        | Bot, _ -> true
        | _, Top -> true
        | _, _   -> false
      let join e e' = if e = Bot then e' else Top
      let meet e e' = if e = Bot then Bot else e'
      let bot = Bot
      let eq = (=)
      let arb_elem      = Arbitrary.among [Top; Bot]
      let arb_elem_le e = if e = Bot then Arbitrary.return bot else arb_elem
      let equiv_pair    = Arbitrary.lift (fun o -> (o,o)) arb_elem
      let to_string e   = if e = Bot then "Bot" else "Top"
      let pprint e      = Format.print_string (to_string e)
    end

where
  - leq,join,meet,bot implements a lattice over elements of type elem,
  - arb_elem is a generator of arbitrary elem values,
  - arb_elem_le is a generator of arbitrary elem values less-or-equal to its argument,
  - equiv_pair is a generator of equivalent elem values,


You can instantiate a generic functor with L and run the generated
QuickCheck testsuite:

    # let module LTests = GenericTests(L) in
        run_tests LTests.suite;;
    check 19 properties...
    testing property leq reflexive in example lattice...
      [✔] passed 1000 tests (0 preconditions failed)
    testing property leq transitive in example lattice...
      [✔] passed 1000 tests (0 preconditions failed)
    testing property leq anti symmetric in example lattice...
      [✔] passed 1000 tests (0 preconditions failed)

     ... (32 additional lines cut) ...

    tests run in 0.02s
    [✔] Success! (passed 19 tests)
    - : bool = true
    # 


Suppose you furthermore have a function between lattices, e.g., flip : L -> L:

    (* example operator -- not monotone *)
    let flip e = if e = L.Bot then L.Top else L.Bot


You can test flip for monotonicity using LCheck's signature DSL:

    # let flip_desc = ("flip",flip) in
         run (testsig (module L) -<-> (module L) =: flip_desc);;
    testing property 'flip monotone in 1. argument'...
      [×] 264 failures over 1000 (print at most 1):
      (Bot, Top)
    - : bool = false
    # 

where the -<-> arrow is supposed to resemble a function arrow --->
with an associated lattice ordering.

Other "property arrows" include -$-> for testing strictness and -~->
for testing invariance.


The functor:
------------

The functor GenericTests accepts any module with the below signature.

    module type LATTICE_TOPLESS =
    sig
      val name  : string
      type elem
      val leq       : elem -> elem -> bool
      val join      : elem -> elem -> elem
      val meet      : elem -> elem -> elem
      val bot       : elem
    (*  val top       : elem *)
      val eq          : elem -> elem -> bool
      val to_string   : elem -> string
      val pprint      : elem -> unit
      val arb_elem    : elem Arbitrary.t
      val equiv_pair  : (elem * elem) Arbitrary.t
      val arb_elem_le : elem -> elem Arbitrary.t
    end

Note that the above signature does not contain an explicit top
element. Insted the signature LATTICE extends the above signature with
such an element along with a small top-related testsuite.


In addition LCheck provides a number of helper lattices:

 - Bool: a Boolean lattice under reverse implication ordering,
 - DBool: a Boolean lattice under implication ordering,
 - MkPairLattice: a functor for building pair lattices ordered component-wise,
 - MkListLattice: a functor for building list lattices ordered entry-wise.


The embedded DSLs:
------------------

The library contains two embedded DSLs for testing operations over
lattices: a combinator-based DSL and a more human-readable DSL with a
syntax approaching math-mode signatures. We illustrate both below.


- The signature DSL is defined by the following BNF:

    baseprop  ::=  modname -<-> modname       (monotonicity)
                |  modname -$-> modname       (strictness)
                |  modname -~-> modname       (invariance)

        prop  ::=  '(testsig' (modname '--->')* baseprop ('--->' modname)*) ')' 'for_op'


  For example,

    (testsig (module L) -<-> (module L)) for_op

  specifies monotonicity of a function from L to L.


  For a more advanced example,

    (testsig (module L) ---> (module L) -<-> (module L) ---> (module L) ---> (module L)) for_op

  specifies monotonicity in the second argument of a function with
  signature L -> L -> L -> L -> L.

  Furthermore the library provides '=:' as an infix shorthand for
  for_op.


  One limitation of the signature-based DSL is that all arguments have
  to be lattice, i.e., to match the LATTICE_TOPLESS signature. The
  combinator-based DSL described below softens this requirement.



- The combinator DSL is defined by the following BNF:


    modname   ::=  '(module' NAME ')'
  
    baseprop  ::=  op_monotone
                |  op_strict
                |  op_invariant
  
    rightprop ::=  baseprop
                |  pw_right modname '(' rightprop ')'
  
    leftprop  ::=  rightprop
                |  pw_left modname '(' leftprop ')'
  
    prop      ::=  'finalize (' leftprop modname modname ')'



  Argument modules to pw_left and pw_right has to match the following
  signature (an element type, a generator, and a string coercion
  function):

    module type ARB_ARG =
    sig
      type elem
      val arb_elem    : elem Arbitrary.t
      val to_string   : elem -> string
    end


  Revising the example above,

    finalize (op_monotone (module L) (module L))

  specifies monotonicity of a function from L to L.


  Revising the more advanced example above,

    finalize (pw_left (module L) (pw_right (module L) (pw_right (module L) op_monotone)) (module L) (module L))

  specifies monotonicity in the second argument of a function with
  signature L -> L -> L -> L -> L.

  Furthermore the library provides '=::' as an infix shorthand for
  finalize.






To build and run:
-----------------

On the command line first run:

    $ make

Then you can start an OCaml toplevel with the appropriate modules loaded:

    $ ocaml -I `ocamlfind query qcheck` -I _build unix.cma qcheck.cma lCheck.cmo
    # #use "example.ml";;
    module L :
      sig
        val name : string
        type elem = Top | Bot
        val leq : elem -> elem -> bool
        val join : elem -> elem -> elem
        val meet : elem -> elem -> elem
        val bot : elem
        val eq : 'a -> 'a -> bool
        val arb_elem : elem QCheck.Arbitrary.t
        val arb_elem_le : elem -> elem QCheck.Arbitrary.t
        val equiv_pair : (elem * elem) QCheck.Arbitrary.t
        val to_string : elem -> string
        val pprint : elem -> unit
      end
    val flip : L.elem -> L.elem = <fun>

From here on you can try the examples from above.
