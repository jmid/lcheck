open QCheck
open LCheck

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

(* example operator -- not monotone *)
let flip e = if e = L.Bot then L.Top else L.Bot

(*
let module LTests = GenericTests(L) in
  run_tests LTests.suite;;
*)
(*
 let flip_desc = ("flip",flip) in
   run (testsig (module L) -<-> (module L) =: flip_desc);;
 *)
