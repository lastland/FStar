module SL.ConcurrentExamples

open SL.Base
open SL.AutoTactic

// Lift from PURE to STATE, needed since we use $ for some args, which is annoying...
let l (x:'a) : ST 'a (fun p m -> m == emp /\ p x m) [] = x


//#set-options "--debug SL.ConcurrentExamples"
//#set-options "--print_full_names --prn --print_implicits"


let left  r () : ST int (fun p m -> exists v. m == r |> v /\ p 1 (r |> v)) [tosref r] by (sl_auto ()) = 1
let right r () : ST int (fun p m -> exists v. m == r |> v /\ p 2 (r |> v)) [tosref r] by (sl_auto ()) = 2

let par1 (r:ref int) (s:ref int) : ST int (fun p m -> exists v w. m == (r |> v <*> s |> w) /\ p 3 (r |> v <*> s |> w)) [] by (sl_auto ())
=
  let (x, y) = par (left r) (right s) in
  x + y

let par2 (r:ref int) (s:ref int) : ST int (fun p m -> exists v w. m == (r |> v <*> s |> w) /\ p 3 (r |> v <*> s |> w))
			            [tosref r; tosref s] by (sl_auto ())
=
  let (x, y) = par (left s) (right r) in
  x + y


let par3 (r s t : ref int) : ST int (fun p m -> exists v w u. m == (r |> v <*> s |> w <*> t |> u) /\ p 5 (r |> v <*> s |> w <*> t |> u)) [] by (FStar.Tactics.dump "1"; sl_auto ())
=
  let (x, z) = par (fun () -> par2 r s) (right t) in
  x + z

(* Funny, the VC for this is much smaller and verifies a lot quicker *)
#push-options "--use_two_phase_tc false"
let par3' (r s t : ref int) : ST int (fun p m -> exists v w u. m == (r |> v <*> s |> w <*> t |> u) /\ p 5 (r |> v <*> s |> w <*> t |> u)) [] by (FStar.Tactics.dump "2"; sl_auto ())
=
  let (x, z) = par (fun () -> par2 r s) (right t) in
  x + z
#pop-options

let ret (x:'a) () : ST 'a (fun p m -> m == emp /\ p x m) [] =
  x

let set_to_2 (r : ref int) () : ST int (fun p m -> exists v. m == (r |> v) /\ p 1 (r |> 2)) [tosref r] =
  r := 2;
  1

#set-options "--debug SL.ConcurrentExamples --debug_level Tac"

(* Actually changing a reference *)
let test04 (r:ref int) : ST int (fun p m -> exists v. m == r |> v /\ p 3 (r |> v)) [tosref r] by (sl_auto ())
=
  let (x, y) = par (set_to_2 r) (ret 2) in
  x + y


(* This is explicit about the frames of the parallel composition, but still requires
 * non-trivial frame reasoning *)
(* Does not work now, we haven't implemented par_exp in the tactic (do we want to? probably not *)
//let test03' (r:ref int) : ST int (fun p m -> exists v. m == r |> v /\ p 3 (r |> v)) [] by (sl_auto ())
//=
//  let (x, y) = par_exp emp emp (fun () -> l 1) (fun () -> l 2) in
//  x + y


let test_acq (r:ref int) (l:lock r) : ST int (fun p m -> m == emp /\ (forall v. p 3 (r |> v))) [tosref r] by (sl_auto ())
  =
  acquire l;
  3

let test_acq_rel (r:ref int) (l:lock r) : ST unit (fun p m -> m == emp /\ p () emp) [] by (sl_auto ())
  =
  acquire l;
  //let v = !r in
  release l

// let test06 (r:ref int) : ST int (fun p m -> exists v. m == r |> v /\ p 3 (r |> v)) [] by (sl_auto ()) =
//   let l = mklock r in
//   let _ = par (fun () -> acquire l; release l; 1) (fun () -> acquire l; release l; 2) in
//   3
//
// unfold let return_wp (a:Type) (x:a) :st_wp a =
//   fun post m0 -> m0 == emp /\ post x m0
//
// open FStar.Tactics
//
// // `compute` is needed for these two, but they work without the tactic since they are
// // explicit about their heaps already. We also use STATE instead of the framed ST.
// let test01 () : STATE int (fun p m -> forall r. m == emp /\ p r m) by (compute ())
// =
//   let (x, y) = par_exp' emp emp (fun () -> l 1) (fun () -> l 2) in
//   x + y
//
// let test02 () : STATE int (fun p m -> m == emp /\ p 3 m) by (compute ())
// =
//   let (x, y) = par_exp' emp emp (fun () -> l 1) (fun () -> l 2) in
//   x + y

