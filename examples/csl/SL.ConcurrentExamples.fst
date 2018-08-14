module SL.ConcurrentExamples

open SL.Heap
open SL.Effect
open SL.ConcurrentActions
open SL.AutoTactic

// Lift from PURE to STATE, needed since we use $ for some args, which is annoying...
let l (x:'a) : STATE 'a (fun p m -> m == emp /\ p x m) = x

(* A trivial test without mentioning heaps *)
//let test03 (r:ref int) : ST int (fun p m -> exists v. m == r |> v /\ p 3 (r |> v)) by (sl_auto ())
//=
//  let (x, y) = par (fun () -> l 1) (fun () -> l 2) in
//  x + y


(* Actually changing a reference *)
//let test04 (r:ref int) : ST int (fun p m -> exists v. m == r |> v /\ p 3 (r |> v)) by (sl_auto ())
//=
//  let (x, y) = par // #_ #_ #(bind_wp (range_of ()) _ _ (frame_write_wp r 2) (fun _ -> return_wp _ 1)) #_
//                 (fun () -> r := 2; 1) (fun () -> l 2) in
//  x + y

//let noaddrs = Set.empty #nat

  //#set-options "--print_full_names"



// let addrs_emp (m m':memory) : Lemma (requires (defined m /\ addrs_in m == Set.empty))
//                                  (ensures (defined (m <*> m') /\ m <*> m' == m'))
//                                  [SMTPat (m <*> m')] // TODO: very likely a bad pattern
//      = admit () // provable from inside SL.Heap

let test05' (r:ref int) (l:lock r) : ST int (fun p m -> m == emp /\ (forall v. p 3 (r |> v))) [tosref r] by (sl_auto ())
                            
  =
  acquire l;
  3

let test05 (r:ref int) (l:lock r) : ST unit (fun p m -> m == emp /\ p () emp) [] by (sl_auto ())
                            
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

(* Sanity check that other programs still work.. since we modified the tactic *)
//let swap_wp (r1 r2:ref int) = fun p m -> exists x y. m == (r1 |> x <*> r2 |> y) /\ p () (r1 |> y <*> r2 |> x)
//let swap (r1 r2:ref int) :ST unit (swap_wp r1 r2) by (sl_auto ())
//  = let x = !r1 in
//    let y = !r2 in
//    r1 := y;
//    r2 := x

//#set-options "--debug SL.ConcurrentExamples"
//#set-options "--print_full_names --prn --print_implicits"

let left  r () : ST int (fun p m -> exists v. m == r |> v /\ p 1 (r |> v)) [tosref r] by (sl_auto ()) = 1 
let right r () : ST int (fun p m -> exists v. m == r |> v /\ p 2 (r |> v)) [tosref r] by (sl_auto ()) = 2

let test03 (r:ref int) (s:ref int) : ST int (fun p m -> exists v w. m == (r |> v <*> s |> w) /\ p 3 (r |> v <*> s |> w)) [] by (sl_auto ())
=
  let (x, y) = par (left r) (right s) in
  x + y
  
let test04 (r:ref int) (s:ref int) : ST int (fun p m -> exists v w. m == (r |> v <*> s |> w) /\ p 3 (r |> v <*> s |> w)) [] by (sl_auto ())
=
  let (x, y) = par (left s) (right r) in
  x + y




  
(* This is explicit about the frames of the parallel composition, but still requires
//#set-options "--debug SL.ConcurrentExamples"
 * non-trivial frame reasoning *)
let test03' (r:ref int) : ST int (fun p m -> exists v. m == r |> v /\ p 3 (r |> v)) [] by (sl_auto ())
=
  let (x, y) = par_exp emp emp (fun () -> l 1) (fun () -> l 2) in
  x + y
