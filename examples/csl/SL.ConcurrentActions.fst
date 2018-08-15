module SL.ConcurrentActions

open SL.Heap
open SL.Effect

let par_comp #a #b (wpa : st_wp a) (wpb : st_wp b) post m1 m2 =
   wpa (fun a m1' -> wpb (fun b m2' -> post (a, b) (m1' <*> m2')) m2) m1
        
let par_wp' #a #b (wpa : st_wp a) (wpb : st_wp b) post m =
    exists m1 m2.
           m == (m1 <*> m2)
        /\ par_comp wpa wpb post m1 m2

(* Silly lemma, but allows to handle goals properly *)
let par_wp'_lemma
  #a #b
  (#wpa : st_wp a)
  (#wpb : st_wp b)
  (m m1 m2 : memory)
  (post : post (a * b))
  (_ : squash (m == (m1 <*> m2)))
  (_ : squash (par_comp wpa wpb post m1 m2))
  //(_ : squash (wpa (fun a m1' -> forall b. post (a, b) m1') m1))
  //(_ : squash (wpb (fun b m2' -> forall a. post (a, b) m2') m2))
     : Lemma (m == (m1 <*> m2)
               /\ (par_comp wpa wpb post m1 m2)) = ()

let par_wp #a #b (wpa : st_wp a) (wpb : st_wp b) : st_wp (a * b) =
  fun post m0 -> frame_wp (par_wp' wpa wpb) (frame_post post) m0

assume val par : (#a:Type) -> (#b:Type) ->
                 (#wpa : st_wp a) ->  (#wpb : st_wp b) ->
                 ($f : (unit -> STATE a wpa)) ->
                 ($g : (unit -> STATE b wpb)) ->
                 STATE (a * b) (par_wp' wpa wpb)



(* Locks and operations *)
// Locks are over a particular reference r.
// Can we use a list or a set? Non-trivial to make it work. Even a set of addresses causes many blowups.
// Can we use a heap predicate? Can we automate frame inference then?
assume new type lock : #a:Type -> ref a -> Type0

let mklock_wp #a (r:ref a) post m = exists v. m == r |> v /\ (forall (l:lock r). post l emp)
let frame_mklock_wp r post m0 = frame_wp (with_fp [tosref r] <| mklock_wp r) (frame_post post) m0
assume val mklock : #a:Type -> (r: ref a) ->
                    STATE (lock r) (frame_mklock_wp r)

  //let l = mklock r in
  //acquire l;
  //par (fun () -> acquire l; r := 2; release l)
  //    (fun () -> r := !r + 1; release l)


let acquire_wp r l post m = m == emp /\ (forall v. post () (r |> v))
let frame_acquire_wp r l post m0 = frame_wp (with_fp [] <| acquire_wp r l) (frame_post post) m0
assume val acquire : #a:Type -> (#r: ref a) -> (l : lock r) ->
                     STATE unit (frame_acquire_wp r l)


let release_wp r l post m = (exists v. m == r |> v) /\ post () emp
let frame_release_wp r l post m0 = frame_wp (with_fp [tosref r] <| release_wp r l) (frame_post post) m0
assume val release : #a:Type -> (#r: ref a) -> (l : lock r) ->
                     STATE unit (frame_release_wp r l)


// let locking_wp r l wp post m =
//     wp (fun x m' -> forall v m1. m' == (r |> v <*> m1) ==> post x m1) m
// 
// assume val locking : #a:Type -> #b:Type -> #r:(ref a) -> (l : lock r) ->
//                      (#wp : st_wp b) -> (f : unit -> STATE b wp) ->
//                   STATE b (frame_locking_wp r l wp)


(* A version with explicit heaps *)
unfold let par_wp'_exp #a #b (wpa : st_wp a) (wpb : st_wp b) (m1 m2 : memory)
                       (post : post (a * b)) (m : memory) : Type0 =
           m == (m1 <*> m2)
        /\ wpa (fun a m1' -> wpb (fun b m2' -> post (a, b) (m1' <*> m2')) m2) m1

let par_wp_exp #a #b (wpa : st_wp a) (wpb : st_wp b) (m1 m2 : memory) : st_wp (a * b) =
  fun post m0 -> frame_wp (par_wp'_exp wpa wpb m1 m2) (frame_post post) m0

assume val par_exp : (#a:Type) -> (#b:Type) ->
                 (#wpa : st_wp a) ->  (#wpb : st_wp b) ->
                 (m1 : memory) -> (m2 : memory) ->
                 ($f : (unit -> STATE a wpa)) ->
                 ($g : (unit -> STATE b wpb)) ->
                 STATE (a * b) (par_wp_exp #a #b wpa wpb m1 m2)

(* Unframed, explicit variant. Not very user-friendly. *)
assume val par_exp' : (#a:Type) -> (#b:Type) ->
                 (#wpa : st_wp a) ->  (#wpb : st_wp b) ->
                 (m1 : memory) -> (m2 : memory) ->
                 ($f : (unit -> STATE a wpa)) ->
                 ($g : (unit -> STATE b wpb)) ->
                 STATE (a * b) (par_wp'_exp #a #b wpa wpb m1 m2)
