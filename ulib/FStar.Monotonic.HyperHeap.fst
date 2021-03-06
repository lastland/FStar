(*
   Copyright 2008-2014 Nikhil Swamy, Aseem Rastogi, and Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module FStar.Monotonic.HyperHeap
open FStar.Map
open FStar.Preorder
open FStar.Monotonic.Heap
module Map = FStar.Map
open FStar.Ghost

(*
 * AR: 12/26
 *     Cleanup:
 *     - Removed the mref type and associated lemmas
 *     - This module now provides the map view of the memory and associated functions and lemmas
 *     - The intention of this module is for it to be included in HyperStack
 *     - Clients don't need to open/know about HyperHeap, they should work only with HyperStack
 *)

(*
 * This is a temporary assumption, we should fix the model to get rid of it
 *)
assume HasEq_rid: hasEq (erased (list (int * int)))

abstract type rid :(a:Type0{hasEq a}) = erased (list (int * int))

abstract let reveal (r:rid) : GTot (list (int * int)) = reveal r

abstract let color (x:rid): GTot int =
  match reveal x with
  | [] -> 0
  | (c, _)::_ -> c

type hmap = Map.t rid heap

(* AR: see issue#1262 *)
abstract let root :rid = let x:rid = hide [] in x

//is this SMTPat bad ?
val lemma_root_has_color_zero: r:rid{r == root}
                               -> Lemma (requires True) (ensures (color r = 0))
                                 [SMTPat (color r)]
let lemma_root_has_color_zero r = ()

//expose this so that no-one should assume otheriwse
let root_has_color_zero (u:unit) :Lemma (color root = 0) = ()

private abstract let rid_length (r:rid) :GTot nat = List.Tot.length (reveal r)

private abstract let rid_tail (r:rid{rid_length r > 0}) :rid =
  elift1_p Cons?.tl r

abstract val includes : r1:rid -> r2:rid -> GTot bool (decreases (reveal r2))
let rec includes r1 r2 =
  if r1=r2 then true
  else if rid_length r2 > rid_length r1
  then includes r1 (rid_tail r2)
  else false

let disjoint (i:rid) (j:rid) : GTot bool =
  not (includes i j) && not (includes j i)

private val lemma_aux: k:rid -> i:rid
      -> Lemma  (requires
                    rid_length k > 0
                    /\ rid_length k <= rid_length i
                    /\ includes k i
                    /\ not (includes (rid_tail k) i))
                 (ensures False)
                 (decreases (rid_length i))
let rec lemma_aux k i = lemma_aux k (rid_tail i)

abstract val lemma_disjoint_includes: i:rid -> j:rid -> k:rid ->
  Lemma (requires (disjoint i j /\ includes j k))
        (ensures (disjoint i k))
        (decreases (List.Tot.length (reveal k)))
        [SMTPat (disjoint i j);
         SMTPat (includes j k)]
let rec lemma_disjoint_includes i j k =
  if rid_length k <= rid_length j
  then ()
  else (lemma_disjoint_includes i j (rid_tail k);
        if rid_length i <= rid_length (rid_tail k)
        then ()
        else (if includes k i
              then lemma_aux k i
              else ()))

abstract val extends: rid -> rid -> GTot bool
let extends r0 r1 = Cons? (reveal r0) && rid_tail r0 = r1

abstract val parent: r:rid{r<>root} -> Tot rid
let parent r = rid_tail r

abstract val lemma_includes_refl: i:rid
                      -> Lemma (requires (True))
                               (ensures (includes i i))
                               [SMTPat (includes i i)]
let lemma_includes_refl i = ()

abstract val lemma_extends_includes: i:rid -> j:rid ->
  Lemma (requires (extends j i))
        (ensures (includes i j /\ not(includes j i)))
        [SMTPat (extends j i)]
let lemma_extends_includes i j = ()

let lemma_includes_anti_symmetric (i:rid) (j:rid) :
  Lemma (requires (includes i j /\ i <> j))
        (ensures (not (includes j i)))
        [SMTPat (includes i j)]
  = ()

abstract val lemma_extends_disjoint: i:rid -> j:rid -> k:rid ->
    Lemma (requires (extends j i /\ extends k i /\ j<>k))
          (ensures (disjoint j k))
let lemma_extends_disjoint i j k = ()

abstract val lemma_extends_parent: i:rid{i<>root} ->
  Lemma (requires True)
        (ensures (extends i (parent i)))
        [SMTPat (parent i)]
let lemma_extends_parent i = ()

abstract val lemma_extends_not_root: i:rid -> j:rid{extends j i} ->
  Lemma (requires True)
        (ensures (j<>root))
        [SMTPat (extends j i)]
let lemma_extends_not_root i j = ()

abstract val lemma_extends_only_parent: i:rid -> j:rid{extends j i} ->
  Lemma (requires True)
        (ensures (i = parent j))
        [SMTPat (extends j i)]
let lemma_extends_only_parent i j = ()

private abstract let test0 :unit = assert (includes (hide [(0, 1) ; (1, 0)]) (hide [(2, 2); (0, 1); (1, 0)]))
private abstract let test1 (r1:rid) (r2:rid{includes r1 r2}) :unit = assert (includes r1 (hide ((0,0)::(reveal r2))))


assume val mod_set : Set.set rid -> Tot (Set.set rid)
assume Mod_set_def: forall (x:rid) (s:Set.set rid). {:pattern Set.mem x (mod_set s)}
                    Set.mem x (mod_set s) <==> (exists (y:rid). Set.mem y s /\ includes y x)

let modifies (s:Set.set rid) (m0:hmap) (m1:hmap) =
  Map.equal m1 (Map.concat m1 (Map.restrict (Set.complement (mod_set s)) m0))
  /\ Set.subset (Map.domain m0) (Map.domain m1)

let modifies_just (s:Set.set rid) (m0:hmap) (m1:hmap) =
  Map.equal m1 (Map.concat m1 (Map.restrict (Set.complement s) m0))
  /\ Set.subset (Map.domain m0) (Map.domain m1)

let modifies_one (r:rid) (m0:hmap) (m1:hmap) =
  modifies_just (Set.singleton r) m0 m1

let equal_on (s:Set.set rid) (m0:hmap) (m1:hmap) =
 (forall (r:rid). {:pattern (Map.contains m0 r)} (Set.mem r (mod_set s) /\ Map.contains m0 r) ==> Map.contains m1 r)
 /\ Map.equal m1 (Map.concat m1 (Map.restrict (mod_set s) m0))

abstract val lemma_modifies_just_trans: m1:hmap -> m2:hmap -> m3:hmap
                       -> s1:Set.set rid -> s2:Set.set rid
                       -> Lemma (requires (modifies_just s1 m1 m2 /\ modifies_just s2 m2 m3))
                               (ensures (modifies_just (Set.union s1 s2) m1 m3))
let lemma_modifies_just_trans m1 m2 m3 s1 s2 = ()

abstract val lemma_modifies_trans: m1:hmap -> m2:hmap -> m3:hmap
                       -> s1:Set.set rid -> s2:Set.set rid
                       -> Lemma (requires (modifies s1 m1 m2 /\ modifies s2 m2 m3))
                               (ensures (modifies (Set.union s1 s2) m1 m3))
let lemma_modifies_trans m1 m2 m3 s1 s2 = ()

abstract val lemma_includes_trans: i:rid -> j:rid -> k:rid
                        -> Lemma (requires (includes i j /\ includes j k))
                                (ensures (includes i k))
				(decreases (reveal k))
                                [SMTPat (includes i j);
                                 SMTPat (includes j k)]
let rec lemma_includes_trans i j k =
  if j=k then ()
  else match reveal k with
        | hd::tl -> lemma_includes_trans i j (hide tl)

abstract val lemma_modset: i:rid -> j:rid
                  -> Lemma (requires (includes j i))
                           (ensures (Set.subset (mod_set (Set.singleton i)) (mod_set (Set.singleton j))))
let lemma_modset i j = ()

abstract val lemma_modifies_includes: m1:hmap -> m2:hmap
                       -> i:rid -> j:rid
                       -> Lemma (requires (modifies (Set.singleton i) m1 m2 /\ includes j i))
                                (ensures (modifies (Set.singleton j) m1 m2))
let lemma_modifies_includes m1 m2 i j = ()

abstract val lemma_modifies_includes2: m1:hmap -> m2:hmap
                       -> s1:Set.set rid -> s2:Set.set rid
                       -> Lemma (requires (modifies s1 m1 m2 /\ (forall x.  Set.mem x s1 ==> (exists y. Set.mem y s2 /\ includes y x))))
                                (ensures (modifies s2 m1 m2))
let lemma_modifies_includes2 m1 m2 s1 s2 = ()

abstract val lemma_disjoint_parents: pr:rid -> r:rid -> ps:rid -> s:rid -> Lemma
  (requires (r `extends` pr /\ s `extends` ps /\ disjoint pr ps))
  (ensures (disjoint r s))
  [SMTPat (extends r pr); SMTPat (extends s ps); SMTPat (disjoint pr ps)]
let lemma_disjoint_parents pr r ps s =
    assert (pr `includes` r);
    assert (ps `includes` s)

abstract val lemma_include_cons: i:rid -> j:rid -> Lemma
  (requires (i<>j /\ includes i j))
  (ensures (j<>root))
let lemma_include_cons i j = ()

let disjoint_regions (s1:Set.set rid) (s2:Set.set rid) =
     forall x y. {:pattern (Set.mem x s1); (Set.mem y s2)} (Set.mem x s1 /\ Set.mem y s2) ==> disjoint x y

let extends_parent (tip:rid{tip<>root}) (r:rid)
  : Lemma (ensures (extends r (parent tip) /\ r<>tip ==> disjoint r tip \/ extends r tip))
          [SMTPat (extends r (parent tip))]
  = ()

let includes_child (tip:rid{tip<>root}) (r:rid)
  : Lemma (ensures (includes r tip ==> r=tip \/ includes r (parent tip)))
          [SMTPat (includes r (parent tip))]
  = ()

let root_is_root (s:rid)
  : Lemma (requires (includes s root))
          (ensures (s = root))
          [SMTPat (includes s root)]
  = ()

abstract let extend (r:rid) (n:int) (c:int)
  :Pure rid (requires True) (ensures (fun s -> s `extends` r /\ Cons? (reveal s) /\ Cons?.hd (reveal s) == (c, n) /\ color s == c))
  = elift1 (fun r -> (c, n)::r) r

abstract let extend_monochrome (r:rid) (n:int)
  : Pure rid (requires True) (ensures (fun s -> s `extends` r /\ Cons? (reveal s) /\ Cons?.hd (reveal s) == ((color r), n) /\ color s == color r))
= elift1 (fun r -> ((match r with | [] -> 0 | (c, _) :: _ -> c), n)::r) r
