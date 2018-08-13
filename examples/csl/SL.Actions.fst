module SL.Actions

open SL.Heap
open SL.Effect

let (<|) f x = f x

type sref = (a:Type & ref a)
let refs = list sref

let tosref #a (r : ref a) : sref = Mkdtuple2 a r

let with_fp (fp : refs) (x:'a) : 'a = x

let with_fp_lemma fp x : Lemma (with_fp fp x == x) [SMTPat (with_fp fp x)] = ()

let lift_div_st (a:Type) (wp:pure_wp a) (p:post a) (m:memory) = wp (fun a -> p a m)
sub_effect DIV ~> STATE = lift_div_st

let read_wp (#a:Type) (r:ref a) : st_wp a =
    (fun post m0 -> exists (x:a). m0 == (r |> x) /\ post x m0)

unfold
let frame_read_wp (#a:Type) (r:ref a) : st_wp a =
   fun post m0 -> frame_wp (read_wp r) (frame_post post) m0

assume
val ( ! ) (#a:Type) (r:ref a)
  :STATE a (with_fp [tosref r] <| frame_read_wp r)

let write_wp (#a:Type) (r:ref a) (v:a) : st_wp unit =
  (fun post m0 -> exists (x:a). m0 == (r |> x) /\ post () (r |> v))

unfold
let frame_write_wp (#a:Type) (r:ref a) (v:a) : st_wp unit =
   fun post m0 -> frame_wp (write_wp r v) (frame_post post) m0

assume
val ( := ) (#a:Type) (r:ref a) (v:a)
  :STATE unit (with_fp [tosref r] <| frame_write_wp r v)
