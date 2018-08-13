module SL.Actions

open SL.Heap
open SL.Effect

let lift_div_st (a:Type) (wp:pure_wp a) (p:post a) (m:memory) = wp (fun a -> p a m)
sub_effect DIV ~> STATE = lift_div_st

let read_wp (#a:Type) (r:ref a) : st_wp a =
    (fun post m0 -> exists (x:a). m0 == (r |> x) /\ post x m0)

unfold
let frame_read_wp (#a:Type) (r:ref a) : st_wp a =
   fun post m0 -> frame_wp (with_fp [tosref r] <| read_wp r) (frame_post post) m0

assume
val ( ! ) (#a:Type) (r:ref a)
  :STATE a (frame_read_wp r)

let write_wp (#a:Type) (r:ref a) (v:a) : st_wp unit =
  (fun post m0 -> exists (x:a). m0 == (r |> x) /\ post () (r |> v))

unfold
let frame_write_wp (#a:Type) (r:ref a) (v:a) : st_wp unit =
   fun post m0 -> frame_wp (with_fp [tosref r] <| write_wp r v) (frame_post post) m0

assume
val ( := ) (#a:Type) (r:ref a) (v:a)
  :STATE unit (frame_write_wp r v)
