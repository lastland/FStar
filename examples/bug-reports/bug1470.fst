module Bug1470

val length : list 'a -> Dv nat
let rec length l =
  match l with
  | [] -> 0
  | hd::tl -> 1 + length tl

assume val aux (n:int) : Dv nat

let l (n:int) : Dv nat = 1 + aux n
let l1 (n:int) : Dv nat = 1 + (aux n + aux n)
let l2 (n:int) : Dv nat = (1 + aux n) + aux n
