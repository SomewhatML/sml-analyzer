datatype 'a list = Cons of 'a | Nil;

fun append x xs = x::xs
  | append x []   = x::[]

val x = 10

datatype 'a option = None | Some of 'a

fun >>= ((Some x), f) = f x 
  | >>= (None  , f) = None

val x = >>= :: nil;

val y = true;
val x = let val _ = 1::y::nil in 10 end;

val y = 10;
val _ = append 1 y;