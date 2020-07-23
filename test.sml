datatype 'a list = :: of 'a | nil;

fun append x xs = x::xs
  | append x []   = 10

val x = 10

datatype 'a option = None | Some of 'a

fun >>= ((Some x), f) = f x 
  | >>= (None  , f) = None

val x = >>=