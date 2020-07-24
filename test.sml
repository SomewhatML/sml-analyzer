fun append x xs = x::xs
  | append x []   = x::[]

val x = 10;

datatype u = U of int;

type t = {x:int, y:int}
