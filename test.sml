datatype 'a list = Cons of 'a | Nil;

fun append x xs = x::xs
  | append x []   = x::[]

val x = 10;

datatype 'a option = None | Some of 'a



val bool_to_int = fn x => if x then 1 else 0;
datatype 'a list = :: of 'a | nil; 

val _ = let val y = 10 in y end;
