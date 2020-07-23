datatype 'a list = Cons of 'a | Nil;

fun append x xs = x::xs
  | append x []   = x::[]

val x = 10

datatype 'a option = None | Some of 'a

fun >>= ((Some x), f) = f x 
  | >>= (None  , f) = None

infixr 3 >>=

val x = (Some 10) >>= (fn x => Some x);

val rand = primitive "Int.random" : unit -> int

val u = case x of 
  | Some x => x
  | None => rand ()
  end

fun main x y z = {x = x, y = y::z}

val q = fn x => Some x;

val _ = main true 1 nil;
