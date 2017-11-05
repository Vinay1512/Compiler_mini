signature ORD =
sig

type t

val le : t -> t -> bool

end

structure IntOrd : ORD =
struct

type t = int
val le = (op <=)
fun le (a,b) = if a <= b then true else false

end


