signature BREAL =
sig
  eqtype bReal
  exception NotNaturalNumber
  exception BRealParseError
  val zero : bReal
  val isMinus : bReal -> bool

  val add : bReal -> bReal -> bReal
  val sub : bReal -> bReal -> bReal
  val mul : bReal -> bReal -> bReal

  val compare : bReal * bReal -> order

  val toString : bReal -> string
  val ts : bReal -> string (* 短縮 *)

  val fromIntInf : IntInf.int -> bReal
  val fii : IntInf.int -> bReal (* 短縮 *)

  val fromString : string -> bReal
  val fs : string -> bReal (* 短縮 *)
end

structure BReal :> BREAL =
struct
  type bReal = (IntInf.int) * int

  exception NotNaturalNumber
  exception BRealParseError

  fun symplifyDecimal ((x, d) : bReal) =
      if x mod 10 <> 0 orelse d = 0 then
        (x, d) : bReal
      else
        symplifyDecimal (x div 10, d - 1)

  fun add ((x1, d1) : bReal) ((x2, d2) : bReal) =
      if d1 = d2 then
        symplifyDecimal ((x1 + x2, d1) : bReal)
      else
        if d1 > d2 then
          symplifyDecimal (x1 + x2 * (IntInf.pow (10, (d1 - d2))), d1)
        else
          symplifyDecimal (add (x2, d2) (x1, d1))

  fun sub ((x1, d1) : bReal) ((x2, d2) : bReal) = symplifyDecimal (add (x1, d1) (x2 * (~ 1 : IntInf.int), d2))

  fun mul ((x1, d1) : bReal) ((x2, d2) : bReal) = symplifyDecimal ((x1 * x2, d1 + d2) : bReal)

  fun compare (a, b) = let val (x, d) = sub a b in IntInf.compare (x, 0) end

  fun toString ((x, d) : bReal) =
      let
        val dstr = IntInf.toString x
        fun mulstr s n = if n < 0 then raise NotNaturalNumber else if n = 0 then "" else s ^ (mulstr s (n - 1))
        val allstr = if String.size dstr <= d then (mulstr "0" (d - String.size dstr + 1)) ^ dstr else dstr
        val length = String.size allstr
        val ret = String.extract (allstr, 0, SOME (length - d)) ^ "." ^ String.extract (allstr, length - d, NONE)
      in
        if d = 0 then
          ret ^ "0"
        else
          ret
      end
  val ts = toString

  fun fromIntInf x = ((x, 0) : bReal)
  val fii = fromIntInf

  (* 小数点省略不可 *)
  fun fromString str =
      let
        val dlst = String.tokens (Utils.eqto #".") str
      in
        case dlst of
          [a, b] => symplifyDecimal ((valOf (IntInf.fromString (a ^ b)), String.size b) : bReal)
        |  _ => raise BRealParseError
      end
  val fs = fromString

  val zero = fromString "0.0"

  fun isMinus x = compare (x, zero) = LESS

end


infix 6 `+
fun (a:BReal.bReal) `+ (b:BReal.bReal) = BReal.add a b
infix 6 `-
fun (a:BReal.bReal) `- (b:BReal.bReal) = BReal.sub a b
infix 7 `*
fun (a:BReal.bReal) `* (b:BReal.bReal) = BReal.mul a b
infix 4 `=
fun (a:BReal.bReal) `= (b:BReal.bReal) = (a = b)
infix 4 `<>
fun (a:BReal.bReal) `<> (b:BReal.bReal) = (a <> b)
infix 4 `<
fun (a:BReal.bReal) `< (b:BReal.bReal) = (BReal.compare (a, b) = LESS)
infix 4 `<=
fun (a:BReal.bReal) `<= (b:BReal.bReal) = (a `< b) orelse (a `= b)
infix 4 `>
fun (a:BReal.bReal) `> (b:BReal.bReal) = not (a `<= b)
infix 4 `>=
fun (a:BReal.bReal) `>= (b:BReal.bReal) = not (a `< b)

