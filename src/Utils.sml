structure Utils =
struct
  exception UtilsError of string

  (* a * b -> c の関数を a -> b -> c に変換する。 *)
  fun curry f x y = f (x, y)

  (* a -> b -> c の関数を a * b -> c に変換する。 *)
  fun uncurry f (x, y) = f x y

  (* List.find等の高階関数用。カリー化された = である。 *)
  fun eqto x y = (x = y)

  (* ↑の否定バージョン *)
  fun neqto x y = (x <> y)

  (* テキストファイルのファイル名を文字列として与えるとそのファイルの内容を文字列として返す。 *)
  fun fileToString filename =
      let
        val is = TextIO.openIn filename
        fun ftsAux NONE     = ""
          | ftsAux (SOME s) = s ^ ftsAux (TextIO.inputLine is)
        val res = ftsAux (TextIO.inputLine is)
      in
        TextIO.closeIn is;
        res
      end

  (* リストの先頭から各要素をfに引数として渡して、初めてtrueが返ったところでリストを二分する。
     初めてtrueが返った要素（境界の要素）は返り値の2つめのリストの先頭となる。 *)
  fun firstSlice _ [] = ([], [])
    | firstSlice f (x :: xs) = if (f x) then ([], x :: xs) else
        let
          val (nxs, r) = firstSlice f xs
        in
          (x :: nxs, r)
        end

  (* リストの各要素をfに引数として渡して、trueが返った場合はその要素を区切りとしてリストをスライスする。
     trueとなる要素が連続していた場合や始端・終端にあった場合でも、スライス結果に空リストは含まない。 *)
  fun chopList f [] = []
    | chopList f l =
      let
        fun chopListAux f [] = [[]]
          | chopListAux f (x :: xs) =
            let
              val ret = chopListAux f xs
            in
              if (f x) then [] :: ret else (x :: (hd ret)) :: (tl ret)
            end
      in
        List.filter (neqto []) (chopListAux f l)
      end

  (* 文字列を構成する文字が全て大文字ならtrue, そうでなければfalseを返す。 *)
  fun isAllUpper s =
      List.all (fn x => Char.isUpper x) (String.explode s)

  (* =を等価の基準としてxが変化しなくなるまでfを適用する。 *)
  fun repeatApply f x =
      let
        val res = f x
      in
        if res = x then
          x
        else
          repeatApply f res
      end

  (* eqfを等価の基準としてxが変化しなくなるまでfを適用する。 *)
  fun repeatApplyEqf f eqf x =
      let
        val res = f x
      in
        if eqf x res then
          x
        else
          repeatApplyEqf f eqf res
      end

  (* 文字列のリストの各要素の間にsを挟んで連結する。 *)
  fun concatWith _ []        = ""
    | concatWith _ [x]       = x
    | concatWith s (x :: xs) = x ^ s ^ (concatWith s xs)

  (* 文字列とファイル名を与えるとテキストファイルを出力する。 *)
  fun outputFile (stringData, fname) =
      let
        open TextIO
        val strm = openOut fname
      in
        output (strm, stringData);
        closeOut strm
      end

  (* fを要素の等価の基準とし、2つのリストが集合として等しいかどうかを判定する。 *)
  fun eqAsSet _ []        []        = true
    | eqAsSet _ (x :: xs) []        = false
    | eqAsSet _ []        (y :: ys) = false
    | eqAsSet f (x :: xs) yl        =
      let
        val nyl = List.filter (fn z => not (f x z)) yl
        val nxs = List.filter (fn z => not (f x z)) xs
      in
        if
          List.length yl = List.length nyl
        then
          false
        else
          eqAsSet f nxs nyl
      end

  (* fを要素の等価の基準とし、2つのリストが多重集合として等しいかどうかを判定する。 *)
  fun eqAsMset _ []        []        = true
    | eqAsMset _ (x :: xs) []        = false
    | eqAsMset _ []        (y :: ys) = false
    | eqAsMset f (x :: xs) yl =
      let
        fun findAndDrop [] = (false, [])
          | findAndDrop (z :: zs) =
            let
              val (result, restset) = findAndDrop zs
            in
              if
                result
              then
                (true, z :: restset)
              else
                if
                  f x z
                then
                  (true, zs)
                else
                  (false, z :: zs)
            end
        val (res, rs) = findAndDrop yl
      in
        if
          res
        then
          eqAsMset f xs rs
        else
          false
      end

  (* リストの要素を先頭から順にfに引数として渡し、最初にtrueが返されたものを取り除いたリストを返す。
     なければ与えられたリストをそのまま返す。 *)
  fun dropOne f []        = []
    | dropOne f (x :: xs) =
      if
        f x
      then
        xs
      else
        x :: (dropOne f xs)

  (* feqを要素の等価の基準として、リストの要素の重複を解消する。 *)
  fun deleteDouble feq []       = []
    | deleteDouble feq (x :: xs) =
      if
        List.exists (feq x) xs
      then
        deleteDouble feq xs
      else
        x :: (deleteDouble feq xs)

  (* 与えられた文字列を指定した区切り文字列で区切り、文字列のリストにする。
     区切り文字列は先頭から順にマッチする。
     区切り文字列が連続して存在するとその間の空の文字列は無視される。
     与えられた文字列の端に区切り文字列があった場合も始端・終端に空の文字列はないものとする。 *)
  (*
    例：
      tokensS "." "aa.bb..cc"  → ["aa", "bb", "cc"]
      tokensS "bb" "aaabbbccc" → ["aaa", "bccc"]
  *)
  fun tokensS ""        str = List.map String.str (String.explode str)
    | tokensS separator str =
      let
        val lofs = String.size separator
        fun tokensSAux "" ""   = []
          | tokensSAux "" last = [last]
          | tokensSAux s  last =
            if
              String.isPrefix separator s
            then
              last :: (tokensSAux (String.extract (s, lofs, NONE)) "")
            else
              tokensSAux (String.extract (s, 1, NONE)) (last ^ (String.extract (s, 0, SOME 1)))
      in
        List.filter (fn x => (x <> "")) (tokensSAux str "")
      end

  (* mapの逆 1つの対象へ関数のリストを順番に適用した結果を返す。 *)
  fun pam target []        = target
    | pam target (f :: fs) = pam (f target) fs


  (* IntInf.int の累乗。 *)
  fun powerIntinf _ (0 : IntInf.int) = 1 : IntInf.int
    | powerIntinf (x : IntInf.int) (1 : IntInf.int) = x : IntInf.int
    | powerIntinf (x : IntInf.int) (y : IntInf.int) =
      if
        y < 0
      then
        raise UtilsError "the second argument of powerIntInf must be a non-negative number"
      else
        if
          y mod 2 = 0
        then
          let
            val (z : IntInf.int) = powerIntinf x ((y div 2) : IntInf.int)
          in
            (z * z) : IntInf.int
          end
        else
          (x * (powerIntinf x (y - 1))) : IntInf.int

  (* eqfを要素の等価基準とし、2つのリストを集合とみて差集合を返す。 *)
  fun substractionAsSet _   s []        = s
    | substractionAsSet eqf s (x :: xs) = substractionAsSet eqf (List.filter (fn e => not (eqf e x)) s) xs

  (* 2つのリストを集合とみて (重複はないものとする) その直積集合を返す。 *)
  fun directProductAsSet []        _  = []
    | directProductAsSet _         [] = [] (* この行は効率化のため *)
    | directProductAsSet (x :: xs) ys = (List.map (fn y => (x, y)) ys) @ (directProductAsSet xs ys)

  (* eqfを要素の等価基準とし、2つのリストを集合とみて共通部分を返す。 *)
  fun intersectionAsSet _ [] _ = []
    | intersectionAsSet _ _ [] = []
    | intersectionAsSet eqf (x :: xs) ys =
      if
        List.exists (eqf x) ys
      then
        x :: (intersectionAsSet eqf xs ys)
      else
        intersectionAsSet eqf xs ys

  (* intの累乗。 *)
  fun powerInt _ 0 = 1
    | powerInt x 1 = x
    | powerInt x y =
      if
        y < 0
      then
        raise UtilsError "the second argument of powerInt must be a non-negative number"
      else
        if
          y mod 2 = 0
        then
          let
            val z = powerInt x (y div 2)
          in
            z * z
          end
        else
          x * (powerInt x (y - 1))

  (* 自然数を桁数を固定して0を詰めた文字列にする。 *)
  fun intToFixedString 1 x =
      if
        0 <= x andalso x < 10
      then
        Int.toString x
      else
        raise UtilsError "out of range"
    | intToFixedString d x =
      if
        d < 0 orelse x < 0
      then
        raise UtilsError "out of range"
      else
        (intToFixedString (d - 1) (x div 10)) ^ (Int.toString (x mod 10))

  (* =を等価の基準として、第一引数が第二引数のリストの要素であるかを判定する。 *)
  fun isIn element [] = false
    | isIn element (x :: xs) = if x = element then true else isIn element xs

  (* リストの順列を全て列挙する。 *)
  fun perm [] = [[]]
    | perm l = List.concat (List.map (fn x => List.map (fn z => x :: z) (perm (dropOne (eqto x) l))) l)

  (* ファイル名から拡張子を取り除く。 *)
  fun chopExtension str =
      if
        String.isSubstring "." str
      then
        let
          val rchars = rev (String.explode str)
          fun chopC ((#".") :: cs) = cs
            | chopC []             = []
            | chopC (c :: cs)      = chopC cs
          val resc = chopC rchars
        in
          String.implode (rev resc)
        end
      else
        str

  (* ファイル名から拡張子を取り出す。 *)
  fun extractExtension str =
    if
      String.isSubstring "." str
    then
      let
        val rchars = rev (String.explode str)
        fun extractC ((#".") :: _)  = []
          | extractC []             = []
          | extractC (c      :: cs) = c :: (extractC cs)
        val resc = extractC rchars
      in
        String.implode (rev resc)
      end
    else
      ""

  (* リストlの要素を空のグループがないようにn個のグループに分ける全てのパターンを列挙する。
     グループの順番が違うものは区別するが各グループ内の要素の順番が違うものは区別しない。 *)
  fun grouping n l =
    let
      fun makeRange 1 = [1]
        | makeRange m = m :: (makeRange (m - 1))
      val range = makeRange n
      fun groupingAux [] = [[]]
        | groupingAux (e :: es) =
          let
            val next = groupingAux es
          in
            List.concat (List.map (fn xl => List.map (fn k => (e, k) :: xl) range) next)
          end
      fun distribute xl = List.map (fn k => List.map (fn (elem, _) => elem) (List.filter (fn (_, j) => k = j) xl)) range
    in
      if n <= 0 then
        raise UtilsError "the number of group must be a positive number"
      else
        List.filter (fn pat => List.all (fn g => g <> []) pat) (List.map distribute (groupingAux l))
    end

  fun range lower upper =
    if
      lower <= upper
    then
      lower :: (range (lower + 1) upper)
    else
      []

  fun repeatString s 0 = ""
    | repeatString s n =
      if
        n < 0
      then
        raise UtilsError "invalid argument value (minus)"
      else
        (s ^ (repeatString s (n - 1)))


end
