structure Commutative =
struct
    (* 集合演算の * は可換ではないため無視 *)
    fun makeCommutative (origin as (BE_Node2 (SOME (BT_Power tp), Keyword "*", _, _))) = origin
      | makeCommutative (origin as (BE_Node2 (NONE,               Keyword "*", _, _))) = origin
      | makeCommutative (BE_Node2 (tp, Keyword tk, e1, e2)) =
        if
          List.exists (Utils.eqto tk) ["+", "&", "or", "\\/", "/\\", "*"] (* 可換結合演算子 *)
        then
          BE_Commutative (tp, Keyword tk, [e1, e2])
        else
          BE_Node2 (tp, Keyword tk, e1, e2)
      | makeCommutative x = x

    fun flattenCommutative (BE_Commutative (_,  _, [e])) = e
      | flattenCommutative (BE_Commutative (tp, Keyword tk, l)) = 
        let
          fun fcAux [] = []
            | fcAux ((BE_Commutative (tpS, Keyword tkS, lS)) :: r) =
              if
                tk = tkS
              then
                lS @ (fcAux r)
              else
                (BE_Commutative (tpS, Keyword tkS, lS)) :: (fcAux r)
            | fcAux (x :: xs) = x :: (fcAux xs)
        in
          BE_Commutative (tp, Keyword tk, fcAux l)
        end
      | flattenCommutative e = e
end
