structure Match =
struct
  (* マッチング結果として規則内の変数を表すときに使うデータ構造 *)
  datatype TRSVar = TRSV of (BType option * BToken)

  exception MatchError of string

  (* 規則と対象の型の整合をtrue/falseで返す。 *)
  fun matchType ruletypeOpt targettypeOpt =
      (case (ruletypeOpt, targettypeOpt) of
          (NONE   ,                         _)                               => true
        | (SOME _ ,                         NONE)                            => false
        | (SOME (BT_Power t1Opt),           SOME (BT_Power t2Opt))           => matchType t1Opt t2Opt
        | (SOME (BT_Pair (t11Opt, t12Opt)), SOME (BT_Pair (t21Opt, t22Opt))) => (matchType t11Opt t21Opt) andalso (matchType t12Opt t22Opt)
        | (SOME t1,                         SOME t2)                         => t1 = t2
      )

  (* 適用対象の式どうしを比較する際に用いる *)
  fun eqKnownTypes NONE _ = false
    | eqKnownTypes _ NONE = false
    | eqKnownTypes (SOME x) (SOME y) = (x = y)

  (* 型を考慮する式の等価性判定 *)
  (* 適用対象どうしの比較 *)
  fun eqExprsWithTypes e1 e2 =
      let
        val to1 = TypeInference.typeOf e1
        val to2 = TypeInference.typeOf e2
      in
        eqKnownTypes to1 to2 andalso
        AST.eqExprs e1 e2
      end

  fun isLiteral (BE_Leaf (_, IntegerLiteral _)) = true
    | isLiteral (BE_Leaf (_, StringLiteral  _)) = true
    | isLiteral (BE_Leaf (_, RealLiteral    _)) = true
    | isLiteral _ = false

  fun isTypeSetByType (BE_Leaf (_, Keyword "INTEGER")) = true
    | isTypeSetByType (BE_Leaf (_, Keyword "BOOL"   )) = true
    | isTypeSetByType (BE_Leaf (_, Keyword "REAL"   )) = true
    | isTypeSetByType (BE_Leaf (_, Keyword "FLOAT"  )) = true
    | isTypeSetByType (BE_Leaf (_, Keyword "STRING" )) = true
    | isTypeSetByType (BE_Leaf (SOME (BT_Power (SOME (BT_Deferred typeName ))), Var identifier)) = (typeName = identifier)
    | isTypeSetByType (BE_Leaf (SOME (BT_Power (SOME (BT_Enum (typeName, _)))), Var identifier)) = (typeName = identifier)
    | isTypeSetByType (BE_Node1 (_, Keyword "POW", e)) = isTypeSetByType e
    | isTypeSetByType (BE_Node2 (SOME (BT_Power _), Keyword "*", e1, e2)) = isTypeSetByType e1 andalso isTypeSetByType e2
    | isTypeSetByType _ = false

  fun eqAsPatternVar (Var x)         (Var y) = x = y
    | eqAsPatternVar (VarLit x)     (VarLit y) = x = y
    | eqAsPatternVar (VarTypeSet x) (VarTypeSet y) = x = y
    | eqAsPatternVar (VarSingle x)  (VarSingle y) = x = y
    | eqAsPatternVar (Var x)        (VarSingle y) =
      let
        val body = String.rev (String.extract (String.rev y, 1, NONE))
      in
        x = body
      end
    | eqAsPatternVar (VarSingle x) (Var y) = eqAsPatternVar (Var y) (VarSingle x)
    | eqAsPatternVar _ _ = false

  (* 2つのマッチング結果をマージする。整合しなければNONEを返す。 *)
  fun mergeTrsv [] l = SOME l
    | mergeTrsv ((TRSV (tp1Opt, v1), e1) :: vs) l =
      let
        val samePatternOpt = List.find (fn (TRSV (_, v2), _) => eqAsPatternVar v1 v2) l
      in
        case samePatternOpt of
          NONE => mergeTrsv vs ((TRSV (tp1Opt, v1), e1) :: l)
        | (SOME (_, e2)) => if eqExprsWithTypes e1 e2 then mergeTrsv vs l else NONE
      end

  (* マッチング候補のリスト2つから整合するものをマージしてリストにする。 *)
  fun mergeTrsvCandidates [] l2 = []
    | mergeTrsvCandidates l1 [] = []
    | mergeTrsvCandidates l1 l2 =
      let
        fun mtcAux [] tl2 = []
          | mtcAux (t1 :: ts1) tl2 =
            let
              val res = List.map valOf (List.filter (Utils.neqto NONE) (List.map (mergeTrsv t1) tl2))
            in
              res @ (mtcAux ts1 tl2)
            end
      in
        mtcAux l1 l2
      end

  fun localVarsPerm vl1 vl2 =
      let
        val p2 = Utils.perm vl2
        val vl1trsv = List.map (fn v => TRSV (NONE, v)) vl1
        val l = List.map (fn vs2 => ListPair.mapEq (fn (trsv, v2) => (trsv, BE_Leaf (NONE, v2))) (vl1trsv, vs2)) p2
      in
        case l of [] => NONE | _ => SOME l
      end

  (* 式と式のマッチング *)
  (* マッチングできた場合その各候補（(TrsVar * BExpr) list）をリストにしてSOMEに包んで返す。
  マッチング失敗時はNONEを返す *)
  fun matchExpr (BE_Leaf (tp1Opt, (VarSingle x))) e =
      if
        matchType tp1Opt (TypeInference.typeOf e)
      then
        SOME [[(TRSV (tp1Opt, VarSingle x), e)]]
      else
        NONE

    | matchExpr (BE_Leaf (tp1Opt, (Var x))) e =
      if
        matchType tp1Opt (TypeInference.typeOf e)
      then
        SOME [[(TRSV (tp1Opt, Var x), e)]]
      else
        NONE

    | matchExpr (BE_Leaf (tp1Opt, VarLit x)) e =
      if
        matchType tp1Opt (TypeInference.typeOf e) andalso
        isLiteral e
      then
        SOME [[(TRSV (tp1Opt, VarLit x), e)]]
      else
        NONE

    | matchExpr (BE_Leaf (tp1Opt, VarTypeSet x)) e =
      if
        matchType tp1Opt (TypeInference.typeOf e) andalso
        isTypeSetByType e
      then
        SOME [[(TRSV (tp1Opt, VarTypeSet x), e)]]
      else
        NONE

    | matchExpr (BE_Leaf (tp1Opt, tk1)) (BE_Leaf (tp2Opt, tk2)) =
      if
        (matchType tp1Opt tp2Opt) andalso (tk1 = tk2)
      then
        SOME [[]]
      else
        NONE

    | matchExpr (BE_Node1 (tp1Opt, tk1, e1)) (BE_Node1 (tp2Opt, tk2, e2)) =
      if
        (matchType tp1Opt tp2Opt) andalso (tk1 = tk2)
      then
        matchExpr e1 e2
      else
        NONE

    | matchExpr (BE_Node2 (_, Keyword "=", e11, e12)) (BE_Node2 (_, Keyword "=", e21, e22)) =
      let
        val p1 = case matchExpr e11 e21 of NONE => [] | SOME l => l
        val p2 = case matchExpr e12 e22 of NONE => [] | SOME l => l
        val res12 = mergeTrsvCandidates p1 p2
        val p3 = case matchExpr e11 e22 of NONE => [] | SOME l => l
        val p4 = case matchExpr e12 e21 of NONE => [] | SOME l => l
        val res34 = mergeTrsvCandidates p3 p4
        val res = Utils.deleteDouble Utils.eqto (res12 @ res34)
      in
        if res = [] then NONE else SOME res
      end


    | matchExpr (BE_Node2 (tp1Opt, tk1, e11, e12)) (BE_Node2 (tp2Opt, tk2, e21, e22)) =
      if
        (matchType tp1Opt tp2Opt) andalso (tk1 = tk2)
      then
        let
          val p1 = case matchExpr e11 e21 of NONE => [] | SOME l => l
          val p2 = case matchExpr e12 e22 of NONE => [] | SOME l => l
          val res = mergeTrsvCandidates p1 p2
        in
          if res = [] then NONE else SOME res
        end
      else
        NONE

    | matchExpr (BE_NodeN (tp1Opt, tk1, es1)) (BE_NodeN (tp2Opt, tk2, es2)) =
      if
        (matchType tp1Opt tp2Opt) andalso (tk1 = tk2) andalso (List.length es1 = List.length es2) andalso
        (
          ListPair.all (fn (e1, e2) => matchExpr e1 e2 <> NONE) (es1, es2)
        )
      then
        let
          val unwrapped = ListPair.map (fn (e1, e2) => valOf (matchExpr e1 e2)) (es1, es2)
          val allmerged = List.foldl (fn (ts1, ts2) => mergeTrsvCandidates ts1 ts2) (hd unwrapped) (tl unwrapped)
        in
          if allmerged = [] then NONE else SOME allmerged
        end
      else
        NONE

    | matchExpr (BE_Fnc (tp1Opt, e11, e12)) (BE_Fnc (tp2Opt, e21, e22)) =
      if
        matchType tp1Opt tp2Opt
      then
        let
          val p1 = case matchExpr e11 e21 of NONE => [] | SOME l => l
          val p2 = case matchExpr e12 e22 of NONE => [] | SOME l => l
          val res = mergeTrsvCandidates p1 p2
        in
          if res = [] then NONE else SOME res
        end
      else
        NONE
    | matchExpr (BE_Img (tp1Opt, e11, e12)) (BE_Img (tp2Opt, e21, e22)) =
      matchExpr (BE_Fnc (tp1Opt, e11, e12)) (BE_Fnc (tp2Opt, e21, e22))

    | matchExpr (BE_Bool (BP e1)) (BE_Bool (BP e2)) = matchExpr e1 e2
    | matchExpr (BE_ExSet (tp1Opt, es1)) (BE_ExSet (tp2Opt, es2)) =
      if
        (matchType tp1Opt tp2Opt) andalso (List.length es1 = List.length es2)
      then
        let
          fun matchExprAux [] l = SOME [[]]
            | matchExprAux (x :: xs) l =
              let
                val unwrapped = List.map
                  valOf
                  (List.filter
                    (Utils.neqto NONE)
                    (List.map
                      (fn y =>
                          case matchExpr x y of
                            NONE => NONE
                          | SOME r1 =>
                            case matchExprAux xs (Utils.dropOne (Utils.eqto y) l) of
                              NONE => NONE
                            | SOME r2 =>
                              case mergeTrsvCandidates r1 r2 of
                                [] => NONE
                              | r3 => SOME r3)
                      l))
              in
                if
                  unwrapped = []
                then
                  NONE
                else
                  let
                    val allmerged = Utils.deleteDouble Utils.eqto (List.concat unwrapped)
                   in
                    case allmerged of [] => NONE | xxx => SOME xxx
                  end
              end
        in
          matchExprAux es1 es2
        end
      else
        NONE

    | matchExpr (BE_InSet (tp1Opt, tks1, BP e1)) (BE_InSet (tp2Opt, tks2, BP e2)) =
      if
        matchType tp1Opt tp2Opt
      then
        matchExpr (BE_Exists (tks1, BP e1)) (BE_Exists (tks2, BP e2))
      else
        NONE

    | matchExpr (BE_ForAll (tks1, BP e11, BP e12)) (BE_ForAll (tks2, BP e21, BP e22)) =
      if
        List.length tks1 = List.length tks2
      then
        let
          val pe1 = case matchExpr e11 e21 of NONE => [] | SOME l => l
          val pe2 = case matchExpr e12 e22 of NONE => [] | SOME l => l
          val pv = case localVarsPerm tks1 tks2 of NONE => [] | SOME l => l
          val resOpt = case (mergeTrsvCandidates pe1 pe2) of [] => NONE | l => (case mergeTrsvCandidates l pv of [] => NONE | r => SOME r)
        in
          resOpt
        end
      else
        NONE

    | matchExpr (expr1 as BE_Exists (tks1, BP e1)) (expr2 as BE_Exists (tks2, BP e2)) =
      if
        List.length tks1 = List.length tks2
      then
        let
          val pe = case matchExpr e1 e2 of NONE => [] | SOME l => l
          val pv = case localVarsPerm tks1 tks2 of NONE => [] | SOME l => l
          val res = mergeTrsvCandidates pe pv
        in
          if res = [] then NONE else SOME res
        end
      else
        NONE

    | matchExpr (BE_Lambda (tp1Opt, tks1, BP e11, e12)) (BE_Lambda (tp2Opt, tks2, BP e21, e22)) =
      if
        matchType tp1Opt tp2Opt
      then
        matchExpr (BE_ForAll (tks1, BP e11, BP e12)) (BE_ForAll (tks2, BP e21, BP e22))
      else
        NONE

    | matchExpr (BE_Sigma (tp1Opt, tk1,  BP e11, e12)) (BE_Sigma (tp2Opt, tk2,  BP e21, e22)) =
        matchExpr (BE_Lambda (tp1Opt, [tk1], BP e11, e12)) (BE_Lambda (tp2Opt, [tk2], BP e21, e22))

    | matchExpr (BE_Pi    (tp1Opt, tk1,  BP e11, e12)) (BE_Pi    (tp2Opt, tk2,  BP e21, e22)) =
        matchExpr (BE_Lambda (tp1Opt, [tk1], BP e11, e12)) (BE_Lambda (tp2Opt, [tk2], BP e21, e22))

    | matchExpr (BE_Inter (tp1Opt, tks1, BP e11, e12)) (BE_Inter (tp2Opt, tks2, BP e21, e22)) =
        matchExpr (BE_Lambda (tp1Opt, tks1,  BP e11, e12)) (BE_Lambda (tp2Opt, tks2,  BP e21, e22))

    | matchExpr (BE_Union (tp1Opt, tks1, BP e11, e12)) (BE_Union (tp2Opt, tks2, BP e21, e22)) =
        matchExpr (BE_Lambda (tp1Opt, tks1,  BP e11, e12)) (BE_Lambda (tp2Opt, tks2,  BP e21, e22))

    | matchExpr (BE_Struct (to1, l1)) (BE_Struct (to2, l2)) =
      if
        to1 <> NONE andalso
        to1 = to2 andalso
        List.length l1 = List.length l2 andalso
(*        ListPair.allEq (fn ((str1, _), (str2, _)) => str1 = str2) (l1, l2) andalso *) (* 型に不明な部分がある場合は弾く *)
        ListPair.allEq (fn ((_, e1), (_, e2)) => matchExpr e1 e2 <> NONE) (l1, l2)
      then
        let
          val unwrapped = ListPair.map (fn ((_, e1), (_, e2)) => valOf (matchExpr e1 e2)) (l1, l2)
          val allmerged = List.foldl (fn (ts1, ts2) => mergeTrsvCandidates ts1 ts2) (hd unwrapped) (tl unwrapped)
        in
          if allmerged = [] then NONE else SOME allmerged
        end
      else
        NONE

    | matchExpr (BE_Rec (to1, l1)) (BE_Rec (to2, l2)) =
      if
        matchType to1 to2 andalso
        List.length l1 = List.length l2 andalso
        ListPair.allEq (fn ((_, e1), (_, e2)) => matchExpr e1 e2 <> NONE) (l1, l2)
      then
        let
          val unwrapped = ListPair.map (fn ((_, e1), (_, e2)) => valOf (matchExpr e1 e2)) (l1, l2)
          val allmerged = List.foldl (fn (ts1, ts2) => mergeTrsvCandidates ts1 ts2) (hd unwrapped) (tl unwrapped)
        in
          if allmerged = [] then NONE else SOME allmerged
        end
      else
        NONE
    | matchExpr (BE_RcAc (to1, e1, str1)) (BE_RcAc (to2, e2, str2)) =
      if
        matchType to1 to2 andalso
        str1 = str2
      then
        matchExpr e1 e2
      else
        NONE
    | matchExpr (BE_Commutative (tp1Opt, tk1, el1)) (BE_Commutative (tp2Opt, tk2, el2)) =
      if
        (matchType tp1Opt tp2Opt) andalso (tk1 = tk2) andalso (List.length el1 <= List.length el2)
      then
        if
          List.length el1 = List.length el2
        then
          (* オペランドの個数が等しい場合は制限付き変数か否かに関わらず1個のオペランドが1個のオペランドにマッチする。 *)
          case matchExprAuxC el1 el2 of
            NONE   => NONE
          | SOME l => SOME (List.map (fn (res, []) => res | _ => (raise MatchError "")) l)
        else
          (* オペランドの個数が異なる場合 *)
          if
            List.exists (fn (BE_Leaf (_, Var _)) => true | _ => false) el1
          then
            (* オペランドの個数が異なりパターン側に通常変数（任意個のオペランドとマッチする）が存在した場合 *)
            let
              (* 規則側のオペランドを通常変数とそうでないものに分ける。 *)
              val (patternExtendedVars, patternOthers) = List.partition (fn (BE_Leaf (_, Var _)) => true  | _ => false) el1
              (* 通常の変数でないオペランドのマッチングを行う。 *)
              val partialMatch = matchExprAuxC patternOthers el2
            in
              if
                partialMatch = NONE
              then
                NONE
              else
                let
                  (* 通常変数以外の部分的マッチング候補と残りのオペランドの組のリスト *)
                  val partialMatchVal = valOf partialMatch

                  (* 通常変数の個数 *)
                  val numberOfExtendedVars = List.length patternExtendedVars

                  (* 部分的マッチング候補と残りのオペランドのリストの組を引数として受け取り、通常変数も含めたマッチング候補を返す関数 *)
                  fun matchExtendedVars (partialMatchResult, rest) =
                      let
                        (* マッチング対象の残りのオペランドを通常変数の個数にグループ分けする方法を全パターン列挙する。 *)
                        val groupPatterns = Utils.grouping numberOfExtendedVars rest
                        (* それぞれのグループ分けパターンに対してマッチングを行う。 *)
                        val restMatchResult =
                              List.map (fn groups => ListPair.map (fn ((BE_Leaf (to, Var vn)), [singleOperand]) => (TRSV (to, Var vn), singleOperand)
                                                                    | ((BE_Leaf (to, Var vn)), group)           => (TRSV (to, Var vn), BE_Commutative (to, tk1, group))
                                                                    | _ => raise MatchError "expected a extended variable but other type of token is given")
                                                                   (patternExtendedVars, groups))
                                       groupPatterns
                      in
                        mergeTrsvCandidates [partialMatchResult] restMatchResult
                      end
                  val res = List.concat (List.map matchExtendedVars partialMatchVal)
                in
                  case res of
                    [] => NONE
                  | _ => SOME res
                end
            end
          else
            (* オペランドの個数が異なり、通常変数が存在しなかった場合、マッチングは失敗する。 *)
            NONE
      else
        NONE
    | matchExpr _ _ = NONE

  and
      mergeTrsvC [] (l, oos) = SOME (l, oos)
    | mergeTrsvC ((TRSV (tp1Opt, v1), e1) :: vs) (l, oos) =
      let
        val samePatternOpt = List.find (fn (TRSV (_, v2), _) => eqAsPatternVar v1 v2) l
      in
        case samePatternOpt of
          NONE => mergeTrsvC vs (((TRSV (tp1Opt, v1), e1) :: l), oos)
        | (SOME (_, e2)) => if eqExprsWithTypes e1 e2 then mergeTrsvC vs (l, oos) else NONE
      end

  and
      mergeTrsvCandidatesC [] l2 = []
    | mergeTrsvCandidatesC l1 [] = []
    | mergeTrsvCandidatesC l1 l2 =
      let
        fun mtcAux [] tl2 = []
          | mtcAux (t1 :: ts1) tl2 =
            let
              val res = List.map valOf (List.filter (Utils.neqto NONE) (List.map (mergeTrsvC t1) tl2))
            in
              res @ (mtcAux ts1 tl2)
            end
      in
        mtcAux l1 l2
      end
  and
    matchExprAuxC [] l = SOME [([], l)]
    | matchExprAuxC (x :: xs) l =
      let
        val unwrapped = List.map
          valOf
          (List.filter
            (Utils.neqto NONE)
            (List.map
              (fn y =>
                  case matchExpr x y of
                    NONE => NONE
                  | SOME r1 =>
                    case matchExprAuxC xs (Utils.dropOne (Utils.eqto y) l) of
                      NONE => NONE
                    | SOME rc2 =>
                      case mergeTrsvCandidatesC r1 rc2 of
                        [] => NONE
                      | rc3 => SOME rc3)
              l))
      in
        if
          unwrapped = []
        then
          NONE
        else
          let
            val allmerged = Utils.deleteDouble Utils.eqto (List.concat unwrapped)
            (* List.foldl (fn (ts1, ts2) => mergeTrsvCandidates ts1 ts2) (hd unwrapped) (tl unwrapped) *)
          in
            case allmerged of [] => NONE | xxx => SOME xxx
          end
      end

    (* マッチング結果による変数の書き換え *)
  fun rewriteVar ((TRSV (tp1Opt, v1), pattern) :: l) (BE_Leaf (_, v2)) = if eqAsPatternVar v1 v2 then pattern else rewriteVar l (BE_Leaf (NONE, v2))

    (* 書き換え対象の変数を書き換えられなかった（書き換え前のパターンに存在しない変数が書き換え後のパターンに出現している）場合 *)
    | rewriteVar [] (BE_Leaf (_, Var        x)) = raise MatchError "invalid rule"
    | rewriteVar [] (BE_Leaf (_, VarLit     _)) = raise MatchError "invalid rule"
    | rewriteVar [] (BE_Leaf (_, VarSingle  _)) = raise MatchError "invalid rule"
    (* VarTypeSet は例外的に書き換え後のみに出現可能 *)

    (* 第二引数が書き換え対象の変数でないとき *)
    | rewriteVar _ e = e

  fun rewriteExpr [] e = e
    | rewriteExpr ((pattern1, pattern2) :: rls) target =
      case matchExpr pattern1 target of
        NONE => rewriteExpr rls target
      | SOME l => if AST.eqExprs pattern1 pattern2 then target else (AST.mapExprTree (rewriteVar (hd l)) pattern2) handle _ => raise MatchError (Stringify.exprToString pattern1)
      (* rewriteVar (hd l) の部分ではマッチングに成功した書き換え規則のうち1つしか適用しないことを表している。
         遅延評価を用いると他の候補にかかる計算コストを削減できる可能性がある *)

  fun rewriteVarTypeSet (BE_Leaf (SOME (BT_Power tOpt), VarTypeSet _)) = TypeInference.typeToExpr tOpt
    | rewriteVarTypeSet e = e

end

