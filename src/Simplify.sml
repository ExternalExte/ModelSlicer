(*
#未実装の規則
  ## 変換
    - floor
    - ceiling
*)

structure Simplify =
struct
exception SimplifyError of string

(* simplifyは外部から直接使わないこと
  (一度符号成分をリテラルのデータ内に押し込めるため) *)

    (* 整数リテラル + 整数リテラル *)
fun simplify (BE_Node2 (SOME BT_Integer, Keyword "+", BE_Leaf (_, IntegerLiteral e1val), BE_Leaf (_, IntegerLiteral e2val))) =
    BE_Leaf (SOME BT_Integer, IntegerLiteral (e1val + e2val))
   
    (* 実数リテラル + 実数リテラル *)
  | simplify (BE_Node2 (SOME BT_Real, Keyword "+", BE_Leaf (_, RealLiteral e1val), BE_Leaf (_, RealLiteral e2val))) =
    BE_Leaf (SOME BT_Real, RealLiteral (e1val `+ e2val))
    
    (* 整数リテラル - 整数リテラル *)
  | simplify (BE_Node2 (SOME BT_Integer, Keyword "-", BE_Leaf (_, IntegerLiteral e1val), BE_Leaf (_, IntegerLiteral e2val))) =
    BE_Leaf (SOME BT_Integer, IntegerLiteral (e1val - e2val))

    (* 実数リテラル - 実数リテラル *)
  | simplify (BE_Node2 (SOME BT_Real, Keyword "-", BE_Leaf (_, RealLiteral e1val), BE_Leaf (_, RealLiteral e2val))) =
    BE_Leaf (SOME BT_Real, RealLiteral (e1val `- e2val))

    (* 整数リテラル * 整数リテラル *)
  | simplify (BE_Node2 (SOME BT_Integer, Keyword "*", BE_Leaf (_, IntegerLiteral e1val), BE_Leaf (_, IntegerLiteral e2val))) =
    BE_Leaf (SOME BT_Integer, IntegerLiteral (e1val * e2val))

    (* 実数リテラル * 実数リテラル *)
  | simplify (BE_Node2 (SOME BT_Real, Keyword "*", BE_Leaf (_, RealLiteral e1val), BE_Leaf (_, RealLiteral e2val))) =
    BE_Leaf (SOME BT_Real, RealLiteral (e1val `* e2val))

    (* 整数リテラル ** 整数リテラル *)
  | simplify (BE_Node2 (_, Keyword "**", BE_Leaf (_, IntegerLiteral e1val), BE_Leaf (_, IntegerLiteral e2val))) =
    BE_Leaf (SOME BT_Integer, IntegerLiteral (Utils.powerIntinf e1val e2val))

    (* 整数リテラル + 整数リテラル (可換) *)
  | simplify (BE_Commutative (SOME BT_Integer, Keyword "+", el)) =
    let
      val litOperands = List.filter (fn (BE_Leaf (_, IntegerLiteral _)) => true | _ => false) el
      val nonlitOperands = List.filter (fn (BE_Leaf (_, IntegerLiteral _)) => false | _ => true) el
      val lite = List.foldl (fn (BE_Leaf (_, IntegerLiteral x), BE_Leaf (_, IntegerLiteral y)) => BE_Leaf (SOME BT_Integer, IntegerLiteral (x + y)) | _ => raise SimplifyError "INTEGER + expression") (BE_Leaf (SOME BT_Integer, IntegerLiteral 0)) litOperands
    in
      BE_Commutative (SOME BT_Integer, Keyword "+", (if litOperands = [] then nonlitOperands else (lite :: nonlitOperands)))
    end
  
    (* 実数リテラル + 実数リテラル (可換) *)
  | simplify (BE_Commutative (SOME BT_Real, Keyword "+", el)) =
    let
      val litOperands = List.filter (fn (BE_Leaf (_, RealLiteral _)) => true | _ => false) el
      val nonlitOperands = List.filter (fn (BE_Leaf (_, RealLiteral _)) => false | _ => true) el
      val lite = List.foldl (fn (BE_Leaf (_, RealLiteral x), BE_Leaf (_, RealLiteral y)) => BE_Leaf (SOME BT_Real, RealLiteral (x `+ y)) | _ => raise SimplifyError "REAL + expression") (BE_Leaf (SOME BT_Real, RealLiteral BReal.zero)) litOperands
    in
      BE_Commutative (SOME BT_Real, Keyword "+", (if litOperands = [] then nonlitOperands else (lite :: nonlitOperands)))
    end

    (* 整数リテラル * 整数リテラル (可換) *)
  | simplify (BE_Commutative (SOME BT_Integer, Keyword "*", el)) =
    let
      val litOperands = List.filter (fn (BE_Leaf (_, IntegerLiteral _)) => true | _ => false) el
      val nonlitOperands = List.filter (fn (BE_Leaf (_, IntegerLiteral _)) => false | _ => true) el
      val lite = List.foldl (fn (BE_Leaf (_, IntegerLiteral x), BE_Leaf (_, IntegerLiteral y)) => BE_Leaf (SOME BT_Integer, IntegerLiteral (x * y)) | _ => raise SimplifyError "INTEGER * expression") (BE_Leaf (SOME BT_Integer, IntegerLiteral 1)) litOperands
    in
      BE_Commutative (SOME BT_Integer, Keyword "*", (if litOperands = [] then nonlitOperands else (lite :: nonlitOperands)))
    end

    (* 実数リテラル * 実数リテラル (可換) *)
  | simplify (BE_Commutative (SOME BT_Real, Keyword "*", el)) =
    let
      val litOperands = List.filter (fn (BE_Leaf (_, RealLiteral _)) => true | _ => false) el
      val nonlitOperands = List.filter (fn (BE_Leaf (_, RealLiteral _)) => false | _ => true) el
      val lite = List.foldl (fn (BE_Leaf (_, RealLiteral x), BE_Leaf (_, RealLiteral y)) => BE_Leaf (SOME BT_Real, RealLiteral (x `* y)) | _ => raise SimplifyError "REAL * expression") (BE_Leaf (SOME BT_Real, RealLiteral (BReal.fromString "1.0"))) litOperands
    in
      BE_Commutative (SOME BT_Real, Keyword "*", (if litOperands = [] then nonlitOperands else (lite :: nonlitOperands)))
    end

  | simplify (BE_Node2 (_, Keyword ":", BE_Leaf (_, Keyword "TRUE" ), BE_Leaf (_, Keyword "BOOL"))) = BE_Leaf (SOME BT_Predicate, Keyword "btrue")
  | simplify (BE_Node2 (_, Keyword ":", BE_Leaf (_, Keyword "FALSE"), BE_Leaf (_, Keyword "BOOL"))) = BE_Leaf (SOME BT_Predicate, Keyword "btrue")
  
    (* 整数の単項マイナスを符号としてリテラル内に押し込める *)
  | simplify (BE_Node1 (SOME BT_Integer, Keyword "-", BE_Leaf (SOME BT_Integer, IntegerLiteral value))) =
      BE_Leaf (SOME BT_Integer, IntegerLiteral (~value))

    (* 空集合 *)
  | simplify (BE_ExSet (to, [])) = BE_Leaf (to, Keyword "{}")

    (* 空シーケンス *)
  | simplify (BE_Seq (to, [])) = BE_Leaf (to, Keyword "[]")

    (* 論理式の木を上から論理積、論理和、論理否定の順にする規則をここに書くことで、
      それが常に保たれている前提で推論規則を整備できる *)
  | simplify (BE_Node1 (SOME BT_Predicate, Keyword "not", BE_Node1 (SOME BT_Predicate, Keyword "not", e))) = e
  | simplify (BE_Node1 (SOME BT_Predicate, Keyword "not", BE_Commutative (SOME BT_Predicate, Keyword "&", l))) =
    BE_Commutative (SOME BT_Predicate, Keyword "or", List.map (fn e => BE_Node1 (SOME BT_Predicate, Keyword "not", e)) l)
  | simplify (BE_Node1 (SOME BT_Predicate, Keyword "not", BE_Commutative (SOME BT_Predicate, Keyword "or", l))) =
    BE_Commutative (SOME BT_Predicate, Keyword "&", List.map (fn e => BE_Node1 (SOME BT_Predicate, Keyword "not", e)) l)
  | simplify (BE_Commutative (SOME BT_Predicate, Keyword "or", l1)) =
    let
      val noDouble = Utils.deleteDouble AST.eqExprs l1
      val andExprOpt = List.find (fn (BE_Commutative (SOME BT_Predicate, Keyword "&", _)) => true | _ => false) noDouble
      val others = Utils.dropOne (fn (BE_Commutative (SOME BT_Predicate, Keyword "&", _)) => true | _ => false) noDouble
    in
      case (andExprOpt, others) of
        (NONE, []) => raise SimplifyError ""
      | (NONE, [y]) => y
      | (NONE, _) => BE_Commutative (SOME BT_Predicate, Keyword "or", noDouble)
      | (SOME x, []) => x
      | (SOME (BE_Commutative (_, _, l2)), _) => BE_Commutative (SOME BT_Predicate, Keyword "&", List.map (fn x => BE_Commutative (SOME BT_Predicate, Keyword "or", (x :: others))) l2)
      | _ => raise SimplifyError ""
    end
  | simplify (expr as BE_Node2 (to, Keyword "..", (BE_Leaf (_, IntegerLiteral i1)), (BE_Leaf (_, IntegerLiteral i2)))) =
    if
      i1 <= i2
    then
      expr
    else
      BE_Leaf (to, Keyword "{}")
  | simplify x = x

and
  simplifyExprTree e =
    let
      val simplified = Utils.repeatApply (fn x => Utils.pam x [AST.mapExprTree simplify, AST.mapExprTree Commutative.flattenCommutative]) e
      
      (* リテラル内に押し込めた符号を整数は単項マイナス、実数は0.0からの引き算として可視化する *)
      fun restoreMinus (BE_Leaf (SOME BT_Integer, IntegerLiteral value)) =
          if
            value < 0
          then
            BE_Node1 (SOME BT_Integer, Keyword "-", BE_Leaf (SOME BT_Integer, IntegerLiteral (~value)))
          else
            BE_Leaf (SOME BT_Integer, IntegerLiteral value)
        | restoreMinus (BE_Leaf (SOME BT_Real, RealLiteral value)) =
          if
            BReal.isMinus value
          then
            BE_Node2 (SOME BT_Real, Keyword "-", BE_Leaf (SOME BT_Real, RealLiteral (BReal.fromString "0.0")), BE_Leaf (SOME BT_Real, RealLiteral value))
          else
            BE_Leaf (SOME BT_Real, RealLiteral value)
          
        | restoreMinus e = e
    in
      AST.mapExprTree restoreMinus simplified
    end

  fun deleteLiteralCondition (expr as BE_Node2 (_, Keyword "<=", (BE_Leaf (_, IntegerLiteral i1)), (BE_Leaf (_, IntegerLiteral i2)))) =
    if
      i1 <= i2
    then
      BE_Leaf (SOME BT_Predicate, Keyword "btrue") 
    else
      BE_Leaf (SOME BT_Predicate, Keyword "bfalse")
  | deleteLiteralCondition (BE_Node2 (_, Keyword "<=", (BE_Leaf (_, IntegerLiteral i1)), (BE_Leaf (_, Keyword "MAXINT")))) =
    if
      i1 <= 2147483647
    then
      BE_Leaf (SOME BT_Predicate, Keyword "btrue")
    else
      BE_Leaf (SOME BT_Predicate, Keyword "bfalse")
  | deleteLiteralCondition (BE_Node2 (_, Keyword "<=", (BE_Leaf (_, Keyword "MAXINT")), (BE_Leaf (_, IntegerLiteral i2)))) =
    if
      2147483647 <= i2
    then
      BE_Leaf (SOME BT_Predicate, Keyword "btrue")
    else
      BE_Leaf (SOME BT_Predicate, Keyword "bfalse")
  | deleteLiteralCondition (BE_Node2 (_, Keyword "<=", (BE_Leaf (_, IntegerLiteral i1)), (BE_Leaf (_, Keyword "MININT")))) =
    if
      i1 <= ~2147483648
    then
      BE_Leaf (SOME BT_Predicate, Keyword "btrue")
    else
      BE_Leaf (SOME BT_Predicate, Keyword "bfalse")  
  | deleteLiteralCondition (BE_Node2 (_, Keyword "<=", (BE_Leaf (_, Keyword "MININT")), (BE_Leaf (_, IntegerLiteral i2)))) =
    if
      ~2147483648 <= i2
    then
      BE_Leaf (SOME BT_Predicate, Keyword "btrue")
    else
      BE_Leaf (SOME BT_Predicate, Keyword "bfalse")
  | deleteLiteralCondition (BE_Node2 (_, Keyword "<=", (BE_Leaf (_, RealLiteral r1)), (BE_Leaf (_, RealLiteral r2)))) =
    if
      r1 `<= r2
    then
      BE_Leaf (SOME BT_Predicate, Keyword "btrue")
    else
          BE_Leaf (SOME BT_Predicate, Keyword "bfalse")
  | deleteLiteralCondition e = e

end
