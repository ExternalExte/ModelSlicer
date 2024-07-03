structure Sort =
struct
  exception SortError of string

  val random_ = Random.rand (1, 1)

  fun randomBool () = Random.randRange (0, 1) random_  = 1

  fun isTyping typeSets (BE_Node2 (_, Keyword ":", BE_Leaf (_, Var _), expr)) =
      let
        fun isTypeSet (BE_Leaf (_, Keyword "INTEGER")) = true
          | isTypeSet (BE_Leaf (_, Keyword "BOOL")) = true
          | isTypeSet (BE_Leaf (_, Keyword "REAL")) = true
          | isTypeSet (BE_Leaf (_, Keyword "FLOAT")) = true
          | isTypeSet (BE_Leaf (_, Keyword "STRING")) = true
          | isTypeSet (BE_Leaf (_, Var typeName)) = Utils.isIn typeName typeSets
          | isTypeSet (BE_Node1 (_, Keyword "POW", e)) = isTypeSet e
          | isTypeSet (BE_Node2 (_, Keyword "*", e1, e2)) = isTypeSet e1 andalso isTypeSet e2
          | isTypeSet _ = false
      in
        isTypeSet expr
      end
    | isTyping _ _ = false

  (* 型付けを最初にする関数 最後に使う *)
  fun makeTypingsFirst typeSets (BE_Commutative (_, Keyword "&", conditions)) =
      let
        val (typings, others) = List.partition (isTyping typeSets) conditions
      in
        BE_Commutative (SOME BT_Predicate, Keyword "&", (typings @ others))
      end
    | makeTypingsFirst _ e = e

  fun exprToString (BE_Leaf _) = " "
    | exprToString (BE_Node1 (_, Keyword operatorString, _))    = operatorString
    | exprToString (BE_Node2 (_, Keyword operatorString, _, _)) = operatorString
    | exprToString (BE_NodeN (_, Keyword operatorString, _))    = operatorString
    | exprToString (BE_Fnc _)    = "Fnc"
    | exprToString (BE_Img _)    = "Img"
    | exprToString (BE_Bool _)   = "Bool"
    | exprToString (BE_ExSet _)  = "ExSet"
    | exprToString (BE_InSet _)  = "InSet"
    | exprToString (BE_Seq _)    = "Seq"
    | exprToString (BE_ForAll _) = "ForAll"
    | exprToString (BE_Exists _) = "Exists"
    | exprToString (BE_Lambda _) = "Lambda"
    | exprToString (BE_Sigma _)  = "Sigma"
    | exprToString (BE_Pi _)     = "Pi"
    | exprToString (BE_Inter _)  = "Inter"
    | exprToString (BE_Union _)  = "Union"
    | exprToString (BE_Struct _) = "Struct"
    | exprToString (BE_Rec _)    = "Rec"
    | exprToString (BE_RcAc _)   = "RcAc"
    | exprToString (BE_Commutative (_, Keyword operatorString, _)) = operatorString
    | exprToString _ = raise SortError "invalid expression"

  val relationPool = ref [] : (BExpr * BExpr) list ref (* 推移的順序関係のプール *)

  fun compareTransitive x y =
      if
        AST.eqExprs x y
      then
        SOME EQUAL
      else if
        List.exists (fn (e1, e2) => AST.eqExprs x e1 andalso AST.eqExprs y e2) (!relationPool)
      then
        SOME LESS
      else if
        List.exists (fn (e1, e2) => AST.eqExprs x e2 andalso AST.eqExprs y e1) (!relationPool)
      then
        SOME GREATER
      else
        NONE

  fun addRelation (x, y) =
      case compareTransitive x y of
        SOME EQUAL   => () (* x と y が等しいため変化なし *)
      | SOME LESS    => () (* x < y が既存の順序に既にあるため変化なし *)
      | SOME GREATER => () (* x < y が既存の順序と矛盾しているので変化なし *)
      | NONE         => let
                          val ltx = List.filter (fn (_, e2) => AST.eqExprs e2 x) (!relationPool) (* e < x *)
                          val gty = List.filter (fn (e1, _) => AST.eqExprs e1 y) (!relationPool) (* y < e *)
                          val ltyRels = List.map (fn (e1, _) => (e1, y)) ltx (* e < x ならば e < y *)
                          val gtxRels = List.map (fn (_, e2) => (x, e2)) gty (* y < e ならば x < e *)
                        in
                          relationPool := (x, y) :: (Utils.deleteDouble (fn (e11, e12) => fn (e21, e22) => AST.eqExprs e11 e21 andalso AST.eqExprs e12 e22) ((!relationPool) @ ltyRels @ gtxRels))
                        end

  fun addRelations (xl, yl) = List.app (fn x => List.app (fn y => addRelation (x, y)) yl) xl

  fun addRelationList [] = ()
    | addRelationList (x :: xs) = (addRelations ([x], xs); addRelationList xs)

  fun addMaxSetRelations maxl = (* その時点での最後尾の識別子群を設定する *)
      let
        val tmp1 = List.filter (fn maxElement => List.all (fn (x, y) => (not (AST.eqExprs maxElement x)) andalso (not (AST.eqExprs maxElement y))) (!relationPool)) maxl (* すでにrelationPool内に何らかの関係があるものを除外 *)
        val tmp2 = List.concat (List.map (fn (x, y) => (x, y) :: (List.concat (List.map (fn e => [(x, e), (y, e)]) tmp1))) (!relationPool))
      in
        relationPool := Utils.deleteDouble (fn (x1, y1) => fn (x2, y2) => AST.eqExprs x1 x2 andalso AST.eqExprs y1 y2) tmp2
      end

  fun addStaticRelations (BMch (_, mchParams, clauses)) =
      let
        val sets       = case List.find (fn (BC_SETS       _) => true | _ => false) clauses of NONE => [] | SOME (BC_SETS       l) => l | _ => raise SortError ""

        val cconstants = case List.find (fn (BC_CCONSTANTS _) => true | _ => false) clauses of NONE => [] | SOME (BC_CCONSTANTS l) => l | _ => raise SortError ""
        val aconstants = case List.find (fn (BC_ACONSTANTS _) => true | _ => false) clauses of NONE => [] | SOME (BC_ACONSTANTS l) => l | _ => raise SortError ""
        val cvariables = case List.find (fn (BC_CVARIABLES _) => true | _ => false) clauses of NONE => [] | SOME (BC_CVARIABLES l) => l | _ => raise SortError ""
        val avariables = case List.find (fn (BC_AVARIABLES _) => true | _ => false) clauses of NONE => [] | SOME (BC_AVARIABLES l) => l | _ => raise SortError ""

        val operation  = case List.find (fn (BC_OPERATIONS _) => true | _ => false) clauses of SOME (BC_OPERATIONS [opr]) => opr | _ => raise SortError "invalid number of opearations"

        val constraintsOpt = List.find (fn (BC_CONSTRAINTS _) => true | _ => false) clauses
        val propertiesOpt  = List.find (fn (BC_PROPERTIES  _) => true | _ => false) clauses
        val invariantOpt   = List.find (fn (BC_INVARIANT   _) => true | _ => false) clauses
        (* ASSERTIONS は無視 *)
        val operationBody  = case operation of BOp (_, _, _, BS_Precondition (_, s)) => s | BOp (_, _, _, s) => s (* 事前条件を除いた操作の代入文 *)

        val (mchParamTypeSetExprs, mchParamNotTypeSetExprs) = List.partition (fn (BE_Leaf (NONE, Var idStr)) => TypeInference.isTypeSetByName idStr | _ => raise SortError "invalid var") (List.map (fn v => BE_Leaf (NONE, v)) mchParams)
        val deferredSetExprs    =              List.map (fn (BT_Deferred x)     =>                   BE_Leaf (NONE, Var x) | _ => raise SortError "")       (List.filter (fn (BT_Deferred _) => true | _ => false) sets)
        val enumSetExprs        =              List.map (fn (BT_Enum (x, _))    =>                   BE_Leaf (NONE, Var x) | _ => raise SortError "")       (List.filter (fn (BT_Enum     _) => true | _ => false) sets)
        val enumSetElementExprs = List.concat (List.map (fn (BT_Enum (_, elms)) => List.map (fn x => BE_Leaf (NONE, Var x)) elms | _ => raise SortError "") (List.filter (fn (BT_Enum     _) => true | _ => false) sets))
        val cconstantExprs = List.map (fn v => BE_Leaf (NONE, v)) cconstants
        val aconstantExprs = List.map (fn v => BE_Leaf (NONE, v)) aconstants
        val cvariableExprs = List.map (fn v => BE_Leaf (NONE, v)) cvariables
        val avariableExprs = List.map (fn v => BE_Leaf (NONE, v)) avariables
        val (outputExprs, inputExprs) = case operation of BOp (_, outputs, inputs, _) => (List.map (fn v => BE_Leaf (NONE, v)) outputs, List.map (fn v => BE_Leaf (NONE, v)) inputs)

        fun extractRecordFieldsInExpr e =
            let
              val recordExprs = AST.findExprs (fn (BE_Struct _) => true | (BE_Rec _) => true | (BE_RcAc _) => true | _ => false) e
              val fieldStrings = List.concat (List.map (fn (BE_Struct (_, l))    => List.map (fn (s, _) => s) l
                                                         | (BE_Rec    (_, l))    => List.concat (List.map (fn (NONE, _) => [] | (SOME s, _) => [s]) l)
                                                         | (BE_RcAc   (_, _, s)) => [s]
                                                         | _                     => raise SortError "")
                                                       recordExprs)
            in
              List.map (fn s => BE_Leaf (NONE, Var s)) (Utils.deleteDouble Utils.eqto fieldStrings)
            end

        fun extractRecordFieldsInSubstitution (BS_Block            s               ) = extractRecordFieldsInSubstitution s
          | extractRecordFieldsInSubstitution BS_Identity                            = []
          | extractRecordFieldsInSubstitution (BS_Precondition     (BP e, s       )) = Utils.deleteDouble Utils.eqto ((extractRecordFieldsInExpr e) @ (extractRecordFieldsInSubstitution s))
          | extractRecordFieldsInSubstitution (BS_Assertion        (BP e, s       )) = Utils.deleteDouble Utils.eqto ((extractRecordFieldsInExpr e) @ (extractRecordFieldsInSubstitution s))
          | extractRecordFieldsInSubstitution (BS_Choice           l               ) = Utils.deleteDouble Utils.eqto (List.concat (List.map extractRecordFieldsInSubstitution l))
          | extractRecordFieldsInSubstitution (BS_If               l               ) = Utils.deleteDouble Utils.eqto (List.concat (List.map (fn (NONE, s) => extractRecordFieldsInSubstitution s | (SOME (BP e), s) => (extractRecordFieldsInExpr e) @ (extractRecordFieldsInSubstitution s)) l))
          | extractRecordFieldsInSubstitution (BS_Select           l               ) = Utils.deleteDouble Utils.eqto (List.concat (List.map (fn (NONE, s) => extractRecordFieldsInSubstitution s | (SOME (BP e), s) => (extractRecordFieldsInExpr e) @ (extractRecordFieldsInSubstitution s)) l))
          | extractRecordFieldsInSubstitution (BS_Case             (e   , l       )) = Utils.deleteDouble Utils.eqto ((extractRecordFieldsInExpr e) @ (List.concat (List.map (fn (el, s) => ((List.concat (List.map extractRecordFieldsInExpr el)) @ (extractRecordFieldsInSubstitution s))) l)))
          | extractRecordFieldsInSubstitution (BS_Any              (_   , BP e, s )) = Utils.deleteDouble Utils.eqto ((extractRecordFieldsInExpr e) @ (extractRecordFieldsInSubstitution s))
          | extractRecordFieldsInSubstitution (BS_Let              (l   , s       )) = Utils.deleteDouble Utils.eqto ((List.concat (List.map (fn (_, e) => extractRecordFieldsInExpr e) l)) @ (extractRecordFieldsInSubstitution s))
          | extractRecordFieldsInSubstitution (BS_BecomesElt       (l   , e       )) = Utils.deleteDouble Utils.eqto ((List.concat (List.map extractRecordFieldsInExpr l)) @ (extractRecordFieldsInExpr e))
          | extractRecordFieldsInSubstitution (BS_BecomesSuchThat  (l   , BP e    )) = Utils.deleteDouble Utils.eqto ((List.concat (List.map extractRecordFieldsInExpr l)) @ (extractRecordFieldsInExpr e))
          | extractRecordFieldsInSubstitution (BS_Call             (_   , l1  , l2)) = Utils.deleteDouble Utils.eqto (List.concat (List.map extractRecordFieldsInExpr (l1 @ l2)))
          | extractRecordFieldsInSubstitution (BS_BecomesEqual     (e1  , e2      )) = Utils.deleteDouble Utils.eqto ((extractRecordFieldsInExpr e1) @ (extractRecordFieldsInExpr e2))
          | extractRecordFieldsInSubstitution (BS_BecomesEqualList (l1  , l2      )) = Utils.deleteDouble Utils.eqto (List.concat (List.map extractRecordFieldsInExpr (l1 @ l2)))
          | extractRecordFieldsInSubstitution (BS_Simultaneous     l               ) = Utils.deleteDouble Utils.eqto (List.concat (List.map extractRecordFieldsInSubstitution l))
          | extractRecordFieldsInSubstitution _                                      = raise SortError "input substitution is for IMPLEMENTATION" (* WHILE, VAR, ;が来たとき *)

        val recordFieldsInConstraints = case constraintsOpt of NONE => [] | SOME (BC_CONSTRAINTS (BP e)) => extractRecordFieldsInExpr e | _ => raise SortError "" (* CONSTRAINTS 内のレコードのフィールドを列挙 *)
        val recordFieldsInProperties  = case propertiesOpt  of NONE => [] | SOME (BC_PROPERTIES  (BP e)) => extractRecordFieldsInExpr e | _ => raise SortError "" (* PROPERTIES 〃 *)
        val recordFieldsInInvariant   = case invariantOpt   of NONE => [] | SOME (BC_INVARIANT   (BP e)) => extractRecordFieldsInExpr e | _ => raise SortError "" (* INVARIANT 〃 *)
        val recordFieldsInOperation   = extractRecordFieldsInSubstitution operationBody                                                 (* 事前条件以外の代入文 〃 *)

        fun addLocalVarRelationsInExpr minSet (BE_Leaf        _                       ) = ()
          | addLocalVarRelationsInExpr minSet (BE_Node1       (_   , _    , e        )) = addLocalVarRelationsInExpr minSet e
          | addLocalVarRelationsInExpr minSet (BE_Node2       (_   , _    , e1   , e2)) = (addLocalVarRelationsInExpr minSet e1; addLocalVarRelationsInExpr minSet e2)
          | addLocalVarRelationsInExpr minSet (BE_NodeN       (_   , _    , l        )) = List.app (addLocalVarRelationsInExpr minSet) l
          | addLocalVarRelationsInExpr minSet (BE_Fnc         (_   , e1   , e2       )) = (addLocalVarRelationsInExpr minSet e1; addLocalVarRelationsInExpr minSet e2)
          | addLocalVarRelationsInExpr minSet (BE_Img         (_   , e1   , e2       )) = (addLocalVarRelationsInExpr minSet e1; addLocalVarRelationsInExpr minSet e2)
          | addLocalVarRelationsInExpr minSet (BE_Bool        (BP e                  )) = addLocalVarRelationsInExpr minSet e
          | addLocalVarRelationsInExpr minSet (BE_ExSet       (_   , l               )) = List.app (addLocalVarRelationsInExpr minSet) l
          | addLocalVarRelationsInExpr minSet (BE_InSet       (_   , vl   , BP e     )) =
            let
              val newMinSet = List.map (fn v => BE_Leaf (NONE, v)) vl
            in
              addRelations (minSet, newMinSet); addLocalVarRelationsInExpr newMinSet e
            end
          | addLocalVarRelationsInExpr minSet (BE_Seq         (_   , l               )) = List.app (addLocalVarRelationsInExpr minSet) l
          | addLocalVarRelationsInExpr minSet (BE_ForAll      (vl  , BP e1, BP e2    )) =
            let
              val newMinSet = List.map (fn v => BE_Leaf (NONE, v)) vl
            in
              addRelations (minSet, newMinSet); addLocalVarRelationsInExpr newMinSet e1; addLocalVarRelationsInExpr newMinSet e2
            end
          | addLocalVarRelationsInExpr minSet (BE_Exists      (vl  , BP e            )) =
            let
              val newMinSet = List.map (fn v => BE_Leaf (NONE, v)) vl
            in
              addRelations (minSet, newMinSet); addLocalVarRelationsInExpr newMinSet e
            end
          | addLocalVarRelationsInExpr minSet (BE_Lambda      (_   , vl   , BP e1, e2)) =
            let
              val newMinSet = List.map (fn v => BE_Leaf (NONE, v)) vl
            in
              addRelations (minSet, newMinSet); addLocalVarRelationsInExpr newMinSet e1; addLocalVarRelationsInExpr newMinSet e2
            end
          | addLocalVarRelationsInExpr minSet (BE_Sigma       (_   , v    , BP e1, e2)) =
            let
              val newMinSet = [(BE_Leaf (NONE, v))]
            in
              addRelations (minSet, newMinSet); addLocalVarRelationsInExpr newMinSet e1; addLocalVarRelationsInExpr newMinSet e2
            end
          | addLocalVarRelationsInExpr minSet (BE_Pi          (_   , v    , BP e1, e2)) =
            let
              val newMinSet = [(BE_Leaf (NONE, v))]
            in
              addRelations (minSet, newMinSet); addLocalVarRelationsInExpr newMinSet e1; addLocalVarRelationsInExpr newMinSet e2
            end
          | addLocalVarRelationsInExpr minSet (BE_Inter       (_   , vl   , BP e1, e2)) =
            let
              val newMinSet = List.map (fn v => BE_Leaf (NONE, v)) vl
            in
              addRelations (minSet, newMinSet); addLocalVarRelationsInExpr newMinSet e1; addLocalVarRelationsInExpr newMinSet e2
            end
          | addLocalVarRelationsInExpr minSet (BE_Union       (_   , vl   , BP e1, e2)) =
            let
              val newMinSet = List.map (fn v => BE_Leaf (NONE, v)) vl
            in
              addRelations (minSet, newMinSet); addLocalVarRelationsInExpr newMinSet e1; addLocalVarRelationsInExpr newMinSet e2
            end
          | addLocalVarRelationsInExpr minSet (BE_Struct      (_   , l               )) = List.app (fn (_, e) => addLocalVarRelationsInExpr minSet e) l
          | addLocalVarRelationsInExpr minSet (BE_Rec         (_   , l               )) = List.app (fn (_, e) => addLocalVarRelationsInExpr minSet e) l
          | addLocalVarRelationsInExpr minSet (BE_RcAc        (_   , e     , _       )) = addLocalVarRelationsInExpr minSet e
          | addLocalVarRelationsInExpr minSet (BE_Commutative (_   , _     , l       )) = List.app (addLocalVarRelationsInExpr minSet) l

        fun addLocalVarRelationsInSubstitution minSet (BS_Block            s               ) = addLocalVarRelationsInSubstitution minSet s
          | addLocalVarRelationsInSubstitution _      BS_Identity                            = ()
          | addLocalVarRelationsInSubstitution minSet (BS_Precondition     (BP e, s       )) = (addLocalVarRelationsInExpr minSet e; addLocalVarRelationsInSubstitution minSet s)
          | addLocalVarRelationsInSubstitution minSet (BS_Assertion        (BP e, s       )) = (addLocalVarRelationsInExpr minSet e; addLocalVarRelationsInSubstitution minSet s)
          | addLocalVarRelationsInSubstitution minSet (BS_Choice           l               ) = List.app (addLocalVarRelationsInSubstitution minSet) l
          | addLocalVarRelationsInSubstitution minSet (BS_If               l               ) = List.app (fn (NONE,          s) => addLocalVarRelationsInSubstitution minSet s
                                                                                                          | ((SOME (BP e)), s) => (addLocalVarRelationsInExpr minSet e; addLocalVarRelationsInSubstitution minSet s)) l
          | addLocalVarRelationsInSubstitution minSet (BS_Select           l               ) = List.app (fn (NONE,          s) => addLocalVarRelationsInSubstitution minSet s
                                                                                                          | ((SOME (BP e)), s) => (addLocalVarRelationsInExpr minSet e; addLocalVarRelationsInSubstitution minSet s)) l
          | addLocalVarRelationsInSubstitution minSet (BS_Case             (e   , l       )) = (addLocalVarRelationsInExpr minSet e; List.app (fn (el, s) => (List.app (addLocalVarRelationsInExpr minSet) el; addLocalVarRelationsInSubstitution minSet s)) l)
          | addLocalVarRelationsInSubstitution minSet (BS_Any              (_   , BP e, s )) = (addLocalVarRelationsInExpr minSet e; addLocalVarRelationsInSubstitution minSet s)
          | addLocalVarRelationsInSubstitution minSet (BS_Let              (l   , s       )) = (List.app (fn (_, e) => addLocalVarRelationsInExpr minSet e) l; addLocalVarRelationsInSubstitution minSet s)
          | addLocalVarRelationsInSubstitution minSet (BS_BecomesElt       (l   , e       )) = (List.app (addLocalVarRelationsInExpr minSet) l; addLocalVarRelationsInExpr minSet e)
          | addLocalVarRelationsInSubstitution minSet (BS_BecomesSuchThat  (l   , BP e    )) = (List.app (addLocalVarRelationsInExpr minSet) l; addLocalVarRelationsInExpr minSet e)
          | addLocalVarRelationsInSubstitution minSet (BS_Call             (_   , l1  , l2)) = List.app (addLocalVarRelationsInExpr minSet) (l1 @ l2)
          | addLocalVarRelationsInSubstitution minSet (BS_BecomesEqual     (e1  , e2      )) = (addLocalVarRelationsInExpr minSet e1; addLocalVarRelationsInExpr minSet e2)
          | addLocalVarRelationsInSubstitution minSet (BS_BecomesEqualList (l1  , l2      )) = List.app (addLocalVarRelationsInExpr minSet) (l1 @ l2)
          | addLocalVarRelationsInSubstitution minSet (BS_Simultaneous     l               ) = List.app (addLocalVarRelationsInSubstitution minSet) l
          | addLocalVarRelationsInSubstitution _      _                                      = raise SortError "input substitution is fo IMPLEMENTATION"

        fun addEnumRelations () = (* 要素の個数による列挙集合の順序付け *)
            let
              val enumSets = List.map (fn (BT_Enum (typeSet, elements)) => (BE_Leaf (NONE, Var typeSet), List.map (fn element => BE_Leaf (NONE, Var element)) elements)
                                        | _                             => raise SortError "")
                                      (List.filter (fn (BT_Enum _) => true | _ => false) sets)
            in
              List.app (fn (typeSet1, elements1) => List.app (fn (typeSet2, elements2) => case Int.compare (List.length elements1, List.length elements2) of
                                                                                            EQUAL   => ()
                                                                                          | LESS    => (addRelation (typeSet1, typeSet2); addRelations (elements1, elements2))
                                                                                          | GREATER => (addRelation (typeSet2, typeSet1); addRelations (elements2, elements1)))
                                                             enumSets)
                       enumSets
            end
      in
        relationPool := [];
        addMaxSetRelations [(BE_Leaf (SOME (BT_Power (SOME BT_Integer)), Keyword "INTEGER"))];
        addMaxSetRelations [(BE_Leaf (SOME (BT_Power (SOME BT_Bool   )), Keyword "BOOL"))];
        addMaxSetRelations [(BE_Leaf (SOME (BT_Power (SOME BT_Real   )), Keyword "REAL"))];
        addMaxSetRelations [(BE_Leaf (SOME (BT_Power (SOME BT_Float  )), Keyword "FLOAT"))];
        addMaxSetRelations [(BE_Leaf (SOME (BT_Power (SOME BT_String )), Keyword "STRING"))];
        addMaxSetRelations mchParamTypeSetExprs;(* 重みではなく順序 <=をプリミティブとするため、向きが一致してわかりやすいため昇順でソート *)
        addMaxSetRelations mchParamNotTypeSetExprs;
        addMaxSetRelations deferredSetExprs;
        addMaxSetRelations enumSetExprs;
        addMaxSetRelations enumSetElementExprs;
        addEnumRelations ();
        (* 型集合の順序付けに、モデル内での登場回数や型としての登場回数も利用すべき？ *) (* TODO *)
        addMaxSetRelations cconstantExprs;
        addMaxSetRelations aconstantExprs;
        addMaxSetRelations cvariableExprs;
        addMaxSetRelations avariableExprs;
        addMaxSetRelations outputExprs;
        addMaxSetRelations inputExprs;

        addMaxSetRelations recordFieldsInConstraints;
        addMaxSetRelations recordFieldsInProperties;
        addMaxSetRelations recordFieldsInInvariant;
        addMaxSetRelations recordFieldsInOperation;
        let
          val allExprsInRelation = Utils.deleteDouble AST.eqExprs (List.concat (List.map (fn (x, y) => [x, y]) (!relationPool)))
        in
          case constraintsOpt of NONE => () | SOME (BC_CONSTRAINTS (BP e)) => addLocalVarRelationsInExpr allExprsInRelation e | _ => raise SortError "";
          case propertiesOpt  of NONE => () | SOME (BC_PROPERTIES  (BP e)) => addLocalVarRelationsInExpr allExprsInRelation e | _ => raise SortError "";
          case invariantOpt   of NONE => () | SOME (BC_INVARIANT   (BP e)) => addLocalVarRelationsInExpr allExprsInRelation e | _ => raise SortError "";
          addLocalVarRelationsInSubstitution allExprsInRelation operationBody
        end
      end
    | addStaticRelations _ = raise SortError "not abstract machine"

  fun compareExprs (expr1 as (BE_Leaf _))                         (expr2 as (BE_Leaf _))                         = compareTransitive expr1 expr2
    | compareExprs (BE_Node1 (to1, Keyword operatorString1, expr1)) (BE_Node1 (to2, Keyword operatorString2, expr2)) =
      let
        val ctResult = compareTransitive (BE_Node1 (to1, Keyword operatorString1, expr1)) (BE_Node1 (to2, Keyword operatorString2, expr2))
      in
        if
          ctResult <> NONE
        then
          ctResult
        else
          if
            operatorString1 = operatorString2
          then
            compareExprs expr1 expr2
          else
            SOME (String.compare (operatorString1, operatorString2))
      end
    | compareExprs (BE_Node2 (_, Keyword "="            , expr11, expr12)) (BE_Node2 (_, Keyword "="            , expr21, expr22)) = compareExprMultiSets [expr11, expr12] [expr21, expr22]
    | compareExprs (BE_Node2 (_, Keyword operatorString1, expr11, expr12)) (BE_Node2 (_, Keyword operatorString2, expr21, expr22)) =
      if
        operatorString1 = operatorString2
      then
        let
          val e1Ord = compareExprs expr11 expr21
        in
          if
            e1Ord = NONE orelse e1Ord = SOME EQUAL
          then
            compareExprs expr12 expr22
          else
            e1Ord
        end
      else
        SOME (String.compare (operatorString1, operatorString2))
    | compareExprs (BE_NodeN (_, Keyword operatorString1, exprs1)) (BE_NodeN (_, Keyword operatorString2, exprs2)) =
      if
        operatorString1 = operatorString2
      then
        let
          val exprsLengthOrd = SOME (Int.compare ((List.length exprs1), (List.length exprs2))) (* 引数の短い方が後 *)
        in
          if
            exprsLengthOrd = SOME EQUAL
          then
            compareExprLists exprs1 exprs2
          else
            exprsLengthOrd
        end
      else
        SOME (String.compare (operatorString1, operatorString2))
    | compareExprs (BE_Commutative (_, Keyword operatorString1, exprs1)) (BE_Commutative (_, Keyword operatorString2, exprs2)) =
      if
        operatorString1 = operatorString2
      then
        let
          val exprsLengthOrd = SOME (Int.compare ((List.length exprs1), (List.length exprs2))) (* 要素数が少ない方が先 *)
        in
          if
            exprsLengthOrd = SOME EQUAL
          then
            compareExprMultiSets exprs1 exprs2 (* 多重集合として比べるよう変更 *)
          else
            exprsLengthOrd
        end
      else
        SOME (String.compare (operatorString1, operatorString2))
    | compareExprs (BE_Fnc (_, expr11, expr12)) (BE_Fnc (_, expr21, expr22)) =
      let
        val e1Ord = compareExprs expr11 expr21
      in
        if
          e1Ord = NONE orelse e1Ord = SOME EQUAL
        then
          compareExprs expr12 expr22
        else
          e1Ord
      end
    | compareExprs (BE_Img (_, expr11, expr12)) (BE_Img (_, expr21, expr22)) =
      let
        val e1Ord = compareExprs expr11 expr21
      in
        if
          e1Ord = NONE orelse e1Ord = SOME EQUAL
        then
          compareExprs expr12 expr22
        else
          e1Ord
      end
    | compareExprs (BE_Bool (BP expr1)) (BE_Bool (BP expr2)) = compareExprs expr1 expr2
    | compareExprs (BE_ExSet (_, exprs1)) (BE_ExSet (_, exprs2)) =
      let
        val exprsLengthOrd = SOME (Int.compare ((List.length exprs1), (List.length exprs2))) (* 要素数が少ない方が先 *)
      in
        if
          exprsLengthOrd = SOME EQUAL
        then
          compareExprMultiSets exprs1 exprs2 (* 集合として比べるよう変更 *)
        else
          exprsLengthOrd
      end
    | compareExprs (BE_InSet (_, tks1, BP e1)) (BE_InSet (_, tks2, BP e2)) =
      let
        val tksLengthOrd = SOME (Int.compare ((List.length tks1), (List.length tks2))) (* 局所変数が少ない方が先 *)
      in
        if
          tksLengthOrd = SOME EQUAL
        then
          compareExprs e1 e2
        else
          tksLengthOrd
      end
    | compareExprs (BE_Seq (_, exprs1)) (BE_Seq (_, exprs2)) =
      let
        val exprsLengthOrd = SOME (Int.compare ((List.length exprs1), (List.length exprs2))) (* 要素数が少ない方が先 *)
      in
        if
          exprsLengthOrd = SOME EQUAL
        then
          compareExprLists exprs1 exprs2
        else
          exprsLengthOrd
      end
    | compareExprs (BE_ForAll (tks1, BP e11, BP e12)) (BE_ForAll (tks2, BP e21, BP e22)) =
      let
        val tksLengthOrd = SOME (Int.compare ((List.length tks1), (List.length tks2))) (* 局所変数が少ない方が先 *)
      in
        if
          tksLengthOrd = SOME EQUAL
        then
          let
            val e1Ord = compareExprs e11 e21
          in
            if
              e1Ord = NONE orelse e1Ord = SOME EQUAL
            then
              compareExprs e21 e22
            else
              e1Ord
          end
        else
          tksLengthOrd
      end
    | compareExprs (BE_Exists (tks1, BP e1)) (BE_Exists (tks2, BP e2)) =
      let
        val tksLengthOrd = SOME (Int.compare ((List.length tks1), (List.length tks2))) (* 局所変数が少ない方が先 *)
      in
        if
          tksLengthOrd = SOME EQUAL
        then
          compareExprs e1 e2
        else
          tksLengthOrd
      end
    | compareExprs (BE_Lambda (_, tks1, BP e11, e12)) (BE_Lambda (_, tks2, BP e21, e22)) =
      let
        val tksLengthOrd = SOME (Int.compare ((List.length tks1), (List.length tks2))) (* 局所変数が少ない方が先 *)
      in
        if
          tksLengthOrd = SOME EQUAL
        then
          let
            val e1Ord = compareExprs e11 e21
          in
            if
              e1Ord = NONE orelse e1Ord = SOME EQUAL
            then
              compareExprs e12 e22
            else
              e1Ord
          end
        else
          tksLengthOrd
      end
    | compareExprs (BE_Sigma (_, _, BP e11, e12)) (BE_Lambda (_, _, BP e21, e22)) =
      let
        val e1Ord = compareExprs e11 e21
      in
        if
          e1Ord = NONE orelse e1Ord = SOME EQUAL
        then
          compareExprs e12 e22
        else
          e1Ord
      end
    | compareExprs (BE_Pi (_, _, BP e11, e12)) (BE_Pi (_, _, BP e21, e22)) =
      let
        val e1Ord = compareExprs e11 e21
      in
        if
          e1Ord = NONE orelse e1Ord = SOME EQUAL
        then
          compareExprs e12 e22
        else
          e1Ord
      end
    | compareExprs (BE_Inter (_, tks1, BP e11, e12)) (BE_Inter (_, tks2, BP e21, e22)) =
      let
        val tksLengthOrd = SOME (Int.compare ((List.length tks1), (List.length tks2))) (* 局所変数が少ない方が先 *)
      in
        if
          tksLengthOrd = SOME EQUAL
        then
          let
            val e1Ord = compareExprs e11 e21
          in
            if
              e1Ord = NONE orelse e1Ord = SOME EQUAL
            then
              compareExprs e12 e22
            else
              e1Ord
          end
        else
          tksLengthOrd

      end
    | compareExprs (BE_Union (_, tks1, BP e11, e12)) (BE_Union (_, tks2, BP e21, e22)) =
      let
        val tksLengthOrd = SOME (Int.compare ((List.length tks1), (List.length tks2))) (* 局所変数が少ない方が先 *)
      in
        if
          tksLengthOrd = SOME EQUAL
        then
          let
            val e1Ord = compareExprs e11 e21
          in
            if
              e1Ord = NONE orelse e1Ord = SOME EQUAL
            then
              compareExprs e12 e22
            else
              e1Ord
          end
        else
          tksLengthOrd
      end
    | compareExprs (BE_Struct (_, l1)) (BE_Struct (_, l2)) =
      let
        val lLengthOrd = SOME (Int.compare ((List.length l1), (List.length l2))) (* フィールド数が少ない方が先 *)
      in
        if
          lLengthOrd = SOME EQUAL
        then
          let
            val (_, es1) = ListPair.unzip l1
            val (_, es2) = ListPair.unzip l2
          in
            compareExprLists es1 es2
          end
        else
          lLengthOrd
      end
    | compareExprs (BE_Rec (_, l1)) (BE_Rec (_, l2)) =
      let
        val lLengthOrd = SOME (Int.compare ((List.length l1), (List.length l2))) (* フィールド数が少ない方が先 *)
      in
        if
          lLengthOrd = SOME EQUAL
        then
          let
            val (_, es1) = ListPair.unzip l1
            val (_, es2) = ListPair.unzip l2
          in
            compareExprLists es1 es2
          end
        else
          lLengthOrd
      end
    (* 何番目のフィールドにアクセスするのかで比較することもできるが、現状レコードのフィールドの順番の扱いの方針が定まっていないため、
    レコードの式のみをみる *)
    | compareExprs (BE_RcAc (_, expr1, _)) (BE_RcAc (_, expr2, _)) = compareExprs expr1 expr2
    | compareExprs expr1 expr2 = SOME (String.compare ((exprToString expr1), (exprToString expr2)))
    and
      compareExprLists []          []          = SOME EQUAL
    | compareExprLists []          _           = raise SortError "different list length"
    | compareExprLists _           []          = raise SortError "different list length"
    | compareExprLists (e1 :: es1) (e2 :: es2) =
      let
        val headOrd = compareExprs e1 e2
        val tailOrd = compareExprLists es1 es2
      in
        case (headOrd, tailOrd) of
          (SOME EQUAL, _         ) => tailOrd
        | (NONE,       NONE      ) => NONE
        | (NONE,       SOME EQUAL) => NONE
        | (NONE,       _         ) => tailOrd
        | _                        => headOrd
      end
    and
      compareExprMultiSets l1 l2 =
      if
        Utils.eqAsMset AST.eqExprs l1 l2
      then
        SOME EQUAL
      else
        let
          val relationList = List.concat (List.map (fn e1 => List.map (fn e2 => compareExprs e1 e2) l2) l1)
          val numberOfNone    = List.length (List.filter (Utils.eqto NONE          ) relationList)
          val numberOfLess    = List.length (List.filter (Utils.eqto (SOME LESS   )) relationList)
          val numberOfGreater = List.length (List.filter (Utils.eqto (SOME GREATER)) relationList)
        in
          if
            numberOfNone = 0 andalso numberOfLess = numberOfGreater
          then
            (* 2つの多重集合から1個ずつ要素を取ってきたときその間の順序が全て決定しており、その個数が拮抗したとき *)
            NONE (* とりあえずNONEにするが後で変更の可能性あり *) (* TO DO *)
          else
            if
              numberOfNone + numberOfGreater < numberOfLess
            then
              SOME LESS
            else
              if
                numberOfNone + numberOfLess < numberOfGreater
              then
                SOME GREATER
              else
                NONE
        end
    and
      compareSubstitutions (BS_Block s1) (BS_Block s2) = compareSubstitutions s1 s2
    | compareSubstitutions BS_Identity BS_Identity = SOME EQUAL
    | compareSubstitutions (BS_Precondition (BP _, s1)) (BS_Precondition (BP _, s2)) = compareSubstitutions s1 s2 (* 事前条件は重み付けの根拠としない (重要) *)
    | compareSubstitutions (BS_Assertion (BP e1, s1)) (BS_Assertion (BP e2, s2)) =
      let
        val eOrd = compareExprs e1 e2
      in
        if
          eOrd = NONE orelse eOrd = SOME EQUAL
        then
          compareSubstitutions s1 s2
        else
          eOrd
      end
    | compareSubstitutions (BS_Choice l1) (BS_Choice l2) =
      let
        val lLenOrd = SOME (Int.compare ((List.length l1), (List.length l2))) (* 要素数が少ない方が先 *)
      in
        if
          lLenOrd = SOME EQUAL
        then
          compareSubstitutionMultiSets l1 l2
        else
          lLenOrd
      end
    | compareSubstitutions (BS_If l1) (BS_If l2) =
      let
        val lLenOrd = SOME (Int.compare ((List.length l1), (List.length l2))) (* 要素数が少ない方が先 *)
      in
        if
          lLenOrd = SOME EQUAL
        then
          let
            (* ELSE節がない方が先 *)
            val elseExists1 = List.length (List.filter (fn (NONE, _) => true | _ => false) l1)
            val elseExists2 = List.length (List.filter (fn (NONE, _) => true | _ => false) l2)
            val elseOrd = SOME (Int.compare (elseExists1, elseExists2))
          in
            if
              elseOrd = SOME EQUAL
            then
              let
                val (eOpts1, ss1) = ListPair.unzip l1
                val (eOpts2, ss2) = ListPair.unzip l2
                val sOrd = compareSubstitutionLists ss1 ss2
                val es1 = List.concat (List.map (fn NONE => [] | (SOME (BP e)) => [e]) eOpts1)
                val es2 = List.concat (List.map (fn NONE => [] | (SOME (BP e)) => [e]) eOpts2)
              in
                if
                  sOrd = NONE orelse sOrd = SOME EQUAL
                then
                  compareExprLists es1 es2
                else
                  sOrd
              end
            else
              elseOrd
          end
        else
          lLenOrd
      end
    | compareSubstitutions (BS_Any (tks1, BP e1, s1)) (BS_Any (tks2, BP e2, s2)) =
      let
        val tksLenOrd = SOME (Int.compare ((List.length tks1), (List.length tks2))) (* 局所変数が少ない方が先 *)
      in
        if
          tksLenOrd = SOME EQUAL
        then
          let
            val eOrd = compareExprs e1 e2
          in
            if
              eOrd = NONE orelse eOrd = SOME EQUAL
            then
              compareSubstitutions s1 s2
            else
              eOrd
          end
        else
          tksLenOrd
      end
    | compareSubstitutions (BS_BecomesElt (es1, re1)) (BS_BecomesElt (es2, re2)) =
      let
        val esLenOrd = SOME (Int.compare ((List.length es1), (List.length es2))) (* 左辺の変数の数が少ない方が先 *)
      in
        if
          esLenOrd = SOME EQUAL
        then
          let
            val esOrd = compareExprLists es1 es2
          in
            if
              esOrd = NONE orelse esOrd = SOME EQUAL
            then
              compareExprs re1 re2
            else
              esOrd
          end
        else
          esLenOrd
      end
    | compareSubstitutions (BS_BecomesSuchThat (es1, BP e1)) (BS_BecomesSuchThat (es2, BP e2)) =
      let
        val esLenOrd = SOME (Int.compare ((List.length es1), (List.length es2))) (* 左辺の変数の数が少ない方が先 *)
      in
        if
          esLenOrd = SOME EQUAL
        then
          let
            val esOrd = compareExprMultiSets es1 es2
          in
            if
              esOrd = NONE orelse esOrd = SOME EQUAL
            then
              compareExprs e1 e2
            else
              esOrd
          end
        else
          esLenOrd
      end
    | compareSubstitutions (BS_Call (_, oparams1, iparams1)) (BS_Call (_, oparams2, iparams2)) = (* 不要かも *)
      let
        val oparamsLenOrd = SOME (Int.compare ((List.length oparams2), (List.length oparams1)))
      in
        if
          oparamsLenOrd = SOME EQUAL
        then
          let
            val iparamsLenOrd = SOME (Int.compare ((List.length iparams2), (List.length iparams1)))
          in
            if
              iparamsLenOrd = SOME EQUAL
            then
              let
                val oparamsOrd = compareExprLists oparams1 oparams2
              in
                if
                  oparamsOrd = NONE orelse oparamsOrd = SOME EQUAL
                then
                  compareExprLists iparams1 iparams2
                else
                  oparamsOrd
              end
            else
              iparamsLenOrd
          end
        else
          oparamsLenOrd
      end
    | compareSubstitutions (BS_BecomesEqual (e11,  e12)) (BS_BecomesEqual (e21, e22)) =
      let
        val e1Ord = compareExprs e11 e21
      in
        if
          e1Ord = NONE orelse e1Ord = SOME EQUAL
        then
          compareExprs e12 e22
        else
          e1Ord
      end
    | compareSubstitutions (BS_Simultaneous l1) (BS_Simultaneous l2) =
      let
        val lLenOrd = SOME (Int.compare ((List.length l2), (List.length l1)))
      in
        if
          lLenOrd = SOME EQUAL
        then
          compareSubstitutionMultiSets l1 l2
        else
          lLenOrd
      end
    | compareSubstitutions (BS_Let _)                _                       = raise SortError "LET substitution"
    | compareSubstitutions _                         (BS_Let _)              = raise SortError "LET substitution"
    | compareSubstitutions (BS_Select _)             _                       = raise SortError "SELECT substitution"
    | compareSubstitutions _                         (BS_Select _)           = raise SortError "SELECT substitution"
    | compareSubstitutions (BS_Case _)               _                       = raise SortError "CASE substitution"
    | compareSubstitutions _                         (BS_Case _)             = raise SortError "CASE substitution"
    | compareSubstitutions (BS_BecomesEqualList _)   _                       = raise SortError "a, b := c, d style substitution"
    | compareSubstitutions _                         (BS_BecomesEqualList _) = raise SortError "a, b := c, d style substitution"
    | compareSubstitutions s1 s2 =
      let
        fun sbstToWeight BS_Identity = 12
          | sbstToWeight (BS_BecomesEqual _) = 11
          | sbstToWeight (BS_BecomesElt _) = 10
          | sbstToWeight (BS_BecomesSuchThat _) = 9
          | sbstToWeight (BS_Call _) = 8
          | sbstToWeight (BS_Block _) = 7
          | sbstToWeight (BS_Precondition _) = 6
          | sbstToWeight (BS_Assertion _) = 5
          | sbstToWeight (BS_Choice _) = 4
          | sbstToWeight (BS_If _) = 3
          | sbstToWeight (BS_Select _) = 2
          | sbstToWeight (BS_Any _) = 1
          | sbstToWeight _ = raise SortError "not primitive substitution"
      in
        SOME (Int.compare ((sbstToWeight s1), (sbstToWeight s2)))
      end
    and
      compareSubstitutionLists []          []          = SOME EQUAL
    | compareSubstitutionLists _           []          = raise SortError "substitution lists have different length"
    | compareSubstitutionLists []          _           = raise SortError "substitution lists have different length"
    | compareSubstitutionLists (s1 :: ss1) (s2 :: ss2) =
      let
        val headOrd = compareSubstitutions s1 s2
        val tailOrd = compareSubstitutionLists ss1 ss2
      in
        case (headOrd, tailOrd) of
          (SOME EQUAL, _         ) => tailOrd
        | (NONE,       NONE      ) => NONE
        | (NONE,       SOME EQUAL) => NONE
        | (NONE,       _         ) => tailOrd
        | _                        => headOrd
      end
    and
      compareSubstitutionMultiSets l1 l2 =
      if
        Utils.eqAsMset (fn s1 => fn s2 => compareSubstitutions s1 s2 = SOME EQUAL) l1 l2
      then
        SOME EQUAL
      else
        let
          val relationList = List.concat (List.map (fn s1 => List.map (fn s2 => compareSubstitutions s1 s2) l2) l1)
          val numberOfNone    = List.length (List.filter (Utils.eqto NONE          ) relationList)
          val numberOfLess    = List.length (List.filter (Utils.eqto (SOME LESS   )) relationList)
          val numberOfGreater = List.length (List.filter (Utils.eqto (SOME GREATER)) relationList)
        in
          if
            numberOfNone = 0 andalso numberOfLess = numberOfGreater
          then
            (* 2つの多重集合から1個ずつ要素を取ってきたときその間の順序が全て決定しており、その個数が拮抗したとき *)
            NONE (* とりあえずNONEにするが後で変更の可能性あり *) (* TODO *)
          else
            if
              numberOfNone + numberOfGreater < numberOfLess
            then
              SOME LESS
            else
              if
                numberOfNone + numberOfLess < numberOfGreater
              then
                SOME GREATER
              else
                NONE
        end

  fun addRelationBySubExpr e1 e2 =
      let
        val NumberOfLessRelations    = List.length (List.filter (fn (le, ge) => AST.isSubExpr e1 le andalso AST.isSubExpr e2 ge) (!relationPool))
        val NumberOfGreaterRelations = List.length (List.filter (fn (le, ge) => AST.isSubExpr e2 le andalso AST.isSubExpr e1 ge) (!relationPool))
      in
        if
          NumberOfLessRelations < NumberOfGreaterRelations
        then
          addRelation (e2, e1)
        else if
          NumberOfLessRelations > NumberOfGreaterRelations
        then
          addRelation (e1, e2)
        else
          ()(* 部分式の関係が拮抗していた場合 *)
      end

  fun getOrderInExprList l = List.app (fn e1 => List.app (fn e2 => if compareExprs e1 e2 = NONE then addRelationBySubExpr e1 e2 else ()) l) l

  fun getOrderOfVars [v] = ()
    | getOrderOfVars vs =
      let
        val exprs = List.map (fn v => BE_Leaf (NONE, v)) vs
      in
        getOrderInExprList exprs
      end

  fun isFixed (f : 'a -> 'a -> order option) l = List.all (fn e1 => List.all (fn e2 => f e1 e2 <> NONE) l) l (* 一意にソート可能であるかを判定 *)

  fun getOrderInExpr (BE_Node2       (_ , Keyword "=", e1, e2)) = getOrderInExprList [e1, e2]
    | getOrderInExpr (BE_ExSet       (_ , l       )) = getOrderInExprList l
    | getOrderInExpr (BE_InSet       (_ , vs, _   )) = getOrderOfVars vs
    | getOrderInExpr (BE_ForAll      (vs, _ , _   )) = getOrderOfVars vs
    | getOrderInExpr (BE_Exists      (vs, _       )) = getOrderOfVars vs
    | getOrderInExpr (BE_Lambda      (_ , vs, _, _)) = getOrderOfVars vs
    | getOrderInExpr (BE_Inter       (_ , vs, _, _)) = getOrderOfVars vs
    | getOrderInExpr (BE_Union       (_ , vs, _, _)) = getOrderOfVars vs
    | getOrderInExpr (BE_Commutative (_ , _ , l   )) = getOrderInExprList l
    | getOrderInExpr e                               = ()

  fun sortExprList l = ListMergeSort.sort (fn (e1, e2) => compareExprs e1 e2 = SOME GREATER) l (* 引数のリストの要素のうちどの2つをとっても順序が定まっているときにしか実行しない前提 *)

  fun getOrderInTopExprTree (BE_Leaf   _                          ) = ()
    | getOrderInTopExprTree (BE_Node1  (_   , _    , e           )) = getOrderInTopExprTree e

    | getOrderInTopExprTree (equalExpr as (BE_Node2 (_, Keyword "=", e1, e2))) =
      if
        isFixed compareExprs [e1, e2]
      then
        List.app getOrderInTopExprTree (sortExprList [e1, e2])
      else
        AST.appExprTree getOrderInExpr equalExpr

    | getOrderInTopExprTree (BE_Node2  (_   , _    , e1   , e2   )) = (addRelation (e1, e2); getOrderInTopExprTree e1; getOrderInTopExprTree e2)
    | getOrderInTopExprTree (BE_NodeN  (_   , _    , l           )) = (addRelationList l; List.app getOrderInTopExprTree l)
    | getOrderInTopExprTree (BE_Fnc    (_   , e1   , e2          )) = (addRelation (e1, e2); getOrderInTopExprTree e1; getOrderInTopExprTree e2)
    | getOrderInTopExprTree (BE_Img    (_   , e1   , e2          )) = (addRelation (e1, e2); getOrderInTopExprTree e1; getOrderInTopExprTree e2)
    | getOrderInTopExprTree (BE_Bool   (BP e                     )) = getOrderInTopExprTree e
    | getOrderInTopExprTree (commutativeExpr as (BE_ExSet (_, l))) =
      if
        isFixed compareExprs l
      then
        List.app getOrderInTopExprTree (sortExprList l) (* オペランドの順序が既に定まっている場合 *)
      else
        AST.appExprTree getOrderInExpr commutativeExpr (* オペランドが可換 *)
    | getOrderInTopExprTree (BE_InSet  (_   , _    , BP e        )) = getOrderInTopExprTree e (* 変数宣言が可換 *)
    | getOrderInTopExprTree (BE_Seq    (_   , l                  )) = (addRelationList l; List.app getOrderInTopExprTree l)
    | getOrderInTopExprTree (BE_ForAll (vs  , BP e1, BP e2       )) = (addRelation (e1, e2); getOrderInTopExprTree e1; getOrderInTopExprTree e2; getOrderOfVars vs)(* 変数宣言が可換 *)
    | getOrderInTopExprTree (BE_Exists (vs  , BP e               )) = (getOrderInTopExprTree e; getOrderOfVars vs)(* 変数宣言が可換 *)
    | getOrderInTopExprTree (BE_Lambda (_   , vs   , BP e1, e2   )) = (addRelation (e1, e2); getOrderInTopExprTree e1; getOrderInTopExprTree e2; getOrderOfVars vs)(* 変数宣言が可換 *)
    | getOrderInTopExprTree (BE_Sigma  (_   , _    , BP e1, e2   )) = (addRelation (e1, e2); getOrderInTopExprTree e1; getOrderInTopExprTree e2)
    | getOrderInTopExprTree (BE_Pi     (_   , _    , BP e1, e2   )) = (addRelation (e1, e2); getOrderInTopExprTree e1; getOrderInTopExprTree e2)
    | getOrderInTopExprTree (BE_Inter  (_   , vs   , BP e1, e2   )) = (addRelation (e1, e2); getOrderInTopExprTree e1; getOrderInTopExprTree e2; getOrderOfVars vs)(* 変数宣言が可換 *)
    | getOrderInTopExprTree (BE_Union  (_   , vs   , BP e1, e2   )) = (addRelation (e1, e2); getOrderInTopExprTree e1; getOrderInTopExprTree e2; getOrderOfVars vs)(* 変数宣言が可換 *)
    | getOrderInTopExprTree (commutativeExpr as (BE_Commutative (_, _, l))) =
      if
        isFixed compareExprs l
      then
        List.app getOrderInTopExprTree (sortExprList l) (* オペランドの順序が既に定まっている場合 *)
      else
        AST.appExprTree getOrderInExpr commutativeExpr (* オペランドが可換 *)
    (* レコード関連は保留 *)
    | getOrderInTopExprTree _ = raise SortError "record expression is not supported"

  (* 引数をcompareSubstitutionsに渡したときの返り値がNONEとなる前提で書く *)
  fun addRelationBySubExprInSubstitutionTrees (BS_Block            s1                ) (BS_Block            s2                ) = addRelationBySubExprInSubstitutionTrees s1 s2
    | addRelationBySubExprInSubstitutionTrees BS_Identity                              BS_Identity                              = ()
    | addRelationBySubExprInSubstitutionTrees (BS_Precondition     (BP e1, s1       )) (BS_Precondition     (BP e2, s2       )) = (addRelationBySubExpr e1 e2; addRelationBySubExprInSubstitutionTrees s1 s2)
    | addRelationBySubExprInSubstitutionTrees (BS_Assertion        (BP e1, s1       )) (BS_Assertion        (BP e2, s2       )) = (addRelationBySubExpr e1 e2; addRelationBySubExprInSubstitutionTrees s1 s2)
    | addRelationBySubExprInSubstitutionTrees (BS_Choice           l1                ) (BS_Choice           l2                ) = List.app (fn s1 => List.app (fn s2 => addRelationBySubExprInSubstitutionTrees s1 s2) l2) l1
    | addRelationBySubExprInSubstitutionTrees (BS_If               l1                ) (BS_If               l2                ) = (ListPair.app (fn ((SOME (BP e1), _), (SOME (BP e2), _)) => addRelationBySubExpr e1 e2
                                                                                                                                                  | _                                      => ())
                                                                                                                                                (l1, l2);
                                                                                                                                   ListPair.app (fn (b1, b2) => addRelationBySubExprInSubstitutionTrees (#2(b1)) (#2(b2))) (l1, l2))
    | addRelationBySubExprInSubstitutionTrees (BS_Select           l1                ) (BS_Select           l2                ) = (ListPair.app (fn ((SOME (BP e1), _), (SOME (BP e2), s2)) => addRelationBySubExpr e1 e2
                                                                                                                                                  | _                                       => ())
                                                                                                                                                (l1, l2);
                                                                                                                                   ListPair.app (fn (b1, b2) => addRelationBySubExprInSubstitutionTrees (#2(b1)) (#2(b2))) (l1, l2))
    | addRelationBySubExprInSubstitutionTrees (BS_Case             _                 ) _                                        = raise SortError "not primitive substitution"
    | addRelationBySubExprInSubstitutionTrees _                                        (BS_Case             _                 ) = raise SortError "not primitive substitution"
    | addRelationBySubExprInSubstitutionTrees (BS_Any              (_    , BP e1, s1)) (BS_Any              (_    , BP e2, s2)) = (addRelationBySubExpr e1 e2; addRelationBySubExprInSubstitutionTrees s1 s2)
    | addRelationBySubExprInSubstitutionTrees (BS_Let              _                 ) _                                        = raise SortError "not primitive substitution"
    | addRelationBySubExprInSubstitutionTrees _                                        (BS_Let              _                 ) = raise SortError "not primitive substitution"
    | addRelationBySubExprInSubstitutionTrees (BS_BecomesElt       (l1   , e1       )) (BS_BecomesElt       (l2   , e2       )) = (ListPair.app (Utils.uncurry addRelationBySubExpr) (l1, l2); addRelationBySubExpr e1 e2)
    | addRelationBySubExprInSubstitutionTrees (BS_BecomesSuchThat  (l1   , BP e1    )) (BS_BecomesSuchThat  (l2   , BP e2    )) = (List.app (fn elm1 => List.app (fn elm2 => addRelationBySubExpr elm1 elm2) l2) l1; addRelationBySubExpr e1 e2)
    | addRelationBySubExprInSubstitutionTrees (BS_Call             (_    , o1   , i1)) (BS_Call             (_    , o2   , i2)) = (ListPair.app (Utils.uncurry addRelationBySubExpr) (o1, o2); ListPair.app (Utils.uncurry addRelationBySubExpr) (i1, i2))
    | addRelationBySubExprInSubstitutionTrees (BS_BecomesEqual     (e11  , e12      )) (BS_BecomesEqual     (e21  , e22      )) = (addRelationBySubExpr e11 e21; addRelationBySubExpr e12 e22)
    | addRelationBySubExprInSubstitutionTrees (BS_BecomesEqualList _                 ) _                                        = raise SortError "not primitive substitution"
    | addRelationBySubExprInSubstitutionTrees _                                        (BS_BecomesEqualList _                 ) = raise SortError "not primitive substitution"
    | addRelationBySubExprInSubstitutionTrees (BS_Simultaneous     l1                ) (BS_Simultaneous     l2                ) = List.app (fn s1 => List.app (fn s2 => addRelationBySubExprInSubstitutionTrees s1 s2) l2) l1
    | addRelationBySubExprInSubstitutionTrees _                                        _                                        = raise SortError "substitution for IMPLEMENTATION"

  fun getOrderInSubstitutionList l = List.app (fn s1 => List.app (fn s2 => if compareSubstitutions s1 s2 = NONE then addRelationBySubExprInSubstitutionTrees s1 s2 else ()) l) l

  fun getOrderInSubstitution (BS_Choice l) = getOrderInSubstitutionList l
    | getOrderInSubstitution (BS_Any (vs, _, _)) = getOrderOfVars vs
    | getOrderInSubstitution (BS_Simultaneous l) = getOrderInSubstitutionList l
    | getOrderInSubstitution _ = ()

  fun sortSubstitutionList l = ListMergeSort.sort (fn (s1, s2) => compareSubstitutions s1 s2 = SOME GREATER) l (* 引数のリストの要素のうちどの2つをとっても順序が定まっているときにしか実行しない前提 *)

  fun getOrderInTopSubstitutionTree (BS_Block            s                ) = getOrderInTopSubstitutionTree s
    | getOrderInTopSubstitutionTree BS_Identity                             = ()
    | getOrderInTopSubstitutionTree (BS_Precondition     (BP e, s        )) = (getOrderInTopExprTree e; getOrderInTopSubstitutionTree s)
    | getOrderInTopSubstitutionTree (BS_Assertion        (BP e, s        )) = (getOrderInTopExprTree e; getOrderInTopSubstitutionTree s)
    | getOrderInTopSubstitutionTree (BS_Choice           l                ) =
      if
        isFixed compareSubstitutions l
      then
        List.app getOrderInTopSubstitutionTree (sortSubstitutionList l)
      else
        AST.appSubstitutionTree getOrderInSubstitution (BS_Choice l)
    | getOrderInTopSubstitutionTree (BS_If               l                ) = List.app (fn (NONE, s       ) => getOrderInTopSubstitutionTree s
                                                                                         | (SOME (BP e), s) => (getOrderInTopExprTree e; getOrderInTopSubstitutionTree s)) l
    | getOrderInTopSubstitutionTree (BS_Select           l                ) = List.app (fn (NONE, s       ) => getOrderInTopSubstitutionTree s
                                                                                         | (SOME (BP e), s) => (getOrderInTopExprTree e; getOrderInTopSubstitutionTree s)) l
    | getOrderInTopSubstitutionTree (BS_Case             (e   , l        )) = raise SortError "not primitive substitution"
    | getOrderInTopSubstitutionTree (BS_Any              (vs  , BP e, s  )) = (getOrderInTopExprTree e; getOrderInTopSubstitutionTree s; getOrderOfVars vs)
    | getOrderInTopSubstitutionTree (BS_Let              (l   , s        )) = raise SortError "not primitive substitution"
    | getOrderInTopSubstitutionTree (BS_BecomesElt       (l   , e        )) = (getOrderInExprList l; getOrderInTopExprTree e; addRelations (l, [e]))
    | getOrderInTopSubstitutionTree (BS_BecomesSuchThat  (l   , BP e     )) = (List.app (AST.appExprTree getOrderInExpr) l; getOrderInTopExprTree e; List.app (fn elm => addRelation (elm, e)) l)
    | getOrderInTopSubstitutionTree (BS_Call             (_   , outs, ins)) = (getOrderInExprList outs; getOrderInExprList ins; addRelations (outs, ins)) (* 操作パラメータの順番は変えない *)
    | getOrderInTopSubstitutionTree (BS_BecomesEqual     (e1  , e2       )) = (getOrderInTopExprTree e1; getOrderInTopExprTree e2; addRelation (e1, e2))
    | getOrderInTopSubstitutionTree (BS_BecomesEqualList _                ) = raise SortError "not primitive substitution"
    | getOrderInTopSubstitutionTree (BS_Simultaneous     l                ) =
      if
        isFixed compareSubstitutions l
           then
        List.app getOrderInTopSubstitutionTree (sortSubstitutionList l)
      else
        AST.appSubstitutionTree getOrderInSubstitution (BS_Simultaneous l)
    | getOrderInTopSubstitutionTree _                                       = raise SortError "substitution for IMPLEMENTATION"

  fun sortClauseList l = ListMergeSort.sort (fn (c1, c2) => #2 (valOf (List.find (fn (ss1, _) => Stringify.clauseToClauseName c1 = ss1) Keywords.clauseKeywords)) >= #2 (valOf (List.find (fn (ss2, _) => Stringify.clauseToClauseName c2 = ss2) Keywords.clauseKeywords))) l

  (*************************************** 以下ランダム順序追加用関数 ***************************************)

  fun addRandomRelation e1 e2 = if (*randomBool ()*)true then addRelation (e1, e2) else addRelation (e2, e1)

  fun addRandomRelationInExprList l = List.app (fn e1 => List.app (fn e2 => if compareExprs e1 e2 = NONE then addRandomRelation e1 e2 else ()) l) l

  fun addRandomRelationInVarList vs = addRandomRelationInExprList (List.map (fn v => BE_Leaf (NONE, v)) vs)

  fun addRandomRelationInExpr (BE_Node2       (_ , Keyword "=", e1, e2)) = if compareExprs e1 e2 = NONE then addRandomRelation e1 e2 else ()
    | addRandomRelationInExpr (BE_ExSet       (_ , l                  )) = addRandomRelationInExprList l
    | addRandomRelationInExpr (BE_InSet       (_ , vs         , _     )) = addRandomRelationInVarList vs
    | addRandomRelationInExpr (BE_ForAll      (vs, _          , _     )) = addRandomRelationInVarList vs
    | addRandomRelationInExpr (BE_Exists      (vs, _                  )) = addRandomRelationInVarList vs
    | addRandomRelationInExpr (BE_Lambda      (_ , vs         , _ , _ )) = addRandomRelationInVarList vs
    | addRandomRelationInExpr (BE_Inter       (_ , vs         , _ , _ )) = addRandomRelationInVarList vs
    | addRandomRelationInExpr (BE_Union       (_ , vs         , _ , _ )) = addRandomRelationInVarList vs
    | addRandomRelationInExpr (BE_Commutative (_ , _          , l     )) = addRandomRelationInExprList l
    | addRandomRelationInExpr e                                          = ()

  fun addRandomRelationInExprTree e = AST.appExprTree addRandomRelationInExpr e

  (* 現時点で compareSubstitutions に与えるとNONEになる代入文同士を比較して、対応する部分の関係をランダムに追加する *)
  fun addRandomRelationInSubstitutionTrees (BS_Block            s1                ) (BS_Block            s2                ) = addRandomRelationInSubstitutionTrees s1 s2
    | addRandomRelationInSubstitutionTrees BS_Identity                              BS_Identity                              = ()
    | addRandomRelationInSubstitutionTrees (BS_Precondition     (BP e1, s1       )) (BS_Precondition     (BP e2, s2       )) = (addRandomRelation e1 e2; addRandomRelationInSubstitutionTrees s1 s2)
    | addRandomRelationInSubstitutionTrees (BS_Assertion        (BP e1, s1       )) (BS_Assertion        (BP e2, s2       )) = (addRandomRelation e1 e2; addRandomRelationInSubstitutionTrees s1 s2)
    | addRandomRelationInSubstitutionTrees (BS_Choice           l1                ) (BS_Choice           l2                ) = List.app (fn s1 => List.app (fn s2 => addRandomRelationInSubstitutionTrees s1 s2) l2) l1
    | addRandomRelationInSubstitutionTrees (BS_If               l1                ) (BS_If               l2                ) = (ListPair.app (fn ((SOME (BP e1), _), (SOME (BP e2), _)) => addRandomRelation e1 e2
                                                                                                                                                  | _                                      => ())
                                                                                                                                                (l1, l2);
                                                                                                                                   ListPair.app (fn (b1, b2) => addRandomRelationInSubstitutionTrees (#2(b1)) (#2(b2))) (l1, l2))
    | addRandomRelationInSubstitutionTrees (BS_Select           l1                ) (BS_Select           l2                ) = (ListPair.app (fn ((SOME (BP e1), _), (SOME (BP e2), s2)) => addRandomRelation e1 e2
                                                                                                                                                  | _                                       => ())
                                                                                                                                                (l1, l2);
                                                                                                                                   ListPair.app (fn (b1, b2) => addRandomRelationInSubstitutionTrees (#2(b1)) (#2(b2))) (l1, l2))
    | addRandomRelationInSubstitutionTrees (BS_Any              (_    , BP e1, s1)) (BS_Any              (_    , BP e2, s2)) = (addRandomRelation e1 e2; addRandomRelationInSubstitutionTrees s1 s2)
    | addRandomRelationInSubstitutionTrees (BS_BecomesElt       (l1   , e1       )) (BS_BecomesElt       (l2   , e2       )) = (ListPair.app (Utils.uncurry addRandomRelation) (l1, l2); addRandomRelation e1 e2)
    | addRandomRelationInSubstitutionTrees (BS_BecomesSuchThat  (l1   , BP e1    )) (BS_BecomesSuchThat  (l2   , BP e2    )) = (List.app (fn elm1 => List.app (fn elm2 => addRandomRelation elm1 elm2) l2) l1; addRandomRelation e1 e2)
    | addRandomRelationInSubstitutionTrees (BS_Call             (_    , o1   , i1)) (BS_Call             (_    , o2   , i2)) = (ListPair.app (Utils.uncurry addRandomRelation) (o1, o2); ListPair.app (Utils.uncurry addRandomRelation) (i1, i2))
    | addRandomRelationInSubstitutionTrees (BS_BecomesEqual     (e11  , e12      )) (BS_BecomesEqual     (e21  , e22      )) = (addRandomRelation e11 e21; addRandomRelation e12 e22)
    | addRandomRelationInSubstitutionTrees (BS_Simultaneous     l1                ) (BS_Simultaneous     l2                ) = List.app (fn s1 => List.app (fn s2 => addRandomRelationInSubstitutionTrees s1 s2) l2) l1
    | addRandomRelationInSubstitutionTrees _                                        _                                        = raise SortError "sorting is only for models"

  fun addRandomRelationInSubstitutionList l = List.app (fn s1 => List.app (fn s2 => if compareSubstitutions s1 s2 = NONE then addRandomRelationInSubstitutionTrees s1 s2 else ()) l) l

  fun addRandomRelationInSubstitution (BS_Assertion (BP e, _)) = addRandomRelationInExprTree e
    | addRandomRelationInSubstitution (BS_Choice l) = addRandomRelationInSubstitutionList l
    | addRandomRelationInSubstitution (BS_If l) = List.app (fn (NONE, _) => () | (SOME (BP e), _) => addRandomRelationInExprTree e) l
    | addRandomRelationInSubstitution (BS_Select l) = List.app (fn (NONE, _) => () | (SOME (BP e), _) => addRandomRelationInExprTree e) l
    | addRandomRelationInSubstitution (BS_Any (vs, BP e, _)) = (addRandomRelationInVarList vs; addRandomRelationInExprTree e)
    | addRandomRelationInSubstitution (BS_BecomesElt (el, re)) = (List.app addRandomRelationInExprTree el; addRandomRelationInExprTree re)
    | addRandomRelationInSubstitution (BS_BecomesSuchThat (el, BP e)) = (addRandomRelationInExprList el; List.app addRandomRelationInExprTree el; addRandomRelationInExprTree e)
    | addRandomRelationInSubstitution (BS_Call (_, el1, el2)) = List.app addRandomRelationInExprTree (el1 @ el2)
    | addRandomRelationInSubstitution (BS_BecomesEqual (e1, e2)) = (addRandomRelationInExprTree e1; addRandomRelationInExprTree e2)
    | addRandomRelationInSubstitution (BS_Simultaneous l) = addRandomRelationInSubstitutionList l
    | addRandomRelationInSubstitution s = () (* 事前条件は除く *)

  fun addRandomRelationInSubstitutionTree s = AST.appSubstitutionTree addRandomRelationInSubstitution s

  fun addRandomRelationInTypes l =
      let
        fun typeToExpr (BT_Enum (t, _)) = BE_Leaf (NONE, Var t)
          | typeToExpr (BT_Deferred t)  = BE_Leaf (NONE, Var t)
          | typeToExpr _ = raise SortError ""
        val _ = addRandomRelationInExprList (List.map typeToExpr l)
        val sorted = ListMergeSort.sort (fn (t1, t2) => compareExprs (typeToExpr t1) (typeToExpr t2) = SOME GREATER) l
      in
        List.app (fn (BT_Enum (_, l)) => addRandomRelationInExprList (List.map (fn s => BE_Leaf (NONE, Var s)) l) | _ => ()) sorted
      end

  fun addRandomRelationInOperation (BOp (_, outputs, inputs, s)) = (addRandomRelationInVarList outputs; addRandomRelationInVarList inputs; addRandomRelationInSubstitutionTree s)

  fun addRandomRelationInClause (BC_CONSTRAINTS (BP e)) = addRandomRelationInExprTree e
    | addRandomRelationInClause (BC_PROPERTIES  (BP e)) = addRandomRelationInExprTree e
    | addRandomRelationInClause (BC_INVARIANT   (BP e)) = addRandomRelationInExprTree e
    | addRandomRelationInClause (BC_ACONSTANTS vs) = addRandomRelationInVarList vs
    | addRandomRelationInClause (BC_CCONSTANTS vs) = addRandomRelationInVarList vs
    | addRandomRelationInClause (BC_AVARIABLES vs) = addRandomRelationInVarList vs
    | addRandomRelationInClause (BC_CVARIABLES vs) = addRandomRelationInVarList vs
    | addRandomRelationInClause (BC_SETS ts) = addRandomRelationInTypes ts
    | addRandomRelationInClause (BC_OPERATIONS [opr]) = addRandomRelationInOperation opr
    | addRandomRelationInClause _ = ()

  (* 可換な部分について全て順序が求められているかを調べ、定まっていない場合はランダムに順序を決定して追加 (事前条件以外) *)
  fun addRandomRelationInComponent (BMch (_, machineParameters, clauses)) =
      (
        addRandomRelationInVarList machineParameters;

        let
          val sortedClauses = sortClauseList clauses
        in
          List.app addRandomRelationInClause sortedClauses
        end)
    | addRandomRelationInComponent _ = raise SortError "sorting is only for models"

  (*************************************** 以下ソート用関数 ***************************************)

  (* sortExprList の定義は↑ *)

  fun sortVarList vs = List.map (fn (BE_Leaf (NONE, v)) => v | _ => raise SortError "") (sortExprList (List.map (fn v => BE_Leaf (NONE, v)) vs))

  (* 再帰なし *)
  fun sortExpr (BE_Node2 (to, Keyword "=", e1, e2)) = (case compareExprs e1 e2 of
                                                         NONE         => raise SortError "missing relation"
                                                       | SOME GREATER => BE_Node2 (to, Keyword "=", e2, e1)
                                                       | _            => BE_Node2 (to, Keyword "=", e1, e2))
    | sortExpr (BE_ExSet (to, l)) = BE_ExSet (to, sortExprList l)
    | sortExpr (BE_InSet (to, vs, p)) = BE_InSet (to, sortVarList vs, p)
    | sortExpr (BE_ForAll (vs, p1, p2)) = BE_ForAll (sortVarList vs, p1, p2)
    | sortExpr (BE_Exists (vs, p)) = BE_Exists (sortVarList vs, p)
    | sortExpr (BE_Lambda (to, vs, p, e)) = BE_Lambda (to, sortVarList vs, p, e)
    | sortExpr (BE_Inter (to, vs, p, e)) = BE_Inter (to, sortVarList vs, p, e)
    | sortExpr (BE_Union (to, vs, p, e)) = BE_Union (to, sortVarList vs, p, e)
    (* レコードは保留 *)
    | sortExpr (BE_Commutative (to, operator, l)) = BE_Commutative (to, operator, sortExprList l)
    | sortExpr e = e

  fun sortSubstitutionList l = ListMergeSort.sort (fn (s1, s2) => compareSubstitutions s1 s2 = SOME GREATER) l

  (* 再帰あり*)
  fun sortExprTree e = AST.mapExprTree sortExpr e

  (* 再帰なし *) (* sortExprTreeを呼ぶ *)
  fun sortSubstitution (BS_Precondition (BP e, s)) = BS_Precondition (BP (sortExprTree e), s)
    | sortSubstitution (BS_Assertion (BP e, s)) = BS_Assertion (BP (sortExprTree e), s)
    | sortSubstitution (BS_Choice l) = BS_Choice (sortSubstitutionList l)
    | sortSubstitution (BS_If     l) = BS_If     (List.map (fn (SOME (BP e), s) => (SOME (BP (sortExprTree e)), s) | x => x) l)
    | sortSubstitution (BS_Select l) = BS_Select (List.map (fn (SOME (BP e), s) => (SOME (BP (sortExprTree e)), s) | x => x) l)
    | sortSubstitution (BS_Any (vs, BP e, s)) = BS_Any (sortVarList vs, BP (sortExprTree e), s)
    | sortSubstitution (BS_BecomesElt (el, re)) = BS_BecomesElt (List.map sortExprTree el, sortExprTree re)
    | sortSubstitution (BS_BecomesSuchThat (el, BP e)) = BS_BecomesSuchThat (sortExprList (List.map sortExprTree el), BP (sortExprTree e))
    | sortSubstitution (BS_Call (opName, outputs, inputs)) = BS_Call (opName, List.map sortExprTree outputs, List.map sortExprTree inputs)
    | sortSubstitution (BS_BecomesEqual (e1, e2)) = BS_BecomesEqual (sortExprTree e1, sortExprTree e2)
    | sortSubstitution (BS_Simultaneous l) = BS_Simultaneous (sortSubstitutionList l)
    | sortSubstitution s = s

  fun sortSubstitutionTree s = AST.mapSubstitutionTree sortSubstitution s

  fun sortTypes l =
      let
        val elementsSorted = List.map (fn (BT_Enum (typeSet, elements)) => BT_Enum (typeSet, List.map (fn (Var x) => x | _ => raise SortError "") (sortVarList (List.map (fn x => Var x) elements))) | deferred => deferred) l
        fun typeToExpr (BT_Enum (t, _)) = BE_Leaf (NONE, Var t)
          | typeToExpr (BT_Deferred t)  = BE_Leaf (NONE, Var t)
          | typeToExpr _ = raise SortError ""
      in
        ListMergeSort.sort (fn (t1, t2) => compareExprs (typeToExpr t1) (typeToExpr t2) = SOME GREATER) elementsSorted
      end

  fun sortOperation (BOp (operationName, outputs, inputs, substitution)) = BOp (operationName, sortVarList outputs, sortVarList inputs, sortSubstitutionTree substitution)

  fun sortClause (BC_CONSTRAINTS (BP e)) = BC_CONSTRAINTS (BP (sortExprTree e))
    | sortClause (BC_PROPERTIES  (BP e)) = BC_PROPERTIES  (BP (sortExprTree e))
    | sortClause (BC_INVARIANT   (BP e)) = BC_INVARIANT   (BP (sortExprTree e))
    | sortClause (BC_ACONSTANTS vs) = BC_ACONSTANTS (sortVarList vs)
    | sortClause (BC_CCONSTANTS vs) = BC_CCONSTANTS (sortVarList vs)
    | sortClause (BC_AVARIABLES vs) = BC_AVARIABLES (sortVarList vs)
    | sortClause (BC_CVARIABLES vs) = BC_CVARIABLES (sortVarList vs)
    | sortClause (BC_SETS ts) = BC_SETS (sortTypes ts)
    | sortClause (BC_OPERATIONS [opr]) = BC_OPERATIONS [(sortOperation opr)]
    | sortClause x = x

  fun sort (inputModel as (BMch (machineName, machineParameters, clauses))) =
      (relationPool := [];
      addStaticRelations inputModel;
      let
        val operation = case (List.find (fn (BC_OPERATIONS [_]) => true | _ => false) clauses) of (SOME (BC_OPERATIONS [opr])) => opr | _ => raise SortError ""
        val machineParameterExprList = List.map (fn v => BE_Leaf (NONE, v)) machineParameters
        val userTypeSetList = (List.filter TypeInference.isTypeSetByName (List.map (fn (Var x) => x | _ => raise SortError "") machineParameters)) @
                              (case List.find (fn (BC_SETS _) => true | _ => false) clauses of
                                 NONE             => []
                               | SOME (BC_SETS l) => List.map (fn (BT_Enum (x, _)) => x | (BT_Deferred x) => x | _ => raise SortError "") l
                               | _                => raise SortError "")
        val setExprList = case List.find (fn (BC_SETS _) => true | _ => false) clauses of
                            NONE             => []
                          | SOME (BC_SETS l) => List.concat (List.map (fn (ty as BT_Enum     (typeSet, elements)) => (BE_Leaf (SOME (BT_Power (SOME ty)), Var typeSet)) :: (List.map (fn element => (BE_Leaf (NONE, Var element))) elements)
                                                                        | (ty as BT_Deferred typeSet            ) => [(BE_Leaf (SOME (BT_Power (SOME ty)), Var typeSet))]
                                                                        | _                                 => raise SortError "") l)
                          | _                => raise SortError ""
        val aconstantsExprList = case (List.find (fn (BC_ACONSTANTS _) => true | _ => false) clauses) of
                               NONE                   => []
                             | SOME (BC_ACONSTANTS l) => List.map (fn v => BE_Leaf (NONE, v)) l
                             | _                      => raise SortError ""
        val cconstantsExprList = case (List.find (fn (BC_CCONSTANTS _) => true | _ => false) clauses) of
                               NONE                   => []
                             | SOME (BC_CCONSTANTS l) => List.map (fn v => BE_Leaf (NONE, v)) l
                             | _                      => raise SortError ""
        val avariablesExprList = case (List.find (fn (BC_AVARIABLES _) => true | _ => false) clauses) of
                               NONE                   => []
                             | SOME (BC_AVARIABLES l) => List.map (fn v => BE_Leaf (NONE, v)) l
                             | _                      => raise SortError ""
        val cvariablesExprList = case (List.find (fn (BC_CVARIABLES _) => true | _ => false) clauses) of
                               NONE                   => []
                             | SOME (BC_CVARIABLES l) => List.map (fn v => BE_Leaf (NONE, v)) l
                             | _                      => raise SortError ""

        val operationParameterExprList = case operation of (BOp (_, outputs, inputs, _)) => List.map (fn v => BE_Leaf (NONE, v)) (outputs @ inputs)

        val globalIdentExprList = machineParameterExprList @ aconstantsExprList @ cconstantsExprList @ avariablesExprList @ cvariablesExprList @ operationParameterExprList

        val constraintsOpt = List.find (fn (BC_CONSTRAINTS _) => true | _ => false) clauses
        val propertiesOpt  = List.find (fn (BC_PROPERTIES  _) => true | _ => false) clauses
        val invariantOpt   = List.find (fn (BC_INVARIANT   _) => true | _ => false) clauses
        (* ASSERTIONS は無視 *)

        val staticConditionList = let
                                    val constraintsList = case constraintsOpt of
                                                            SOME (BC_CONSTRAINTS (BP (BE_Commutative (_, Keyword "&", l)))) => l
                                                          | SOME (BC_CONSTRAINTS (BP e                                   )) => [e]
                                                          | NONE                                                            => []
                                                          | _                                                               => raise SortError ""
                                    val propertiesList  = case propertiesOpt  of
                                                            SOME (BC_PROPERTIES  (BP (BE_Commutative (_, Keyword "&", l)))) => l
                                                          | SOME (BC_PROPERTIES  (BP e                                   )) => [e]
                                                          | NONE                                                            => []
                                                          | _                                                               => raise SortError ""
                                    val invariantList   = case invariantOpt   of
                                                            SOME (BC_INVARIANT   (BP (BE_Commutative (_, Keyword "&", l)))) => l
                                                          | SOME (BC_INVARIANT   (BP e                                   )) => [e]
                                                          | NONE                                                            => []
                                                          | _                                                               => raise SortError ""
                                  in
                                    constraintsList @ propertiesList @ invariantList
                                  end

        val operationBody       = case operation of BOp (_, _, _, BS_Precondition (_, s   )) => s      | BOp (_, _, _, s) => s    (* 事前条件を除いた操作の代入文 *)
        val preconditionExprOpt = case operation of BOp (_, _, _, BS_Precondition (BP e, _)) => SOME e | _                => NONE (* 事前条件 option *)

        val _ = List.app (fn (BE_Node2 (_, Keyword ":", e1, BE_Node1 (_, Keyword k, e2))) => if k = "POW" orelse k = "FIN" then addRelation (e1, e2) else ()
                           | (BE_Node2 (_, Keyword k  , e1, e2                         )) => if k = "<=" orelse k = "<" orelse k = "<:" orelse k = "<<:" then addRelation (e1, e2) else ()
                           | _                                                            => ())
                         staticConditionList


        fun getOrder () =
            (
              (case constraintsOpt of
                NONE                         => ()
              | SOME (BC_CONSTRAINTS (BP e)) => getOrderInTopExprTree e
              | _                            => raise SortError "");
              (case propertiesOpt  of
                NONE                         => ()
              | SOME (BC_PROPERTIES  (BP e)) => getOrderInTopExprTree e
              | _                            => raise SortError "");
              (case invariantOpt   of
                NONE                         => ()
              | SOME (BC_INVARIANT   (BP e)) => getOrderInTopExprTree e
              | _                            => raise SortError "");
              getOrderInTopSubstitutionTree operationBody;
              getOrderInExprList globalIdentExprList (* モデル変数等についての順序を求める *)
            )

        fun getOrderCycle () = (* 新しく順序が判明しなくなるまで繰り返す *)
            let
              val initialLength = List.length (!relationPool)
              val _ = getOrder ()
            in
              if
                List.length (!relationPool) = initialLength
              then
                ()
              else
                getOrderCycle ()
            end
        val _ = getOrderCycle ()
        val _ = addRandomRelationInComponent inputModel (* 事前条件以外について順序が定まらなかった箇所の順序をランダムに与える *)
        fun getOrderInPreconditionCycle e =
            let
              val initialLength = List.length (!relationPool)
              val _ = getOrderInTopExprTree e
            in
              if
                List.length (!relationPool) = initialLength
              then
                ()
              else
                getOrderInPreconditionCycle e
            end
        val _ = case preconditionExprOpt of SOME e => getOrderInPreconditionCycle e | NONE => () (* 事前条件に関する順序を求める *)
        val _ = case preconditionExprOpt of SOME e => addRandomRelationInExprTree e | NONE => () (* 事前条件に関して順序が定まらなかった箇所の順序をランダムに与える *)

        val sortedMachineParameters = sortVarList machineParameters
        val sortedClauses = sortClauseList (List.map sortClause clauses)
      in
        AST.mapExprsInComponent (makeTypingsFirst userTypeSetList) (BMch (machineName, sortedMachineParameters, sortedClauses))
      end)
    | sort _ = raise SortError "input component is not abstract machine"

end

