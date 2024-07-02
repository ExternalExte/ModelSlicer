structure ImplicitCondition =
struct
  exception ICondError of string

  fun makeBtrueConditionsFromExpr e =
      let
        fun extractIntegerLiterals (BE_Leaf (_, IntegerLiteral x)) = [x]
          | extractIntegerLiterals e = List.concat (List.map extractIntegerLiterals (AST.subExprTrees e))

        fun extractRealLiterals (BE_Leaf (_, RealLiteral x)) = [x]
          | extractRealLiterals e = List.concat (List.map extractRealLiterals (AST.subExprTrees e))

        fun extractAndMakeSetSubstractionConditions (substraction as BE_Node2 (SOME (BT_Power to), Keyword "-", lhs, _)) = [(BE_Node2 (SOME BT_Predicate, Keyword ":", substraction, BE_Node1 (SOME (BT_Power (SOME (BT_Power to))), Keyword "POW", lhs)))]
          | extractAndMakeSetSubstractionConditions e = List.concat (List.map extractAndMakeSetSubstractionConditions (AST.subExprTrees e))

        val integerList = Utils.deleteDouble Utils.eqto ((0 : IntInf.int) :: (1 : IntInf.int) :: extractIntegerLiterals e) (* 0, 1 は加法・乗法で単位元や零元となる特別な値なので加えておく *)
        val realList    = Utils.deleteDouble Utils.eqto ((BReal.fromString "0.0") :: (BReal.fromString "1.0") :: extractRealLiterals e)

        fun makeIntegerLiteralConditions l =
            let
              val pairList = Utils.deleteDouble Utils.eqto (List.filter (fn (x, y) => x <> y) (List.concat (List.map (fn x => List.map (fn y => (x, y)) l) l)))
            in
              List.map (fn (x, y) => if
                                       x <= y
                                     then
                                       BE_Node2 (SOME BT_Predicate, Keyword "<=", BE_Leaf (SOME BT_Integer, IntegerLiteral x), BE_Leaf (SOME BT_Integer, IntegerLiteral y))
                                     else
                                       BE_Node2 (SOME BT_Predicate, Keyword "<=", BE_Leaf (SOME BT_Integer, IntegerLiteral y), BE_Leaf (SOME BT_Integer, IntegerLiteral x))) pairList
            end
        fun makeRealLiteralConditions l =
            let
              val pairList = Utils.deleteDouble Utils.eqto (List.filter (fn (x, y) => x `<> y) (List.concat (List.map (fn x => List.map (fn y => (x, y)) l) l)))
            in
              List.map (fn (x, y) => if
                                       x `<= y
                                     then
                                       BE_Node2 (SOME BT_Predicate, Keyword "<=", BE_Leaf (SOME BT_Real, RealLiteral x), BE_Leaf (SOME BT_Real, RealLiteral y))
                                     else
                                       BE_Node2 (SOME BT_Predicate, Keyword "<=", BE_Leaf (SOME BT_Real, RealLiteral y), BE_Leaf (SOME BT_Real, RealLiteral x))) pairList

            end
      in
        (makeIntegerLiteralConditions integerList) @ (makeRealLiteralConditions realList) @ (Utils.deleteDouble Utils.eqto (extractAndMakeSetSubstractionConditions e))
      end

  fun extractConstraintsList clauses =
    let
      val cOpt = List.find (fn (BC_CONSTRAINTS _) => true | _ => false) clauses
    in
      (case cOpt of
        NONE => []
      | SOME (BC_CONSTRAINTS (BP (BE_Commutative (_, Keyword "&", l)))) => l
      | SOME (BC_CONSTRAINTS (BP e)) => [e]
      | _ => raise ICondError "")
    end

  fun extractPropertiesList clauses =
    let
      val cOpt = List.find (fn (BC_PROPERTIES _) => true | _ => false) clauses
    in
      (case cOpt of
        NONE => []
      | SOME (BC_PROPERTIES (BP (BE_Commutative (_, Keyword "&", l)))) => l
      | SOME (BC_PROPERTIES (BP e)) => [e]
      | _ => raise ICondError "")
    end

  fun extractInvariantList clauses =
    let
      val cOpt = List.find (fn (BC_INVARIANT _) => true | _ => false) clauses
    in
      (case cOpt of
        NONE => []
      | SOME (BC_INVARIANT (BP (BE_Commutative (_, Keyword "&", l)))) => l
      | SOME (BC_INVARIANT (BP e)) => [e]
      | _ => raise ICondError "")
    end

  fun wrapCondition [] = raise ICondError "empty conditions"
    | wrapCondition [e] = BP e
    | wrapCondition l = BP (Commutative.flattenCommutative (BE_Commutative (SOME BT_Predicate, Keyword "&", l)))

  fun grouping ([] : BExpr list) = [([], [])]
    | grouping (x :: xs) = List.concat (List.map (fn (g1, g2) => [((x :: g1), g2), (g1, (x :: g2))]) (grouping xs))

  fun matchConditionsList [] _ = SOME [[]]
    | matchConditionsList (e :: es) targetList =
      let
        val mp = List.filter (fn (_, NONE) => false | _ => true)
                             (List.map (fn x => (x, Match.matchExpr e x)) targetList)
        val nextMerged = List.concat (List.map (fn (x, SOME l1) => (case (matchConditionsList es (Utils.dropOne (Utils.eqto x) targetList)) of
                                                                      NONE      => []
                                                                    | (SOME l2) => Match.mergeTrsvCandidates l1 l2)
                                                 | _ => raise ICondError "")
                                               mp)
      in
        if
          nextMerged = []
        then
          NONE
        else
          SOME (Utils.deleteDouble (Utils.eqAsSet Utils.eqto) nextMerged)
      end

  fun simplifyCondition e =
      let
        val applyingFunctions =
          [
            AST.mapExprTree Commutative.flattenCommutative,
            (*Simplify.simplifyExprTree,*)
            TypeInference.typeExprTree
          ]
      in
        Utils.repeatApplyEqf (fn x => Utils.pam x applyingFunctions) AST.eqExprs e
      end

  fun simplifyConditionsList [] = []
    | simplifyConditionsList [e] =
      (case simplifyCondition e of
        (BE_Commutative (_, Keyword "&", l)) => l
      | res => [res])
    | simplifyConditionsList l =
      (case simplifyCondition (BE_Commutative (SOME BT_Predicate, Keyword "&", l)) of
        (BE_Commutative (_, Keyword "&", l)) => l
      | res => [res])

  val callCounter = ref 0

  fun tryApplying (pattern1, pattern2) oldConditions newConditions =
      let
        (* 簡易的な条件のリスト化を推論規則について行う。条件の階層の統一（上から順に積、和、否定）を推論規則に対して施すかどうかは未定 *)
        val pattern1List = case pattern1 of (BE_Commutative (_, Keyword "&", l)) => l | _ => [pattern1]
        (* 古い条件の中から探してくるものと新しい条件の中から探してくるものに分けたパターンを全て列挙するが、
        全て古い条件の中から探してくるパターンを除く（必ず1個は新しい条件の中から探す） *)
        val groupingPatterns = List.filter (fn (_, []) => false | _ => true) (grouping pattern1List)
        val candidatesOpt = List.map (fn (oldp, newp) => ((matchConditionsList oldp oldConditions), (matchConditionsList newp newConditions))) groupingPatterns
        val merged = Utils.deleteDouble (Utils.eqAsSet Utils.eqto) (List.concat (List.map (fn (SOME l1, SOME l2) => Match.mergeTrsvCandidates l1 l2 | _ => []) candidatesOpt))
        val res = List.map (fn m => AST.mapExprTree (Match.rewriteVar m) pattern2) merged
        val _ = (simplifyConditionsList (res @ oldConditions @ newConditions)) handle TypeInference.BTypeError _ => raise ICondError ( "type error is occured in applying implicit condition rule :\n" ^
                                                                                                                                       (Stringify.exprToString pattern1) ^ " @->@ " ^ (Stringify.exprToString pattern2) ^ "\n\n" ^
                                                                                                                                       "OLD CONDITIONS:\n"     ^ (Utils.concatWith "\n" (List.map Stringify.exprToString oldConditions)) ^ "\n\n" ^
                                                                                                                                       "NEW CONDITIONS:\n"     ^ (Utils.concatWith "\n" (List.map Stringify.exprToString newConditions)) ^ "\n\n" ^
                                                                                                                                       "DERIVED CONDITIONS:\n" ^ (Utils.concatWith "\n" (List.map Stringify.exprToString res          )) ^ "\n"
                                                                                                                                     )
      in
        Utils.deleteDouble AST.eqExprs res
      end

  fun deriveImplicitConditionsRound [] _ newConditionsList = newConditionsList (* 推論規則が空 *)
    | deriveImplicitConditionsRound _ oldConditionsList [] = List.map TypeInference.typeExprTree oldConditionsList
    | deriveImplicitConditionsRound rules oldConditionsList newConditionsList =
      let
        val derivedConditionsList    = Utils.deleteDouble AST.eqExprs (List.concat (List.map (fn r => tryApplying r oldConditionsList newConditionsList) rules))
        val updatedOldConditionsList = simplifyConditionsList (Utils.deleteDouble AST.eqExprs (oldConditionsList @ newConditionsList))
        val updatedNewConditionsList = simplifyConditionsList (Utils.substractionAsSet AST.eqExprs derivedConditionsList updatedOldConditionsList)
      in
        deriveImplicitConditionsRound rules updatedOldConditionsList updatedNewConditionsList
      end

      (* [推論規則] -> [上位スコープの条件] -> [条件] -> [導出後の条件] *)
  fun deriveImplicitConditionList _  _ [] = [] (* 条件が空 *)
    | deriveImplicitConditionList rules upperConditions conditions =
      let
        val literalConditions = makeBtrueConditionsFromExpr (BE_Commutative (SOME BT_Predicate, Keyword "&", conditions))
        val derived = deriveImplicitConditionsRound rules (Utils.deleteDouble Utils.eqto (literalConditions @ upperConditions)) conditions
      in
        Utils.substractionAsSet AST.eqExprs derived upperConditions (* 上位スコープの条件と同じものは消す *)
      end

      (* [推論規則] -> [上位スコープの条件] -> 操作 -> 事前条件の暗黙の条件を導出後の操作 *)
  fun deriveImplicitConditionsInPrecondition [] _ opr = opr
    | deriveImplicitConditionsInPrecondition rules upperConditions (BOp (oprName, oparams, iparams, BS_Precondition ((BP e), s))) =
      let
        val conditionList = case e of (BE_Commutative (_, Keyword "&", l)) => l | _ => [e]
        val newPrecondition = wrapCondition (deriveImplicitConditionList rules upperConditions conditionList)
      in
        BOp (oprName, oparams, iparams, BS_Precondition (newPrecondition, s))
      end
    | deriveImplicitConditionsInPrecondition _ _ opr = opr

  (* 細分化モデルの条件式を持つ代入文に対して再帰的に暗黙の条件を導出 *)
  fun deriveImplicitConditionsInSubstitution [] _ s = s
    | deriveImplicitConditionsInSubstitution rules upperConditions (BS_Block  s) = deriveImplicitConditionsInSubstitution rules upperConditions s
      (* 字面統一のための暗黙の条件の導出であるため、事前条件に依存しないようにする *)
    | deriveImplicitConditionsInSubstitution rules upperConditions (BS_Precondition (p, s)) = BS_Precondition (p, (deriveImplicitConditionsInSubstitution rules upperConditions s))
    | deriveImplicitConditionsInSubstitution rules upperConditions (BS_Choice l) = BS_Choice (List.map (deriveImplicitConditionsInSubstitution rules upperConditions) l)
    | deriveImplicitConditionsInSubstitution rules upperConditions (BS_If l) =
      let
        fun deriveImplicitConditionInIfBranch exclusiveCondList ((SOME (BP e), s) :: ifBranches) =
            let
              val condList = case e of (BE_Commutative (_, Keyword "&", l)) => l | _ => [e]
              val inversedExclusiveCondList = List.map (fn e => Simplify.simplifyExprTree (BE_Node1 (SOME BT_Predicate, Keyword "not", e))) exclusiveCondList
              val premise = Utils.deleteDouble AST.eqExprs (upperConditions @ inversedExclusiveCondList)
              val newCondList = deriveImplicitConditionList rules premise condList
              val newCond = wrapCondition newCondList
              val newExclusiveCondList = Utils.deleteDouble AST.eqExprs (exclusiveCondList @ newCondList)
              val ns = deriveImplicitConditionsInSubstitution rules premise s
            in
              (SOME newCond, ns) :: (deriveImplicitConditionInIfBranch newExclusiveCondList ifBranches)
            end
          | deriveImplicitConditionInIfBranch exclusiveConditionList [(NONE, s)] =
            let
              val inversedExclusiveCondList = List.map (fn e => Simplify.simplifyExprTree (BE_Node1 (SOME BT_Predicate, Keyword "not", e))) exclusiveConditionList
              val premise = Utils.deleteDouble AST.eqExprs (upperConditions @ inversedExclusiveCondList)
            in
              [(NONE, deriveImplicitConditionsInSubstitution rules premise s)]
            end
          | deriveImplicitConditionInIfBranch _ [] = []
          | deriveImplicitConditionInIfBranch _ _ = raise ICondError "invalid form of IF substitution"
      in
        BS_If (deriveImplicitConditionInIfBranch [] l)
      end
    | deriveImplicitConditionsInSubstitution rules upperConditions (BS_Select l) =
      let
        fun deriveImplicitConditionsInSubstitutionAux (NONE,        s) = (NONE, deriveImplicitConditionsInSubstitution rules upperConditions s)
          | deriveImplicitConditionsInSubstitutionAux (SOME (BP e), s) =
            let
              val conditionList = case e of (BE_Commutative (_, Keyword "&", l)) => l | _ => [e]
              val newConditionList = deriveImplicitConditionList rules upperConditions conditionList
              val newCondition = wrapCondition newConditionList
              val ns = deriveImplicitConditionsInSubstitution rules (Utils. deleteDouble AST.eqExprs (newConditionList @ upperConditions)) s
            in
              (SOME newCondition, ns)
            end
      in
        BS_Select (List.map deriveImplicitConditionsInSubstitutionAux l)
      end
    | deriveImplicitConditionsInSubstitution rules upperConditions (BS_Any (tks, BP e, s)) =
      let
        val conditionList = case e of (BE_Commutative (_, Keyword "&", l)) => l | _ => [e]
        val newConditionList = deriveImplicitConditionList rules upperConditions conditionList
        val newCondition = wrapCondition newConditionList
        val ns = deriveImplicitConditionsInSubstitution rules (Utils.deleteDouble AST.eqExprs (newConditionList @ upperConditions)) s
      in
        BS_Any (tks, newCondition, ns)
      end
    | deriveImplicitConditionsInSubstitution rules upperConditions (BS_Simultaneous l) = BS_Simultaneous (List.map (deriveImplicitConditionsInSubstitution rules upperConditions) l)
    | deriveImplicitConditionsInSubstitution _ _ s = s


    (* コンポーネント全体の制約条件に対して適用 *)
  fun deriveImplicitConditions slicedFlag rules (BMch (name, mparams, clauses)) =
      let
        val constraintsList = extractConstraintsList clauses
        val propertiesList  = extractPropertiesList clauses
        val invariantList   = extractInvariantList clauses
        val oprs            = List.concat (List.map (fn (BC_OPERATIONS l) => l | _ => []) clauses)
        val newConstraintsList = deriveImplicitConditionList rules [] constraintsList
        val newPropertiesList  = deriveImplicitConditionList rules newConstraintsList propertiesList
        val newInvariantList   = deriveImplicitConditionList rules (Utils.deleteDouble AST.eqExprs (newConstraintsList @ newPropertiesList)) invariantList
        val newOprs            = if
                                    slicedFlag
                                 then
                                    (case oprs of
                                       [(BOp (name, oparam, iparam, s))] =>  [(BOp (name, oparam, iparam, deriveImplicitConditionsInSubstitution rules (Utils.deleteDouble AST.eqExprs (newConstraintsList @ newPropertiesList @ newInvariantList)) s))]
                                     | _ => raise ICondError "")
                                 else
                                   List.map (deriveImplicitConditionsInPrecondition rules (Utils.deleteDouble AST.eqExprs (newConstraintsList @ newPropertiesList @ newInvariantList))) oprs
        val newClauses = List.map (fn (BC_CONSTRAINTS _) => (BC_CONSTRAINTS (wrapCondition newConstraintsList))
                                    | (BC_PROPERTIES  _) => (BC_PROPERTIES  (wrapCondition newPropertiesList))
                                    | (BC_INVARIANT   _) => (BC_INVARIANT   (wrapCondition newInvariantList))
                                    | (BC_OPERATIONS  _) => (BC_OPERATIONS  newOprs)
                                    | others             => others)
                                  clauses
      in
        BMch (name, mparams, newClauses)
      end
    | deriveImplicitConditions _ _ _ = raise ICondError "this system is only for machines"


  (* 細分化モデルのIFやANYの条件式に対する暗黙の条件の導出 *)(*
  fun deriveImplicitConditionsInSlicedModel rules (BMch (name, mparams, clauses)) =
      let
        val constraintsList      = extractConstraintsList clauses
        val propertiesList       = extractPropertiesList  clauses
        val invariantList        = extractInvariantList   clauses
        val (BC_OPERATIONS [(BOp (opName, oparams, iparams, s))]) = valOf (List.find (fn (BC_OPERATIONS _) => true | _ => false) clauses)
        val ns = deriveImplicitConditionsInSubstitution rules (Utils.deleteDouble AST.eqExprs (constraintsList @ propertiesList @ invariantList)) s
        val newOperation = BOp (opName, oparams, iparams, ns)
        val newClauses = List.map (fn BC_OPERATIONS _ => BC_OPERATIONS [newOperation] | others => others) clauses
      in
        BMch (name, mparams, newClauses)
      end
    | deriveImplicitConditionsInSlicedModel _ _ = raise ICondError "this system is only for machines"*)

(*************** 以下、=関係による条件式の書き換え用関数 ***************)

  fun rewriteAllEqualExpr (expr1, expr2) target =
      if
        AST.eqExprs expr1 target
      then
        expr2
      else
        target

  fun rewriteAllEqualExprInConditionList (e1, e2) (targets : BExpr list) =
      let
        val alle1 = List.map (AST.mapExprTree (rewriteAllEqualExpr (e1, e2))) targets
        val alle2 = List.map (AST.mapExprTree (rewriteAllEqualExpr (e2, e1))) targets
      in
        Utils.deleteDouble AST.eqExprs (alle1 @ alle2)
      end

  (* 整数と集合において a <= b と a : POW (b) がプリミティブで、a < b, b > a, b >= a, a <: b, a <<: b, a /<: b, a /<<: b, a = b, a /= b が非プリミティブである前提 *)
  fun findEquivalences [] = []
    | findEquivalences ((BE_Node2 (_, Keyword "<=", e1, e2)) :: rest) =
      (case TypeInference.typeOf e1 of
        (SOME BT_Integer) => (if
                                List.exists (fn (BE_Node2 (_, Keyword "<=", lhs, rhs)) => AST.eqExprs e1 rhs andalso AST.eqExprs e2 lhs | _ => false) rest
                              then
                                (e1, e2) :: findEquivalences rest
                              else
                                findEquivalences rest)
      | _                 => findEquivalences rest)
    | findEquivalences ((BE_Node2 (_, Keyword ":", e1, BE_Node1 (_, Keyword "POW", e2))) :: rest) =
        if
          List.exists (fn (BE_Node2 (_, Keyword ":", lhs, BE_Node1 (_, Keyword "POW", rhs))) => AST.eqExprs e1 rhs andalso AST.eqExprs e2 lhs | _ => false) rest
        then
          (e1, e2) :: findEquivalences rest
        else
          findEquivalences rest
    | findEquivalences ((BE_Node2 (_, Keyword "=", e1, e2)) :: rest) = (e1, e2) :: findEquivalences rest (* REAL等 *)
    | findEquivalences (p :: rest) = findEquivalences rest

  fun equivalencesToConditions [] = []
    | equivalencesToConditions ((e1, e2) :: rest) =
      (case TypeInference.typeOf e1 of
        (SOME BT_Integer   ) => [(BE_Node2 (SOME BT_Predicate, Keyword "<=", e1, e2)),
                                 (BE_Node2 (SOME BT_Predicate, Keyword "<=", e2, e1))]
                                @ (equivalencesToConditions rest)
      | (SOME (BT_Power to)) => [(BE_Node2 (SOME BT_Predicate, Keyword ":", e1, BE_Node1 (SOME (BT_Power (SOME (BT_Power to))), Keyword "POW", e2))),
                                 (BE_Node2 (SOME BT_Predicate, Keyword ":", e2, BE_Node1 (SOME (BT_Power (SOME (BT_Power to))), Keyword "POW", e1)))]
                                @ (equivalencesToConditions rest)
      | to                   => (BE_Node2 (SOME BT_Predicate, Keyword "=", e1, e2)) :: equivalencesToConditions rest)

  fun rewriteEqualExprInStaticConditionList (upperConditions : BExpr list) (targetConditions : BExpr list) =
      let
        val equalPairs      = findEquivalences targetConditions
        val upperEqualPairs = findEquivalences upperConditions
        fun deleteReversed [] = []
          | deleteReversed ((e1, e2) :: xs) =
            if
              List.exists (fn (x1, x2) => ((AST.eqExprs x1 e1) andalso (AST.eqExprs x2 e2)) orelse ((AST.eqExprs x1 e1) andalso (AST.eqExprs x2 e2))) xs (* 同順も逆順も重複は削除 *)
            then
              deleteReversed xs
            else
              (e1, e2) :: (deleteReversed xs)
        val allEqualPairs = deleteReversed (upperEqualPairs @ equalPairs)
        val resultList = (List.foldl (fn (x, l) => rewriteAllEqualExprInConditionList x l) targetConditions allEqualPairs)
        val equalExprs = equivalencesToConditions equalPairs
      in
        Utils.deleteDouble AST.eqExprs (List.map (AST.mapExprTree rewriteEqualExprInExpr) (resultList @ equalExprs))
      end
  and
      rewriteEqualExprInExpr (BE_Commutative (_, Keyword "&", l)) =
      (case rewriteEqualExprInStaticConditionList [] l of
        []  => raise ICondError "empty conditions"
      | [e] => e
      | es  => BE_Commutative (SOME BT_Predicate, Keyword "&", es))
    | rewriteEqualExprInExpr e = e
  and
      rewriteEqualExprInExprWithUpperCondition upperConditions (BE_Commutative (_, Keyword "&", l)) =
      (case Utils.substractionAsSet AST.eqExprs (rewriteEqualExprInStaticConditionList upperConditions l) upperConditions of
        []  => BE_Leaf (SOME BT_Predicate, Keyword "btrue")
      | [e] => e
      | es  => BE_Commutative (SOME BT_Predicate, Keyword "&", es))
    | rewriteEqualExprInExprWithUpperCondition upperConditions e = rewriteEqualExprInExprWithUpperCondition upperConditions (BE_Commutative (SOME BT_Predicate, Keyword "&", [e]))

  fun rewriteEqualExprInPredicateWithUpperCondition uc (BP e) = BP (rewriteEqualExprInExprWithUpperCondition uc e)

  fun rewriteImplicitConditionsInOperation false upperConditions (BOp (oprName, outputs, inputs, BS_Precondition (p, s))) = BOp (oprName, outputs, inputs, BS_Precondition (rewriteEqualExprInPredicateWithUpperCondition upperConditions p, s))
    | rewriteImplicitConditionsInOperation _     upperConditions (BOp (oprName, outputs, inputs, s)) = BOp (oprName, outputs, inputs, AST.mapPredicatesInSubstitutionTree (rewriteEqualExprInPredicateWithUpperCondition upperConditions) s)

    (* slicedFlagがtrue => 全体に適用、false => 操作内の条件には適用せず *)
  fun rewriteEqualExprs slicedFlag (BMch (name, mparams, clauses)) =
      let
        val constraintsList = extractConstraintsList clauses
        val propertiesList  = extractPropertiesList clauses
        val invariantList   = extractInvariantList clauses
        val newConstraintsList = rewriteEqualExprInStaticConditionList [] constraintsList
        val newPropertiesList  = rewriteEqualExprInStaticConditionList newConstraintsList propertiesList
        val newInvariantList   = rewriteEqualExprInStaticConditionList (Utils.deleteDouble AST.eqExprs (newConstraintsList @ newPropertiesList)) invariantList
        val  oprs = List.concat (List.map (fn (BC_OPERATIONS l) => l | _ => []) clauses)
        val newOprs = List.map (rewriteImplicitConditionsInOperation slicedFlag (Utils.deleteDouble AST.eqExprs (newConstraintsList @ newPropertiesList @ newInvariantList))) oprs
        val newClauses = List.map (fn (BC_CONSTRAINTS _) => (BC_CONSTRAINTS (wrapCondition newConstraintsList))
                                        | (BC_PROPERTIES  _) => (BC_PROPERTIES  (wrapCondition newPropertiesList))
                                        | (BC_INVARIANT   _) => (BC_INVARIANT   (wrapCondition newInvariantList))
                                        | (BC_OPERATIONS  _) => (BC_OPERATIONS  newOprs)
                                        | others             => others)
                                      clauses
      in
        BMch (name, mparams, newClauses)
      end
    | rewriteEqualExprs _ _ = raise ICondError "this system is only for machines"
end

(* TODO upperConditionのみからの書き換え *)
