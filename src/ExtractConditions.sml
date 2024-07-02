structure ExtractConditions =
struct
  exception ExtractConditionsError of string

  fun extractTypeName NONE                          = []
    | extractTypeName (SOME BT_Real)                = []
    | extractTypeName (SOME BT_Integer)             = []
    | extractTypeName (SOME BT_String)              = []
    | extractTypeName (SOME BT_Float)               = []
    | extractTypeName (SOME BT_Bool)                = []
    | extractTypeName (SOME (BT_Power to))          = extractTypeName to
    | extractTypeName (SOME (BT_Pair (to1, to2)))   = (extractTypeName to1) @ (extractTypeName to2)
    | extractTypeName (SOME (BT_Deferred str))      = [(Var str)]
    | extractTypeName (SOME (BT_Enum (str, elems))) = (Var str) :: (List.map (fn s => Var s) elems)
    | extractTypeName (SOME BT_Predicate)           = []
    | extractTypeName _                             = [] (* BT_Structは未実装 *)

  (* 式内で使われている識別子を返す (式内で使用されている型も含む) *)
  fun extractIdsInExpr (BE_Leaf (to, Var vn))            = (Var vn) :: (extractTypeName to)
    | extractIdsInExpr (BE_Leaf (to, _))                 =  extractTypeName to
    | extractIdsInExpr (BE_Node1 (to, opName, e))        = (extractTypeName to) @ (extractIdsInExpr e)
    | extractIdsInExpr (BE_Node2 (to, opName, e1, e2))   = (extractTypeName to) @ (extractIdsInExpr e1) @ (extractIdsInExpr e2)
    | extractIdsInExpr (BE_NodeN (to, opName, el))       = (extractTypeName to) @ (List.concat (List.map extractIdsInExpr el))
    | extractIdsInExpr (BE_Fnc (to, e1, e2))             = (extractTypeName to) @ (extractIdsInExpr e1) @ (extractIdsInExpr e2)
    | extractIdsInExpr (BE_Img (to, e1, e2))             = (extractTypeName to) @ (extractIdsInExpr e1) @ (extractIdsInExpr e2)
    | extractIdsInExpr (BE_Bool (BP e))                  = extractIdsInExpr e
    | extractIdsInExpr (BE_ExSet (to, el))               = (extractTypeName to) @ (List.concat (List.map extractIdsInExpr el))
    | extractIdsInExpr (BE_InSet (to, lvs, BP e))        = Utils.substractionAsSet Utils.eqto ((extractTypeName to) @ (extractIdsInExpr e)) lvs
    | extractIdsInExpr (BE_Seq (to, el))                 = (extractTypeName to) @ (List.concat (List.map extractIdsInExpr el))
    | extractIdsInExpr (BE_ForAll (lvs, BP e1, BP e2))   = Utils.substractionAsSet Utils.eqto ((extractIdsInExpr e1) @ (extractIdsInExpr e2)) lvs
    | extractIdsInExpr (BE_Exists (lvs, BP e))           = Utils.substractionAsSet Utils.eqto (extractIdsInExpr e) lvs
    | extractIdsInExpr (BE_Lambda (to, lvs, BP e1, e2))  = Utils.substractionAsSet Utils.eqto ((extractTypeName to) @ (extractIdsInExpr e1) @ (extractIdsInExpr e2)) lvs
    | extractIdsInExpr (BE_Sigma (to, lv, BP e1, e2))    = Utils.substractionAsSet Utils.eqto ((extractTypeName to) @ (extractIdsInExpr e1) @ (extractIdsInExpr e2)) [lv]
    | extractIdsInExpr (BE_Pi (to, lv, BP e1, e2))       = Utils.substractionAsSet Utils.eqto ((extractTypeName to) @ (extractIdsInExpr e1) @ (extractIdsInExpr e2)) [lv]
    | extractIdsInExpr (BE_Inter (to, lvs, BP e1, e2))   = Utils.substractionAsSet Utils.eqto ((extractTypeName to) @ (extractIdsInExpr e1) @ (extractIdsInExpr e2)) lvs
    | extractIdsInExpr (BE_Union (to, lvs, BP e1, e2))   = Utils.substractionAsSet Utils.eqto ((extractTypeName to) @ (extractIdsInExpr e1) @ (extractIdsInExpr e2)) lvs
    | extractIdsInExpr (BE_Commutative (to, opName, el)) = (extractTypeName to) @ (List.concat (List.map extractIdsInExpr el))
    | extractIdsInExpr _                                 = raise ExtractConditionsError "records are not available on this version" (* レコード未実装 *)

  fun extractIdsInSubstitution (BS_Block s)                     = extractIdsInSubstitution s
    | extractIdsInSubstitution BS_Identity                      = []
    | extractIdsInSubstitution (BS_Precondition (BP e, s))      = Utils.deleteDouble Utils.eqto ((extractIdsInSubstitution s) @ (extractIdsInExpr e))
    | extractIdsInSubstitution (BS_Assertion (BP e, s))         = Utils.deleteDouble Utils.eqto ((extractIdsInExpr e) @ extractIdsInSubstitution s) 
    | extractIdsInSubstitution (BS_Choice sl)                   = Utils.deleteDouble Utils.eqto (List.concat (List.map extractIdsInSubstitution sl))
    | extractIdsInSubstitution (BS_If l)                        = Utils.deleteDouble Utils.eqto (List.concat (List.map (fn (NONE, s) => extractIdsInSubstitution s | (SOME (BP e), s) => (extractIdsInExpr e) @ (extractIdsInSubstitution s)) l))
    | extractIdsInSubstitution (BS_Select l)                    = Utils.deleteDouble Utils.eqto (List.concat (List.map (fn (NONE, s) => extractIdsInSubstitution s | (SOME (BP e), s) => (extractIdsInExpr e) @ (extractIdsInSubstitution s)) l))
    | extractIdsInSubstitution (BS_Case (e, l))                 = Utils.deleteDouble Utils.eqto ((extractIdsInExpr e) @ (List.concat (List.map (fn (el, s) => (List.concat (List.map extractIdsInExpr el)) @ (extractIdsInSubstitution s)) l)))
    | extractIdsInSubstitution (BS_Any (vl, BP e, s))           = Utils.deleteDouble Utils.eqto ((extractIdsInExpr e) @ (extractIdsInSubstitution s))
    | extractIdsInSubstitution (BS_Let (l, s))                  = raise ExtractConditionsError "beta reduction is not completed"
    | extractIdsInSubstitution (BS_BecomesElt (el, re))         = Utils.deleteDouble Utils.eqto ((List.concat (List.map extractIdsInExpr el)) @ (extractIdsInExpr re))
    | extractIdsInSubstitution (BS_BecomesSuchThat (el, BP e1)) = Utils.deleteDouble Utils.eqto ((List.concat (List.map extractIdsInExpr el)) @ (extractIdsInExpr e1))
    | extractIdsInSubstitution (BS_Call (_, el1, el2))          = Utils.deleteDouble Utils.eqto ((List.concat (List.map extractIdsInExpr el1)) @ (List.concat (List.map extractIdsInExpr el2)))
    | extractIdsInSubstitution (BS_BecomesEqual (e1, e2))       = Utils.deleteDouble Utils.eqto ((extractIdsInExpr e1) @ (extractIdsInExpr e2))
    | extractIdsInSubstitution (BS_BecomesEqualList (el1, el2)) = Utils.deleteDouble Utils.eqto ((List.concat (List.map extractIdsInExpr el1)) @ (List.concat (List.map extractIdsInExpr el2)))
    | extractIdsInSubstitution (BS_Simultaneous sl)             = Utils.deleteDouble Utils.eqto (List.concat (List.map extractIdsInSubstitution sl))
    | extractIdsInSubstitution (BS_LocalVariable (_, s))        = extractIdsInSubstitution s
    | extractIdsInSubstitution (BS_Sequencing sl)               = Utils.deleteDouble Utils.eqto (List.concat (List.map extractIdsInSubstitution sl))
    | extractIdsInSubstitution (BS_While (BP e1, s, BP e2, e3)) = Utils.deleteDouble Utils.eqto ((extractIdsInSubstitution s) @ (extractIdsInExpr e1) @ (extractIdsInExpr e2) @ (extractIdsInExpr e3))
      
  fun exprToConditionList (BE_Commutative (_, Keyword "&", l)) = l
    | exprToConditionList (BE_Leaf (_, Keyword "btrue")) = []
    | exprToConditionList e = [e]

  fun deleteUnnecessaryConditions constantList necessaryVarList conditionList =
      let
        fun deleteUnnecessaryConditionsAux cond =
            let
              val usedVars = extractIdsInExpr cond
            in
              Utils.intersectionAsSet Utils.eqto usedVars necessaryVarList <> [] andalso         (* 必要な変数が条件内にある *) 
              Utils.substractionAsSet Utils.eqto usedVars (constantList @ necessaryVarList) = [] (* 定数と必要な変数以外のユーザ定義識別子が存在しない *)
            end
      in
        List.filter deleteUnnecessaryConditionsAux conditionList
      end
      
  (* 不要な変数宣言や事前条件を削除 (ANYをどうするかは考え中) *)
  fun deleteUnusedVars constantList (BS_Precondition (BP p, s))  =
      let
        val preconditionList = exprToConditionList p
        val usedVars = extractIdsInSubstitution s
        val newPreconditionList = deleteUnnecessaryConditions constantList usedVars preconditionList
      in
        case newPreconditionList of
          []  => BS_Block s
        | [e] => BS_Precondition (BP e, s)
        | l   => BS_Precondition (BP (BE_Commutative (SOME BT_Predicate, Keyword "&", l)), s)
      end
    | deleteUnusedVars _ (BS_LocalVariable (declaredVars, s)) =
      let
        val usedVars = extractIdsInSubstitution s
        val newDeclaredVars = Utils.intersectionAsSet Utils.eqto declaredVars usedVars
      in
        if
          newDeclaredVars = []
        then
          BS_Block s
        else
          BS_LocalVariable (newDeclaredVars, s)
      end
    | deleteUnusedVars _ s = s

  (* EXTENDS, USES, PROMOTES は対象外とする *)
  (* SEES は展開 or 削除されている前提 *)
  (* extract [参照しているモデル] 操作分割済みのモデル(元のモデルの全ての制約条件を含む) 詳細化前の変数 元の操作で更新されている変数 *)
  fun extract referenceModels component refinedVars changedInOriginalOperation =
      let
(* ↓データの取り出し *)
          
        val (name, refiningMachineNameOpt, params, clauses) = case component of
                                                             BMch (n,    p, c) => (n, NONE  , p, c)
                                                           | BRef (n, r, p, c) => (n, SOME r, p, c)
                                                           | BImp (n, r, p, c) => (n, SOME r, p, c)

        val BC_OPERATIONS [(BOp (oprName, outputParams, inputParams, substitution))] = valOf (List.find (fn (BC_OPERATIONS _) => true | _ => false) clauses)
        val constraintsList = case List.find (fn (BC_CONSTRAINTS _) => true | _ => false) clauses of
                                NONE                         => []
                              | SOME (BC_CONSTRAINTS (BP e)) => exprToConditionList e
                              | _                            => raise ExtractConditionsError ""
        val propertiesList  = case List.find (fn (BC_PROPERTIES  _) => true | _ => false) clauses of
                                NONE                         => []
                              | SOME (BC_PROPERTIES  (BP e)) => exprToConditionList e
                              | _                            => raise ExtractConditionsError ""
        val invariantList   = case List.find (fn (BC_INVARIANT   _) => true | _ => false) clauses of
                                NONE                         => []
                              | SOME (BC_INVARIANT   (BP e)) => exprToConditionList e
                              | _                            => raise ExtractConditionsError ""
        val includesList = case List.find (fn (BC_INCLUDES _) => true | _ => false) clauses of
                             NONE                 => []
                           | SOME (BC_INCLUDES l) => l
                           | _                    => raise ExtractConditionsError ""
        val importsList  = case List.find (fn (BC_IMPORTS  _) => true | _ => false) clauses of
                             NONE                 => []
                           | SOME (BC_IMPORTS  l) => l
                           | _                    => raise ExtractConditionsError ""
        val setsList       = case List.find (fn (BC_SETS       _) => true | _ => false) clauses of
                               NONE                   => []
                             | SOME (BC_SETS       l) => l
                             | _                      => raise ExtractConditionsError ""
        val aconstantsList = case List.find (fn (BC_ACONSTANTS _) => true | _ => false) clauses of
                               NONE                   => []
                             | SOME (BC_ACONSTANTS l) => l
                             | _                      => raise ExtractConditionsError ""
        val cconstantsList = case List.find (fn (BC_CCONSTANTS _) => true | _ => false) clauses of
                               NONE                   => []
                             | SOME (BC_CCONSTANTS l) => l
                             | _                      => raise ExtractConditionsError ""
        val avariablesList = case List.find (fn (BC_AVARIABLES _) => true | _ => false) clauses of
                               NONE                   => []
                             | SOME (BC_AVARIABLES l) => l
                             | _                      => raise ExtractConditionsError ""
        val cvariablesList = case List.find (fn (BC_CVARIABLES _) => true | _ => false) clauses of
                               NONE                   => []
                             | SOME (BC_CVARIABLES l) => l
                             | _                      => raise ExtractConditionsError ""
        val valuesList = case List.find (fn (BC_VALUES _) => true | _ => false) clauses of
                           NONE               => []
                         | SOME (BC_VALUES l) => l
                         | _                  => raise ExtractConditionsError ""

        val setsIdList = List.concat (List.map (fn (BT_Deferred x) => [Var x] | (BT_Enum (x, elms)) => (Var x) :: (List.map (fn y => Var y) elms) |  _ => raise ExtractConditionsError "") setsList)

(* ↑データの取り出し *)
(* ↓参照節以外の更新 *)

        val isImplementation = case component of (BImp _) => true | _ => false (* 以降実装か否かで処理を変える *)

        val allConstants = cconstantsList @ aconstantsList @ setsIdList @ params

        val newSubstitution = AST.mapSubstitutionTree (deleteUnusedVars allConstants) substitution

        val usedIdsInNewSubstitution = (extractIdsInSubstitution newSubstitution) @ refinedVars
        
        val newOutputParams   = Utils.intersectionAsSet Utils.eqto outputParams   usedIdsInNewSubstitution
        val newInputParams    = Utils.intersectionAsSet Utils.eqto inputParams    usedIdsInNewSubstitution
        
        val newAVariablesList = Utils.intersectionAsSet Utils.eqto avariablesList usedIdsInNewSubstitution
        val newCVariablesList = Utils.intersectionAsSet Utils.eqto cvariablesList usedIdsInNewSubstitution

        val newInvariantList = if
                                 isImplementation
                               then
                                 (* 入力が実装だった場合、分割後の代入文で使われている変数が使われており他の変数が使われていない不変条件を抽出 *)
                                 deleteUnnecessaryConditions allConstants usedIdsInNewSubstitution invariantList
                               else
                                 let
                                   (* 中村先輩の博士論文 p53 と同様の命名 *)
                                   (* リファインメントも同様 *)
                                   val varsVprime = usedIdsInNewSubstitution (* vars(V') *)
                                   val x = #1(AST.extractVars newSubstitution) (* X *)
                                   val xprime = Utils.substractionAsSet Utils.eqto changedInOriginalOperation x (* X' *)
                                   val chs1 = deleteUnnecessaryConditions allConstants (Utils.substractionAsSet Utils.eqto varsVprime x) invariantList (* chs(I, vars(V') - X) *)
                                   val chs2 = deleteUnnecessaryConditions allConstants (Utils.substractionAsSet Utils.eqto varsVprime xprime) invariantList (* chs(I, vars(V') - X') *)
                                 in
                                   Utils.deleteDouble Utils.eqto (chs1 @ chs2)
                                 end

        val usedIdsInNewInvariant = Utils.deleteDouble Utils.eqto (List.concat (List.map extractIdsInExpr newInvariantList))
        val usedIdsInNewInvariantAndSubstitution = Utils.deleteDouble Utils.eqto (usedIdsInNewSubstitution @ usedIdsInNewInvariant)
        
        val newAConstantsList = Utils.intersectionAsSet Utils.eqto aconstantsList usedIdsInNewInvariantAndSubstitution
        val newCConstantsList = Utils.intersectionAsSet Utils.eqto cconstantsList usedIdsInNewInvariantAndSubstitution
        
        val newPropertiesList = deleteUnnecessaryConditions (setsIdList @ params) (newAConstantsList @ newCConstantsList) propertiesList

        val usedIdsInNewProperties = Utils.deleteDouble Utils.eqto (List.concat (List.map extractIdsInExpr newPropertiesList))
        val usedVarsConstsAndSets = Utils.deleteDouble Utils.eqto (usedIdsInNewInvariantAndSubstitution @ usedIdsInNewProperties)

        val newSetsList = List.filter (fn (BT_Deferred x        ) => Utils.isIn (Var x) usedVarsConstsAndSets
                                        | (BT_Enum     (x, elms)) => Utils.isIn (Var x) usedVarsConstsAndSets orelse
                                                                     Utils.intersectionAsSet Utils.eqto (List.map (fn y => Var y) elms) usedVarsConstsAndSets <> []
                                        | _                       => raise ExtractConditionsError "") setsList
        val newSetsIdList = List.concat (List.map (fn (BT_Deferred x) => [Var x] | (BT_Enum (x, elms)) => (Var x) :: (List.map (fn y => Var y) elms) |  _ => raise ExtractConditionsError "") newSetsList)
        
        val allUsedIds = Utils.deleteDouble Utils.eqto (newSetsIdList @ usedVarsConstsAndSets)

         (* 暫定的なものなので左辺がこのコンポーネント(実装)で使われているかどうかで判断し、再帰的に抽出しない。また、IMPORTしたモデル内の定数(変数も？)が右辺に使われている場合を想定しない *)
        val newValuesList = List.filter (fn (v, _) => Utils.isIn v allUsedIds) valuesList
        
        val newParams = Utils.intersectionAsSet Utils.eqto params allUsedIds
        
        val newConstraintsList = deleteUnnecessaryConditions [] newParams constraintsList


(* ↑参照節以外の更新 *)
(* ↓参照節のリスト作成 *)
        val calledOperations = List.map (fn (BS_Call (opid, _, _)) => opid | _ => raise ExtractConditionsError "") (AST.findSubstitutions (fn (BS_Call _) => true | _ => false) substitution)

        fun operationExists (BMch (_, _, cs)) (Var opid) =
            let
              val opsOpt = List.find (fn (BC_OPERATIONS _) => true | _ => false) cs
            in
              case opsOpt of
                NONE => false
              | SOME (BC_OPERATIONS opl) => List.exists (fn (BOp (opname, _, _, _)) => opname = opid) opl
              | _                        => raise ExtractConditionsError ""
            end
          | operationExists _                 _    = false (* モデル以外はここで無視 *)
          
        val usedModelNameList = List.map (fn (BMch (mn, _, _)) => mn | _ => raise ExtractConditionsError "") (List.filter (fn m => List.exists (operationExists m) calledOperations) referenceModels)
        
        val newIncludesList = List.filter (fn (BMchInst (Var mName, _)) => Utils.isIn mName usedModelNameList | _ => raise ExtractConditionsError "Renamed or invalid machine name in INCLUDES") includesList
        
        val newImportsList  = List.filter (fn (BMchInst (Var mName, _)) => Utils.isIn mName usedModelNameList | _ => raise ExtractConditionsError "Renamed or invalid machine name in IMPORTS" ) importsList
        
(* ↑参照節のリスト作成 *)
(* ↓節の構成 *)
        val newConstraints = case newConstraintsList of
                               []  => []
                             | [e] => [(BC_CONSTRAINTS (BP e))]
                             | l   => [(BC_CONSTRAINTS (BP (BE_Commutative (SOME BT_Predicate, Keyword "&", l))))]
        val newProperties  = case Utils.substractionAsSet AST.eqExprs newPropertiesList newConstraintsList of
                               []  => []
                             | [e] => [(BC_PROPERTIES  (BP e))]
                             | l   => [(BC_PROPERTIES  (BP (BE_Commutative (SOME BT_Predicate, Keyword "&", l))))]
        val newInvariant   = case Utils.substractionAsSet AST.eqExprs newInvariantList (newConstraintsList @ newPropertiesList) of
                               []  => []
                             | [e] => [(BC_INVARIANT   (BP e))]
                             | l   => [(BC_INVARIANT   (BP (BE_Commutative (SOME BT_Predicate, Keyword "&", l))))]
        val newOperations = [(BC_OPERATIONS [(BOp (oprName, newOutputParams, newInputParams, newSubstitution))])]
                             
        val newAVariables = case newAVariablesList of [] => [] | l => [(BC_AVARIABLES l)]
        val newCVariables = case newCVariablesList of [] => [] | l => [(BC_CVARIABLES l)]
        val newAConstants = case newAConstantsList of [] => [] | l => [(BC_ACONSTANTS l)]
        val newCConstants = case newCConstantsList of [] => [] | l => [(BC_CCONSTANTS l)]

        val newSets = case newSetsList of [] => [] | l => [(BC_SETS l)]
        val newValues = case newValuesList of [] => [] | l => [(BC_VALUES l)]
        
        val newIncludes = case newIncludesList of [] => [] | l => [(BC_INCLUDES l)]
        val newImports  = case newImportsList  of [] => [] | l => [(BC_IMPORTS  l)]

        val newClauses = newConstraints @
                         newValues @
                         newSets @
                         newIncludes @
                         newImports @
                         newAConstants @
                         newCConstants @
                         newProperties @
                         newAVariables @
                         newCVariables @
                         newInvariant @
                         newOperations
      in
        case component of
          BMch _ => BMch (name, newParams, newClauses)
        | BRef _ => BRef (name, valOf refiningMachineNameOpt, newParams, newClauses)
        | BImp _ => BImp (name, valOf refiningMachineNameOpt, newParams, newClauses)
      end
end
