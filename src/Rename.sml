structure Rename =
struct
  exception RenameError of string

  (* 局所変数宣言から識別子置換履歴を取得 (途中からナンバリング可能) *)
  fun renameLocalVarsInTokens prefix count tks =
      let
        val idStrList = List.map (fn (Var idStr) => idStr | _ => raise RenameError "invalid variable declaration") tks
        val len = List.length tks
        val numberList = Utils.range count (count + len - 1)
        val newIdStrList = List.map (fn n => prefix ^ (Utils.intToFixedString 3 n)) numberList
        val newTks = List.map (fn x => Var x) newIdStrList
      in
        (newTks, ListPair.zip (idStrList, newIdStrList), count + len)
      end

  (* 置換履歴と識別子の文字列を受け取り、置換結果の文字列を返す *)
  fun renameIdStr (history : (string * string) list) x =
      (case List.find (fn (b, _) => b = x) history of
        NONE => x
      | SOME (_, a) => a)

  (* 式のリストから識別子置換履歴を取得 (途中からナンバリング可能) *)
  fun renameLocalVarsInExprList _ _      count []        = ([], [], count)
    | renameLocalVarsInExprList history  prefix count (e :: es) =
      let
        val (newe, eHistory, eCount) = renameLocalVarsInExpr history prefix count e
        val (newes, esHistory, esCount) = renameLocalVarsInExprList history prefix eCount es
      in
        (newe :: newes, eHistory @ esHistory, esCount)
      end

  (* 式から識別子置換履歴を取得 *)
  (* 途中からナンバリング可能 (pre-order) *)
  and renameLocalVarsInExpr history prefix count (BE_Leaf  (to, Var x))          = (BE_Leaf (to, Var (renameIdStr history x)), [] : ((string * string) list), count)
    | renameLocalVarsInExpr history prefix count (BE_Node1 (to, tk, e))          =
      let
        val (newe, eHistory, eCount) = renameLocalVarsInExpr history prefix count e
      in
        (BE_Node1 (to, tk, newe), eHistory, eCount)
      end
    | renameLocalVarsInExpr history prefix count (BE_Node2 (to, tk, e1, e2))     =
      let
        val ([newe1, newe2], eHistory, eCount) = renameLocalVarsInExprList history prefix count [e1, e2]
      in
        (BE_Node2 (to, tk, newe1, newe2), eHistory, eCount)
      end
    | renameLocalVarsInExpr history prefix count (BE_NodeN (to, tk, el))         =
      let
        val (newel, elHistory, elCount) = renameLocalVarsInExprList history prefix count el
      in
        (BE_NodeN (to, tk, newel), elHistory, elCount)
      end
    | renameLocalVarsInExpr history prefix count (BE_Fnc (to, e1, e2))           =
      let
        val ([newe1, newe2], eHistory, eCount) = renameLocalVarsInExprList history prefix count [e1, e2]
      in
        (BE_Fnc (to, newe1, newe2), eHistory, eCount)
      end
    | renameLocalVarsInExpr history prefix count (BE_Img (to, e1, e2))           =
      let
        val ([newe1, newe2], eHistory, eCount) = renameLocalVarsInExprList history prefix count [e1, e2]
      in
        (BE_Img (to, newe1, newe2), eHistory, eCount)
      end
    | renameLocalVarsInExpr history prefix count (BE_Bool (BP e))                =
      let
        val (newe, eHistory, eCount) = renameLocalVarsInExpr history prefix count e
      in
        (BE_Bool (BP newe), eHistory, eCount)
      end
    | renameLocalVarsInExpr history prefix count (BE_ExSet (to, el))              =
      let
        val (newel, elHistory, elCount) = renameLocalVarsInExprList history prefix count el
      in
        (BE_ExSet (to, newel), elHistory, elCount)
      end
    | renameLocalVarsInExpr history prefix count (BE_InSet (to, tks, BP e))       =
      let
        val (newTks, tksHistory, tksCount) = renameLocalVarsInTokens prefix count tks
        val (newe, eHistory, eCount)   = renameLocalVarsInExpr (history @ tksHistory) prefix tksCount e
      in
        (BE_InSet (to, newTks, BP newe), tksHistory @ eHistory, eCount)
      end
    | renameLocalVarsInExpr history prefix count (BE_Seq (to, el))                =
      let
        val (newel, elHistory, elCount) = renameLocalVarsInExprList history prefix count el
      in
        (BE_Seq (to, newel), elHistory, elCount)
      end
    | renameLocalVarsInExpr history prefix count (BE_ForAll (tks, BP e1, BP e2)) =
      let
        val (newTks, tksHistory, tksCount) = renameLocalVarsInTokens   prefix count    tks
        val ([newe1, newe2], eHistory,   eCount)   = renameLocalVarsInExprList (history @ tksHistory) prefix tksCount [e1, e2]
      in
        (BE_ForAll (newTks, BP newe1, BP newe2), tksHistory @ eHistory, eCount)
      end
    | renameLocalVarsInExpr history prefix count (BE_Exists (tks, BP e))         =
      let
        val (newTks, tksHistory, tksCount) = renameLocalVarsInTokens prefix count tks
        val (newe, eHistory, eCount)   = renameLocalVarsInExpr (history @ tksHistory) prefix tksCount e
      in
        (BE_Exists (newTks, BP newe), tksHistory @ eHistory, eCount)
      end
    | renameLocalVarsInExpr history prefix count (BE_Lambda (to, tks, BP e1, e2)) =
      let
        val (newTks, tksHistory, tksCount) = renameLocalVarsInTokens prefix count tks
        val ([newe1, newe2], eHistory, eCount)   = renameLocalVarsInExprList (history @ tksHistory) prefix tksCount [e1, e2]
      in
        (BE_Lambda (to, newTks, BP newe1, newe2), tksHistory @ eHistory, eCount)
      end
    | renameLocalVarsInExpr history prefix count (BE_Sigma (to, tk, BP e1, e2))   =
      let
        val ([newTk], tksHistory, tksCount) = renameLocalVarsInTokens prefix count [tk]
        val ([newe1, newe2], eHistory, eCount)   = renameLocalVarsInExprList (history @ tksHistory) prefix tksCount [e1, e2]
      in
        (BE_Sigma (to, newTk, BP newe1, newe2), tksHistory @ eHistory, eCount)
      end
    | renameLocalVarsInExpr history prefix count (BE_Pi (to, tk, BP e1, e2))      =
      let
        val ([newTk], tksHistory, tksCount) = renameLocalVarsInTokens prefix count [tk]
        val ([newe1, newe2], eHistory, eCount)   = renameLocalVarsInExprList (history @ tksHistory) prefix tksCount [e1, e2]
      in
        (BE_Pi (to, newTk, BP newe1, newe2), tksHistory @ eHistory, eCount)
      end
    | renameLocalVarsInExpr history prefix count (BE_Inter (to, tks, BP e1, e2))  =
      let
        val (newTks, tksHistory, tksCount) = renameLocalVarsInTokens prefix count tks
        val ([newe1, newe2], eHistory, eCount)   = renameLocalVarsInExprList (history @ tksHistory) prefix tksCount [e1, e2]
      in
        (BE_Inter (to, newTks, BP newe1, newe2), tksHistory @ eHistory, eCount)
      end
    | renameLocalVarsInExpr history prefix count (BE_Union (to, tks, BP e1, e2))  =
      let
        val (newTks, tksHistory, tksCount) = renameLocalVarsInTokens prefix count tks
        val ([newe1, newe2], eHistory, eCount)   = renameLocalVarsInExprList (history @ tksHistory) prefix tksCount [e1, e2]
      in
        (BE_Union (to, newTks, BP newe1, newe2), tksHistory @ eHistory, eCount)
      end
    | renameLocalVarsInExpr history prefix count (BE_Commutative (to, tk, el) )    =
      let
        val (newel, elHistory, elCount) = renameLocalVarsInExprList history prefix count el
      in
        (BE_Commutative (to, tk, newel), elHistory, elCount)
      end
    | renameLocalVarsInExpr _ _ _ (BE_Struct _) = raise RenameError "record is not supported in this version"
    | renameLocalVarsInExpr _ _ _ (BE_Rec _)    = raise RenameError "record is not supported in this version"
    | renameLocalVarsInExpr _ _ _ (BE_RcAc _)   = raise RenameError "record is not supported in this version"
    | renameLocalVarsInExpr _ _ count e = (e, [], count) (* リテラル式等 *)








  fun renameLocalVarsInPrecondition history (BE_Commutative (_, Keyword "&", exprList)) =
      let
        val resultList = List.map (renameLocalVarsInPrecondition history) exprList
        val (newExprList, newHistoryList) = ListPair.unzip resultList
      in
        (BE_Commutative (SOME BT_Predicate, Keyword "&", newExprList), List.concat newHistoryList)
      end
    | renameLocalVarsInPrecondition history expr =
      let
        val (newExpr, newHistory, _) = renameLocalVarsInExpr history "pl" 1 expr
      in
        (newExpr, List.map (fn (bf, af) => (bf, af, SOME newExpr)) newHistory) 
      end

  fun renameMachineParams [] = ([], [] : (string * string) list)
    | renameMachineParams l =
      let
        val setCount = ref 1
        val varCount = ref 1
        fun getMachineParamsHistoryAux [] = []
          | getMachineParamsHistoryAux ((Var x) :: rest) =
            if
              TypeInference.isTypeSetByName x
            then
              let
                val newIdStr = "PS_" ^ (Utils.intToFixedString 3 (!setCount)) (* 番号とprefixの間に_を入れることで重複解消後と形式が揃い、ファイル出力後に型推論が可能になる (TypeInference.isTypeSetByNameを参照) *)
              in
                (setCount := !setCount + 1; ((x, newIdStr) :: (getMachineParamsHistoryAux rest)))
              end
            else
              let
                val newIdStr = "mp_" ^ (Utils.intToFixedString 3 (!varCount))
              in
                (varCount := !varCount + 1; ((x, newIdStr) :: (getMachineParamsHistoryAux rest)))
              end
          | getMachineParamsHistoryAux _ = raise RenameError "invalid machine parameter"
        val history = getMachineParamsHistoryAux l
        val (_, after) = ListPair.unzip history
      in
        (List.map (fn x => Var x) after, history)
      end

  fun renameConstraints history expr = case renameLocalVarsInExpr history "lv" 1 expr of (newExpr, newHistory, newCount) => (SOME (BC_CONSTRAINTS (BP newExpr)), newHistory, newCount)

  fun renameIdentifiersInSets history l =
      let
        fun renameSetDeclarations [] = []
          | renameSetDeclarations ((BT_Deferred x)     :: rest) =
            let
              val next = renameSetDeclarations rest
            in
              (BT_Deferred (renameIdStr history x)) :: next
            end
          | renameSetDeclarations ((BT_Enum (x, elml)) :: rest) =
            let
              val next = renameSetDeclarations rest
              val nx = renameIdStr history x
              val nelml = List.map (renameIdStr history) elml
            in
              (BT_Enum (nx, nelml)) :: next
            end
          | renameSetDeclarations _ = raise RenameError ""
      in
        renameSetDeclarations l
      end      

  fun renameSets l =
    let
      val dsCount = ref 1
      val esCount = ref 1
      fun getSetsHistoryAux [] = []
        | getSetsHistoryAux ((BT_Deferred idStr) :: rest) =
          let
            val newIdStr = "DS" ^ (Utils.intToFixedString 3 (!dsCount))
          in
            (dsCount := !dsCount + 1; ((idStr, newIdStr) :: (getSetsHistoryAux rest)))
          end
        | getSetsHistoryAux ((BT_Enum (idStr, el)) :: rest) =
          let
            val newIdStr = "ES" ^ (Utils.intToFixedString 3 (!esCount))
            val enumElemsHistory = ListPair.zip (el, (List.map (fn n => "ee" ^ (Utils.intToFixedString 3 n) ^ "_" ^ newIdStr) (Utils.range 1 (List.length el))))
          in
            (dsCount := !esCount + 1; ((idStr, newIdStr) :: enumElemsHistory @ (getSetsHistoryAux rest)))
          end
        | getSetsHistoryAux _ = raise RenameError ""
      val history = getSetsHistoryAux l
    in
      (SOME (BC_SETS (renameIdentifiersInSets history l)), history)
    end
    
  fun getVarDeclarationsHistory prefix l = 
    let
      val count = ref 1
      fun getVarDeclarationsHistoryAux [] = []
        | getVarDeclarationsHistoryAux ((Var idStr) :: rest) =
          let
            val newIdStr = prefix ^ (Utils.intToFixedString 3 (!count))
          in
            (count := !count + 1; ((idStr, newIdStr) :: (getVarDeclarationsHistoryAux rest)))
          end
        | getVarDeclarationsHistoryAux _ = raise RenameError "invalid local variable declaration"
    in
      getVarDeclarationsHistoryAux l
    end 

  fun renameAConstants l =
      let
        val history = getVarDeclarationsHistory "ac" l
        val (_, after) = ListPair.unzip history
      in
        (SOME (BC_ACONSTANTS (List.map (fn x => Var x) after)), history)
      end

  fun renameCConstants l =
      let
        val history = getVarDeclarationsHistory "cc" l
        val (_, after) = ListPair.unzip history
      in
        (SOME (BC_CCONSTANTS (List.map (fn x => Var x) after)), history)
      end
      
  fun renameProperties history count expr = case renameLocalVarsInExpr history "lv" count expr of (newExpr, newHistory, newCount) => (SOME (BC_PROPERTIES (BP newExpr)), newHistory, newCount)
  
  fun renameAVariables l =
      let
        val history = getVarDeclarationsHistory "av" l
        val (_, after) = ListPair.unzip history
      in
        (SOME (BC_AVARIABLES (List.map (fn x => Var x) after)), history)
      end

  fun renameCVariables l =
      let
        val history = getVarDeclarationsHistory "cv" l
        val (_, after) = ListPair.unzip history
      in
        (SOME (BC_CVARIABLES (List.map (fn x => Var x) after)), history)
      end

  fun renameInvariant history count expr = case renameLocalVarsInExpr history "lv" count expr of (newExpr, newHistory, newCount) => (SOME (BC_INVARIANT  (BP newExpr)), newHistory, newCount)

  fun renameLocalVarsInSubstitutionList history anyCount count []        = ([], [], anyCount, count)
    | renameLocalVarsInSubstitutionList history anyCount count (s :: ss) =
      let
        val (news,  sHistory,  sAnyCount,  sCount)  = renameLocalVarsInSubstitution     history anyCount  count  s
        val (newss, ssHistory, ssAnyCount, ssCount) = renameLocalVarsInSubstitutionList history sAnyCount sCount ss
      in
        (news :: newss, sHistory @ ssHistory, ssAnyCount, ssCount)
      end

  and renameLocalVarsInSubstitution history anyCount count (BS_Block s)             =
      let
        val (ns, newHistory, newAnyCount, newCount) = renameLocalVarsInSubstitution history anyCount count s
      in
        (BS_Block ns, newHistory, newAnyCount, newCount)
      end
    | renameLocalVarsInSubstitution history anyCount count BS_Identity              = (BS_Identity, [], anyCount, count)
    | renameLocalVarsInSubstitution history anyCount count (BS_Precondition _)      = raise RenameError "double Precondition"
    | renameLocalVarsInSubstitution history anyCount count (BS_Assertion (BP e, s)) =
      let
        val (newe, eHistory, eCount) = renameLocalVarsInExpr history "lv" count e
        val (news, sHistory, sAnyCount, sCount) = renameLocalVarsInSubstitution history anyCount eCount s
      in
        (BS_Assertion (BP newe, news), eHistory @ sHistory, sAnyCount, sCount)
      end
    | renameLocalVarsInSubstitution history anyCount count (BS_Choice sl)           =
      let
        val (newsl, sHistory, sAnyCount, sCount) = renameLocalVarsInSubstitutionList history anyCount count sl
      in
        (BS_Choice newsl, sHistory, sAnyCount, sCount)
      end
    | renameLocalVarsInSubstitution history anyCount count (BS_If l)                =
      let
        val el = List.concat (List.map (fn (SOME (BP e), _) => [e] | _ => []) l)
        val sl = List.map (fn (_, s) => s) l
        val (newel, elHistory, elCount) = renameLocalVarsInExprList history "lv" count el
        val (newsl, slHistory, slAnyCount, slCount) = renameLocalVarsInSubstitutionList history anyCount elCount sl
        val newl = ListPair.zip ((List.map (fn e => SOME (BP e)) newel) @ [NONE], newsl)
      in
        (BS_If newl, elHistory @ slHistory, slAnyCount, slCount)
      end
    | renameLocalVarsInSubstitution history anyCount count (BS_Select l)            =
      let
        val el = List.concat (List.map (fn (SOME (BP e), _) => [e] | _ => []) l)
        val sl = List.map (fn (_, s) => s) l
        val (newel, elHistory, elCount) = renameLocalVarsInExprList history "lv" count el
        val (newsl, slHistory, slAnyCount, slCount) = renameLocalVarsInSubstitutionList history anyCount elCount sl
        val newl = ListPair.zip ((List.map (fn e => SOME (BP e)) newel) @ [NONE], newsl)
      in
        (BS_Select newl, elHistory @ slHistory, slAnyCount, slCount)
      end
    | renameLocalVarsInSubstitution history _ _ (BS_Case _) = raise RenameError "CASE substitution is not primitive"
    | renameLocalVarsInSubstitution history anyCount count (BS_Any (tks, BP e, s))  =
      let
        val (newTks, tksHistory, tksCount) = renameLocalVarsInTokens "al" anyCount tks
        val (newe, eHistory, eCount) = renameLocalVarsInExpr (history @ tksHistory) "lv" count e
        val (news, sHistory, sAnyCount, sCount) = renameLocalVarsInSubstitution (history @ tksHistory) tksCount eCount s
      in
        (BS_Any (newTks, BP newe, news), tksHistory @ eHistory @ sHistory, sAnyCount, sCount)
      end
    | renameLocalVarsInSubstitution history _ _ (BS_Let        _        ) = raise RenameError "LET substitution is not primitive"
    | renameLocalVarsInSubstitution history _ _ (BS_BecomesElt (el, re)) = raise RenameError ":: substitution is not primitive"
    | renameLocalVarsInSubstitution history anyCount count (BS_BecomesSuchThat (el, BP e))     =
      let
        val (newel, lhsHistory, lhsCount) = renameLocalVarsInExprList history "lv" count el
        val (newe,  rhsHistory, rhsCount) = renameLocalVarsInExpr (history @ lhsHistory) "lv" lhsCount e
      in
        (BS_BecomesSuchThat (newel, BP newe), lhsHistory @ rhsHistory, anyCount, rhsCount)
      end
    | renameLocalVarsInSubstitution history _ _ (BS_Call _) = raise RenameError "Operations call in substitution is not supported in this version"
    | renameLocalVarsInSubstitution history anyCount count (BS_BecomesEqual (e1, e2)) =
      let
        val (newe1, e1History, e1Count) = renameLocalVarsInExpr history "lv" count e1
        val (newe2, e2History, e2Count) = renameLocalVarsInExpr (history @ e1History) "lv" e1Count e2
      in
        (BS_BecomesEqual (newe1, newe2), e1History @ e2History, anyCount, e2Count)
      end
    | renameLocalVarsInSubstitution history _ _ (BS_BecomesEqualList _) = raise RenameError "substitution like \"a, b := c, d\" is not primitive"
    | renameLocalVarsInSubstitution history anyCount count (BS_Simultaneous sl) =
      let
        val (newsl, sHistory, sAnyCount, sCount) = renameLocalVarsInSubstitutionList history anyCount count sl
      in
        (BS_Simultaneous newsl, sHistory, sAnyCount, sCount)
      end
    | renameLocalVarsInSubstitution history _ _ _ = raise RenameError "Renaming is only for models"


  fun renameOperation history count (BOp (oprName, outputs, inputs, BS_Precondition (BP preconditionExpr, substitution))) =
      let
        val outputsHistory = getVarDeclarationsHistory "op" outputs
        val (_, newOutputStrs) = ListPair.unzip outputsHistory
        val newOutputs = List.map (fn x => Var x) newOutputStrs

        val inputsHistory  = getVarDeclarationsHistory "ip" inputs
        val (_, newInputStrs)  = ListPair.unzip inputsHistory
        val newInputs  = List.map (fn x => Var x) newInputStrs
        val (newPreconditionExpr, preconditionHistory) = renameLocalVarsInPrecondition (history @ inputsHistory @ outputsHistory) preconditionExpr
        
        val (newSubstitution, substitutionHistory, _, _) = renameLocalVarsInSubstitution (history @ inputsHistory @ outputsHistory) 1 count substitution

        val newHistory = (List.map (fn (bf, af) => (bf, af, NONE)) (outputsHistory @ inputsHistory @ substitutionHistory)) @ preconditionHistory
      in
        (SOME (BC_OPERATIONS [(BOp (oprName, newOutputs, newInputs, BS_Precondition ((BP newPreconditionExpr), newSubstitution)))]), newHistory)
      end
    | renameOperation history count (BOp (oprName, outputs, inputs, substitution)) =
      let
        val outputsHistory = getVarDeclarationsHistory "op" outputs
        val (_, newOutputStrs) = ListPair.unzip outputsHistory
        val newOutputs = List.map (fn x => Var x) newOutputStrs

        val inputsHistory  = getVarDeclarationsHistory "ip" inputs
        val (_, newInputStrs)  = ListPair.unzip inputsHistory
        val newInputs  = List.map (fn x => Var x) newInputStrs

        val (newSubstitution, substitutionHistory, _, _) = renameLocalVarsInSubstitution (history @ inputsHistory @ outputsHistory) 1 count substitution

        val newHistory = List.map (fn (bf, af) => (bf, af, NONE)) (outputsHistory @ inputsHistory @ substitutionHistory)
      in
        (SOME (BC_OPERATIONS [(BOp (oprName, newOutputs, newInputs, newSubstitution))]), newHistory)
      end

  (* モデル全体を受け取り、識別子置換後のモデルと識別子置換履歴を返す *)
  (* BComponent -> (BComponent * (string * string * BExpr option) list) *)
  (* モデル -> (識別子置換後のモデル, [(置換前の識別子名, 置換後の識別子名, 置換された識別子が事前条件内の局所変数である場合はその置換後の式 option)]) *)
  fun rename (BMch (machineName, machineParams, clauses)) =
    let
      (* - マシンパラメータ *)
      val (resultMachineParams, machineParamsHistory) = renameMachineParams machineParams
      
      (* - CONSTRAINTS *)
      val (resultConstraintsOpt, localVarsInConstraintsHistory, localVarsCountConstraints) =
        case List.find (fn (BC_CONSTRAINTS _) => true | _ => false) clauses of
          NONE => (NONE, [], 1)
        | (SOME (BC_CONSTRAINTS (BP e))) => renameConstraints machineParamsHistory e (*renameLocalVarsInExpr "lv" 1 e*)
        | _ => raise RenameError ""
        
      (* - SETS *)
      val (resultSetsOpt, setsHistory) =
        case List.find (fn (BC_SETS _)        => true | _ => false) clauses of
          NONE => (NONE, [])
        | (SOME (BC_SETS l))             => renameSets l
        | _ => raise RenameError ""

      (* - ACONSTANTS *)
      val (resultAConstantsOpt, aconstantsHistory) =
        case List.find (fn (BC_ACONSTANTS _)  => true | _ => false) clauses of
          NONE => (NONE, [])
        | (SOME (BC_ACONSTANTS l))       => renameAConstants l
        | _ => raise RenameError ""

      (* - CCONSTANTS *)
      val (resultCConstantsOpt, cconstantsHistory) =
        case List.find (fn (BC_CCONSTANTS _)  => true | _ => false) clauses of
          NONE => (NONE, [])
        | (SOME (BC_CCONSTANTS l))       => renameCConstants l
        | _ => raise RenameError ""

      val historyBeforeProperties = machineParamsHistory @ localVarsInConstraintsHistory @ setsHistory @ aconstantsHistory @ cconstantsHistory
      
      (* - PROPERTIES *)
      val (resultPropertiesOpt, localVarsInPropertiesHistory, localVarsCountProperties) =
        case List.find (fn (BC_PROPERTIES _)  => true | _ => false) clauses of
          NONE => (NONE, [], localVarsCountConstraints)
        | (SOME (BC_PROPERTIES (BP e)))  => renameProperties historyBeforeProperties localVarsCountConstraints e (*renameLocalVarsInExpr "lv" localVarsCountConstraints e*)
        | _ => raise RenameError ""

      (* - AVARIABLES *)
      val (resultAVariablesOpt, avariablesHistory) =
        case List.find (fn (BC_AVARIABLES _)  => true | _ => false) clauses of
          NONE => (NONE, [])
        | (SOME (BC_AVARIABLES l))       => renameAVariables l
        | _ => raise RenameError ""

      (* - CVARIABLES *)
      val (resultCVariablesOpt, cvariablesHistory) =
        case List.find (fn (BC_CVARIABLES _)  => true | _ => false) clauses of
          NONE => (NONE, [])
        | (SOME (BC_CVARIABLES l))       => renameCVariables l
        | _ => raise RenameError ""

      val historyBeforeInvariant = historyBeforeProperties @ localVarsInPropertiesHistory @ avariablesHistory @ cvariablesHistory
      
      (* - INVARIANT *)
      val (resultInvariantOpt, localVarsInInvariantHistory, localVarsCountInvariant) =
        case List.find (fn (BC_INVARIANT _) => true | _ => false) clauses of
          NONE => (NONE, [], localVarsCountProperties)
        | (SOME (BC_INVARIANT (BP e)))   => renameInvariant historyBeforeInvariant localVarsCountProperties e(*renameLocalVarsInExpr "lv" localVarsCountProperties e*)
        | _ => raise RenameError ""

      val historyBeforeOperations = historyBeforeInvariant @ localVarsInInvariantHistory 
      
      (* - OPERATIONS *)
      val (resultOperationsOpt, localVarsInOperationHistory) =
        case List.find (fn (BC_OPERATIONS _) => true | _ => false) clauses of
          NONE => (NONE, [])
        | (SOME (BC_OPERATIONS [opr]))   => renameOperation historyBeforeOperations localVarsCountInvariant opr
        | _ => raise RenameError "No operation or several operations aregiven"

       val resultHistory = localVarsInOperationHistory @ (List.map (fn (b, a) => (b, a, NONE)) historyBeforeOperations)

       val resultClausesOpt = [
                                resultConstraintsOpt,
                                resultSetsOpt,
                                resultAConstantsOpt,
                                resultCConstantsOpt,
                                resultPropertiesOpt,
                                resultAVariablesOpt,
                                resultCVariablesOpt,
                                resultInvariantOpt,
                                resultOperationsOpt
                              ]
       val resultClauses = List.concat (List.map (fn NONE => [] | (SOME x) => [x]) resultClausesOpt)
       val resultMachine = BMch (machineName, resultMachineParams, resultClauses)
    in
      (resultMachine, resultHistory)
    end
   | rename _ = raise RenameError "Renaming is only for models"
   
end
