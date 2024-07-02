structure OperationDivision =
struct
  exception OpDivError of string

  (* 分割前の代入文からその代入文内のIF条件を全て抽出しリストとして返す *)
      (* BSubstitution -> BPredicate list *)
      (* 分割前の代入文 (事前条件去済み) -> [IF文に登場する全ての条件] *)
  fun extractAllConditions (BS_Simultaneous l) =
      List.concat (List.map extractAllConditions l)
    | extractAllConditions (BS_If l) =
      List.concat (List.map (fn (NONE, s) => extractAllConditions s | (SOME p, s) => p :: (extractAllConditions s)) l)
    | extractAllConditions s = []

  (* 番号付き代入文のリストを受け取り、互いに依存する番号付き代入文のグループのリストと、番号付き代入文の依存関係を番号付き代入文の番号を用いて表したものを組にして返す *)
      (* (int * BSubstitution) list -> (((int * BSubstitution) list list) * ((int * int) list)) *)
      (* [番号付き代入文] -> [[互いに依存する番号付き代入文のグループ]], [(影響を受ける (結合順を先にするべき) 代入文の番号, 影響を与える (結合順を後にするべき) 代入文の番号)] *)
  fun findCodependence indexedSubstitutions =
      let
        (* 番号付き代入文をその代入文内で変更される識別子、参照される識別子と組にする *)
        fun makeGraphNode (sId, s) =
            let
              val (cVars, rVars) = AST.extractVars s
            in
              ((sId, s), cVars, rVars)
            end

        (* 参照関係のグラフのノードを作成 *)
        val graphNodes = List.map makeGraphNode indexedSubstitutions

        (* グラフのノードのデータ (変更・参照識別子) からノード同士の依存関係を求め、
           始点と終点のノードの番号付き代入文の組によってエッジを表現する *)
        val (graphEdges : ((int * BSubstitution) * (int * BSubstitution)) list) =
          Utils.deleteDouble Utils.eqto
          (List.filter (fn (x, y) => x <> y)
            (List.concat
              (List.concat
                (List.concat
                  (List.map (fn (indexedSubstitution1, changedVars1, referenceVars1) =>
                          (List.map (fn referenceVar1 =>
                              List.map (fn (indexedSubstitution2, changedVars2, referenceVars2) =>
                                  if
                                    Utils.isIn referenceVar1 changedVars2
                                  then
                                    [(indexedSubstitution1, indexedSubstitution2)]
                                  else
                                    [])
                              graphNodes)
                      referenceVars1))
                    graphNodes)))))

        (* 依存関係を辿り、相互依存を検出する *)
        fun trace initialIndexedSubstitution =
            let
              val fstEdges = List.filter (fn (x, y) => x = initialIndexedSubstitution) graphEdges
              val fstDependings = List.map (fn (x, y) => y) fstEdges
              fun traceAux route brc =
                  if
                    brc = initialIndexedSubstitution
                  then
                    route
                  else
                    if
                      Utils.isIn brc route
                    then
                      []
                    else
                      let
                        val nextEdges = List.filter (fn (x, y) => x = brc) graphEdges
                        val nextDependings = List.map (fn (x, y) => y) nextEdges
                      in
                        List.concat (List.map (traceAux (brc :: route)) nextDependings)
                      end
            in
              Utils.deleteDouble Utils.eqto (List.concat (List.map (traceAux [initialIndexedSubstitution]) fstDependings))
            end

        (* グラフのエッジを代入文の番号のみを用いて表現したもの *)
        val graphEdgesById = List.map (fn ((i1, _), (i2, _)) => (i1, i2)) graphEdges
      in
        (* gropingIndexedSubstitutions関数でallIndexedSubstitutionsを参照するため、独立している代入文は含まれなくてもOK *)
        (List.map trace indexedSubstitutions, graphEdgesById)
      end

  (* 他の番号付き代入文と相互に依存しないような番号付き代入文を含まない、要素に重複を許した番号付き代入文のグループのリストと全ての番号付き代入文のリストを受け取り、
      重複無く全番号付き代入文を含むような番号付き代入文のグループのリストを返す *)
      (* (int * BSubstitution) list list -> (int * BSubstitution) list -> (int * BSubstitution) list list *)
      (* [[相互に依存する番号付き代入文の集合 (要素に重複あり・独立した代入文を含まない) ]] -> [全ての番号付き代入文]
        -> [[全ての番号付き代入文を相互依存によってグループ化したもの (重複なし・全番号付き代入文を含む) ]] *)
  fun groupingIndexedSubstitutions (codependentSets : (int * BSubstitution) list list) ([] : (int * BSubstitution) list) : (int * BSubstitution) list list = codependentSets
    | groupingIndexedSubstitutions codependentSets (is :: iss) =
      let
        val (includings, notIncludings) = List.partition (List.exists (Utils.eqto is)) codependentSets
        val newCodependentSets = (Utils.deleteDouble Utils.eqto (is :: (List.concat includings))) :: notIncludings
      in
        groupingIndexedSubstitutions newCodependentSets iss
      end

  fun simplifySubstitution (BS_Block s) = s
    (* PRE は想定せず (一番外側のは除去済み) *)
    | simplifySubstitution (BS_Assertion (_, BS_Identity)) = BS_Identity
    (* CHOICE は対象外 *)
    | simplifySubstitution (BS_If l) =
      let
        fun conjunction [] = raise OpDivError ""
          | conjunction [e] = e
          | conjunction es = BE_Commutative (SOME BT_Predicate, Keyword "&", es)

        fun deleteSkipsInIfBranches skippedConditions ((SOME (BP e), BS_Identity) :: r) = deleteSkipsInIfBranches (e :: skippedConditions) r
          | deleteSkipsInIfBranches skippedConditions ((SOME (BP e), s          ) :: r) =
            let
              val newConditionExpr = conjunction (e :: (List.map (fn expr => BE_Node1 (SOME BT_Predicate, Keyword "not", expr)) skippedConditions))
              val next = deleteSkipsInIfBranches skippedConditions r
            in
              (SOME (BP newConditionExpr), s) :: next
            end
          | deleteSkipsInIfBranches _                 [(NONE       , BS_Identity)     ] = []
          | deleteSkipsInIfBranches []                [(NONE       , s          )     ] = [(NONE, s)]
          | deleteSkipsInIfBranches skippedConditions [(NONE       , s          )     ] =
            let
              val newConditionExpr = conjunction (List.map (fn expr => BE_Node1 (SOME BT_Predicate, Keyword "not", expr)) skippedConditions)
            in
              [(SOME (BP newConditionExpr), s)]
            end
          | deleteSkipsInIfBranches _                 []                                = []
          | deleteSkipsInIfBranches _                 _                                 = raise OpDivError "invalid IF"

      in
        case deleteSkipsInIfBranches [] l of [] => BS_Identity | res => BS_If res
      end
    (* SELECT は対象外 *)
    (* CASE は IF に変換済み *)
    (* ANY は分割しない *)
    (* LET は展開済み *)
    | simplifySubstitution (BS_Simultaneous l) =
      (
        case List.filter (Utils.neqto BS_Identity) l of
          []  => BS_Identity
        | [s] => s
        | ss  => BS_Simultaneous ss
      )
    | simplifySubstitution (BS_Sequencing l) =
      (
        case List.filter (Utils.neqto BS_Identity) l of
          []  => BS_Identity
        | [s] => s
        | ss  => BS_Sequencing ss
      )
    | simplifySubstitution s = s

  fun simplifySubstitutionTree s = Utils.repeatApply (AST.mapSubstitutionTree simplifySubstitution) s

  (* 代入文を受け取り、番号と番号による依存関係付きの分割済み代入文を返す *)
      (* BSubstitution -> (int * BSubstitution * (int list)) list *)
      (* 分割前の代入文 (事前条件除去済み) -> [(番号, 分割後の代入文, [結合順が自身より先になる代入文の番号])] *)
  fun divideSubstitution substitution =
      let
        val (allChangedVars, _) = AST.extractVars substitution (* すべての変更変数 *)

        (* ある変数を変更する最小単位の代入文を残して他をskipにする関数 *)
        fun extractSubstitutionChangingVar v (BS_Block s) = BS_Block (extractSubstitutionChangingVar v s)
          | extractSubstitutionChangingVar v (BS_Assertion (p, s)) = BS_Assertion (p, extractSubstitutionChangingVar v s)
          (* CHOICE は対象外 *)
          | extractSubstitutionChangingVar v (BS_If l) = BS_If (List.map (fn (pOpt, s) => (pOpt, extractSubstitutionChangingVar v s)) l)
          (* SELECT は対象外 *)
          (* CASE は IF に変換済み *)
          (* ANYは 分離しない *)
          (* LET は展開済み *)
          | extractSubstitutionChangingVar v (BS_Simultaneous l) = BS_Simultaneous (List.map (extractSubstitutionChangingVar v) l)
          | extractSubstitutionChangingVar v s =
            let
              val (changedVars, _) = AST.extractVars s
            in
              if
                List.exists (Utils.eqto v) changedVars
              then
                s
              else
                BS_Identity
            end

         val allDividedSubstitutionList = List.map (fn v => extractSubstitutionChangingVar v substitution) allChangedVars

         (* 最小単位の代入文に被りがあるならばtrue *)
         fun isMergeableByChangedVars (BS_Block        s1         ) (BS_Block        s2         ) = isMergeableByChangedVars s1 s2
           | isMergeableByChangedVars BS_Identity                   _                             = false
           | isMergeableByChangedVars _                             BS_Identity                   = false
           | isMergeableByChangedVars (BS_Assertion    (_, s1    )) (BS_Assertion    (_, s2    )) = isMergeableByChangedVars s1 s2
           | isMergeableByChangedVars (BS_If           l1         ) (BS_If           l2         ) = ListPair.exists (fn ((_, s1), (_, s2)) => isMergeableByChangedVars s1 s2) (l1, l2)
           | isMergeableByChangedVars (BS_Simultaneous l1         ) (BS_Simultaneous l2         ) = ListPair.exists (Utils.uncurry isMergeableByChangedVars) (l1, l2)
           | isMergeableByChangedVars s1                            s2                            = if s1 = s2 then true else raise OpDivError ""

         fun mergeSubstitutions (BS_Block        s1          ) (BS_Block        s2          ) = BS_Block (mergeSubstitutions s1 s2)
           | mergeSubstitutions BS_Identity                    s                              = s
           | mergeSubstitutions s                              BS_Identity                    = s
           | mergeSubstitutions (BS_Assertion    (p1, s1    )) (BS_Assertion    (p2, s2    )) = if p1 = p2 then BS_Assertion (p1 ,(mergeSubstitutions s1 s2)) else raise OpDivError ""
           | mergeSubstitutions (BS_If           l1          ) (BS_If           l2          ) = BS_If (ListPair.map (fn ((pOpt1, s1), (pOpt2, s2)) => if pOpt1 = pOpt2 then (pOpt1, mergeSubstitutions s1 s2) else raise OpDivError "") (l1, l2))
           | mergeSubstitutions (BS_Simultaneous l1          ) (BS_Simultaneous l2          ) = BS_Simultaneous (ListPair.map (Utils.uncurry mergeSubstitutions) (l1, l2))
           | mergeSubstitutions s1                             s2                             = if s1 = s2 then s1 else raise OpDivError ""

         (* 最小単位の代入文内で複数の変数を変更している場合それらの変数を変更する代入分をマージする *)
         fun mergeByChangedVars sList =
             let
               fun mergeByChangedVarsAux [] = []
                 | mergeByChangedVarsAux (s :: ss) =
                   let
                     val (mergeable, unmergeable) = List.partition (isMergeableByChangedVars s) ss
                     val merged = List.foldl (Utils.uncurry mergeSubstitutions) s mergeable
                   in
                     merged :: (mergeByChangedVarsAux unmergeable)
                   end
               val initialLength = List.length sList
               val res = mergeByChangedVarsAux sList
             in
               if
                 List.length res = initialLength
               then
                 res
               else
                 mergeByChangedVars res
             end

        fun indexing l = ListPair.zip (Utils.range 1 (List.length l), l)
        val simplifiedSubstitutionList = indexing (List.map simplifySubstitutionTree (mergeByChangedVars allDividedSubstitutionList))

        val (codependentSets, dependenceEdges) = findCodependence simplifiedSubstitutionList
        val groups = List.filter (Utils.neqto []) (groupingIndexedSubstitutions codependentSets simplifiedSubstitutionList)

        val indexedGroups = indexing groups
        fun searchGroupDependencies [] = []
          | searchGroupDependencies ((sId1, sId2) :: rest) =
            let
              val nextDependencies = searchGroupDependencies rest
              val groupId1 = #1 (valOf (List.find (fn (_, group) => List.exists (fn (idx, _) => idx = sId1) group) indexedGroups))
              val groupId2 = #1 (valOf (List.find (fn (_, group) => List.exists (fn (idx, _) => idx = sId2) group) indexedGroups))
            in
              if
                groupId1 = groupId2
              then
                nextDependencies
              else
                (groupId1, groupId2) :: nextDependencies
            end
        val groupDependenceEdges = searchGroupDependencies dependenceEdges
        fun searchSubsequentIndex idx = List.map (fn (i1, _) => i1) (List.filter (fn (_, i2) => i2 = idx) groupDependenceEdges)
        fun appendIndexedSubstitutions [] = raise OpDivError ""
          | appendIndexedSubstitutions l = BS_Simultaneous (List.concat (List.map (fn (_, BS_Simultaneous ss) => ss | (_, s) => [s]) l))
      in
        (List.map (fn (idx, group) => (idx, appendIndexedSubstitutions group, Utils.deleteDouble Utils.eqto (searchSubsequentIndex idx))) indexedGroups) : (int * BSubstitution * (int list)) list
      end


  (* 操作を分割して文字列による依存関係情報付きの分割結果の操作のリストを返す *)
      (* BOperation -> (string * BOperation * (string list)) list *)
      (* 操作 -> [(細分化モデルのファイル名になるべき文字列の後半 (元の操作名-番号), 分割後の操作, [結合順が自身より先になる細分化モデルのファイル名の後半])] *)
  fun divideOp (BOp (oprName, oparams, iparams, BS_Precondition (p, s))) =
      let
        val ss = divideSubstitution s
        val changedInOriginalOperation = #1(AST.extractVars s)
        fun indexToFileName i = oprName ^ "-" ^ (Utils.intToFixedString 3 i)
      in
        List.map (fn (idx, ns, deps) => (indexToFileName idx, BOp ("operation", oparams, iparams, BS_Precondition (p, ns)), changedInOriginalOperation, List.map indexToFileName deps)) ss
      end
    | divideOp (BOp (oprName, oparams, iparams, s)) =
      let
        val ss = divideSubstitution s
        val changedInOriginalOperation = #1(AST.extractVars s)
        fun indexToFileName i = oprName ^ "-" ^ (Utils.intToFixedString 3 i)
      in
        List.map (fn (idx, ns, deps) => (indexToFileName idx, BOp ("operation", oparams, iparams, ns), changedInOriginalOperation, List.map indexToFileName deps)) ss
      end


  (* 操作のリストの各要素を分割し名前と文字列による依存関係情報付きの分割結果の操作のリストを返す *)
      (* BOperation list -> (string * BOperation * (string list)) list *)
      (* [操作] -> [(細分化モデルのファイル名になるべき文字列の後半 (元の操作名-番号), 分割後の操作, [結合順が自身より先になる細分化モデルのファイル名の後半])] *)
  fun divideOps ops = List.concat (List.map divideOp ops)


  (* 初期化の代入文を受け取り、名前付きの分割結果の操作のリストを返す *)
      (* BSubstitution -> (string * BOperation) list *)
      (* INITIALISATIONの代入文 -> [(細分化モデルのファイル名になるべき文字列の後半 (番号), 分割後の操作)] *)
  fun divideInitialisationSubstitution s =
    let
      val ss = divideSubstitution s
    in
      List.map (fn (idx, ns, _) => (Utils.intToFixedString 3 idx, (BOp ("operation", [], [], ns)))) ss
    end

  (* 操作分割を行う関数 *)
      (* BComponent -> (string * BComponent * (string list)) list *)
      (* モデル -> [(細分化モデルのファイル名, 操作分割後の操作を一つしか持たないモデル, [自身より結合順が先になる細分化モデルのファイル名])] *)
  fun divide (BMch (mchName, param, clauses)) =
      let
        (* 入力モデルの節のリストのうち, 代入文を含む節 (INITIALISATION, OPERATIONS) を除いたもの *)
        val clausesWithoutSubstitutions = List.filter (fn (BC_OPERATIONS _) => false | (BC_INITIALISATION _) => false | _ => true) clauses

        (* ファイル名の文字列を作るための補助的な関数 *)
        fun makeOperationMachineName name = mchName ^ "-op-" ^ name
        fun makeInitialisationMachineName name = mchName ^ "-init-" ^ name

        (* OPERATIONSの各操作を分割してできた細分化モデル *)
        val oprsSlicedModels = (case (List.find (fn (BC_OPERATIONS _) => true | _ => false) clauses) of
                                 (SOME (BC_OPERATIONS ops)) =>
                                   let
                                     val dividedOps = divideOps ops
                                     val newClausesList = List.map (fn (slicedModelName, opr, changedInOriginalOperation, deps) => (slicedModelName, (BC_OPERATIONS [opr]) :: clausesWithoutSubstitutions, changedInOriginalOperation, deps)) dividedOps
                                   in
                                     List.map (fn (slicedModelName, x, changedInOriginalOperation, deps) => (makeOperationMachineName slicedModelName, BMch ("Mch", param, x), changedInOriginalOperation, List.map makeOperationMachineName deps)) newClausesList
                                   end
                                 | NONE => []
                                 | _ => raise OpDivError "")

        (* INITIALISATIONを分割してできた細分化モデル *)
        val initSlicedModels = (case (List.find (fn (BC_INITIALISATION _) => true | _ => false) clauses) of
                                 (SOME (BC_INITIALISATION s)) =>
                                   let
                                     val changedInOriginalInit = #1(AST.extractVars s)
                                     val dividedOps = divideInitialisationSubstitution s
                                     val newClausesList = List.map (fn (slicedModelName, opr) => (slicedModelName, (BC_OPERATIONS [opr]) :: clausesWithoutSubstitutions)) dividedOps
                                   in
                                     List.map (fn (slicedModelName, x) => (makeInitialisationMachineName slicedModelName, BMch ("Mch", param, x), changedInOriginalInit, [])) newClausesList
                                   end
                                 | NONE => []
                                 | _ => raise OpDivError "")
      in
        oprsSlicedModels @ initSlicedModels
      end
    | divide _ = raise OpDivError "this program can process only Machines." (* リファインメントや実装が入力された場合 *)
end
