structure Parser =
struct
  exception ParseError of string

      (* 先にマシンの最後のENDを取り除く関数 *)
      (* BToken list -> BToken list *)
  fun removeEnd alltks =
      case (rev alltks) of
        ((Keyword "END") :: tks) => (rev tks)
      | _ => raise ParseError "missing END"

      (* マシンパラメータのパース *)
      (* BToken list -> BToken list * BToken list *)
  fun parseAux ((Var x) :: (Keyword ",") :: rest) =
       let
         val (vv, rr) = parseAux rest
       in
         (((Var x) :: vv), rr)
       end
     | parseAux ((Var x) :: (Keyword ")") :: rest) = ([Var x], rest)
     | parseAux _ = raise ParseError "parse error in MACHINE/REFINEMENT/IMPLEMENTATION parameter"

      (* 詳細化元のコンポーネント名を求める *)
      (* BToken list -> string * BToken list *)
  fun findRefines ((Keyword "REFINES") :: (Var mn) :: rest) = (mn, rest)
    | findRefines (x                   :: xs)               = (case (findRefines xs) of (mn, rest) => (mn, x :: rest))
    | findRefines []                                        = raise ParseError "missing REFINES"

  fun renamedToVar (Renamed (s1, s2)) = Var (s1 ^ "." ^ s2)
    | renamedToVar v = v

  fun distinguishRenamedVar (Var varStr) =
      let
        val varStrList = List.map String.implode (Utils.chopList (Utils.eqto #".") (String.explode varStr))
      in
        case varStrList of
          [newStr] => Var newStr
        | [newStr1, newStr2] => Renamed (newStr1, newStr2)
        | _ => raise ParseError "invalid renaming of identifier"
      end
    | distinguishRenamedVar x = x

  fun distinguishRenamedVarInComponent c = AST.mapVarsInComponent distinguishRenamedVar c

      (* モデル全体の構文解析を行う関数 *)
      (* val parse : BToken list -> BComponent *)
  fun parse ((Keyword "MACHINE") :: (Var machineName) :: (Keyword "(") :: btokens) =
      let
        val (v, r) = parseAux btokens
      in
        distinguishRenamedVarInComponent (BMch (machineName, v, (pClauses (removeEnd r))))
      end
    | parse ((Keyword "MACHINE") :: (Var machineName) :: btokens) =
        distinguishRenamedVarInComponent (BMch (machineName, [], (pClauses (removeEnd btokens))))
    | parse ((Keyword "REFINEMENT") :: (Var refinementName) :: (Keyword "(") :: btokens) =
      let
        val (v, r) = parseAux btokens
        val (machineName, rr) = findRefines r
      in
        distinguishRenamedVarInComponent (BRef (refinementName, machineName, v, (pClauses (removeEnd rr))))
      end
    | parse ((Keyword "REFINEMENT") :: (Var refinementName) :: btokens) =
      let
        val (machineName, r) = findRefines btokens
      in
        distinguishRenamedVarInComponent (BRef (refinementName, machineName, [], (pClauses (removeEnd r))))
      end
    | parse ((Keyword "IMPLEMENTATION") :: (Var implementationName) :: (Keyword "(") :: btokens) =
      let
        val (v, r) = parseAux btokens
        val (machineName, rr) = findRefines r
      in
        distinguishRenamedVarInComponent (BImp (implementationName, machineName, v, (pClauses (removeEnd rr))))
      end
    | parse ((Keyword "IMPLEMENTATION") :: (Var implementationName) :: btokens) =
      let
        val (machineName, r) = findRefines btokens
      in
        distinguishRenamedVarInComponent (BImp (implementationName, machineName, [], (pClauses (removeEnd r))))
      end
    | parse _ = raise ParseError "invalid component header"
  and

    (* 節のリストをパースする関数 *)
    (* val pClauses : BToken list -> BClause list *)
      pClauses [] = []
    | pClauses ((Keyword "CONSTRAINTS") :: btks)        =
      let
        val (p, rest) = pPredicate btks
      in
        (BC_CONSTRAINTS p) :: (pClauses rest)
      end
    | pClauses ((Keyword "PROPERTIES") :: btks)         =
      let
        val (p, rest) = pPredicate btks
      in
        (BC_PROPERTIES p) :: (pClauses rest)
      end
    | pClauses ((Keyword "INVARIANT") :: btks)          =
      let
        val (p, rest) = pPredicate btks
      in
        (BC_INVARIANT p) :: (pClauses rest)
      end
    | pClauses ((Keyword "ASSERTIONS") :: btks)         =
      let
        val (p, rest) = pPredicate btks
      in
        (BC_ASSERTIONS p) :: (pClauses rest)
      end
    | pClauses ((Keyword "SEES") :: btks)               =
      let
        val (mis, rest) = pMachineInstanciationList btks
      in
        (BC_SEES mis) :: (pClauses rest)
      end
    | pClauses ((Keyword "INCLUDES") :: btks)           =
      let
        val (mis, rest) = pMachineInstanciationList btks
      in
        (BC_INCLUDES mis) :: (pClauses rest)
      end
    | pClauses ((Keyword "PROMOTES") :: btks)           =
      let
        val (mis, rest) = pMachineInstanciationList btks
      in
        (BC_PROMOTES mis) :: (pClauses rest)
      end
    | pClauses ((Keyword "EXTENDS") :: btks)            =
      let
        val (mis, rest) = pMachineInstanciationList btks
      in
        (BC_EXTENDS mis) :: (pClauses rest)
      end
    | pClauses ((Keyword "USES") :: btks)               =
      let
        val (mis, rest) = pMachineInstanciationList btks
      in
        (BC_USES mis) :: (pClauses rest)
      end
    | pClauses ((Keyword "IMPORTS") :: btks)            =
      let
        val (mis, rest) = pMachineInstanciationList btks
      in
        (BC_IMPORTS mis) :: (pClauses rest)
      end
    | pClauses ((Keyword "CONCRETE_CONSTANTS") :: btks) =
      let
        val (vs, rest) = pVarList btks
      in
        (BC_CCONSTANTS vs) :: (pClauses rest)
      end
    | pClauses ((Keyword "ABSTRACT_CONSTANTS") :: btks) =
      let
        val (vs, rest) = pVarList btks
      in
        (BC_ACONSTANTS vs) :: (pClauses rest)
      end
    | pClauses ((Keyword "CONSTANTS") :: btks)          =
      let
        val (vs, rest) = pVarList btks
      in
        (BC_CCONSTANTS vs) :: (pClauses rest)
      end
    | pClauses ((Keyword "VALUES") :: btks)             =
      let
        val (alle, rest) = pExpr btks
        fun pValues (BE_Node2 (_, Keyword ";", a, b)) = (pValues a) @ [b]
          | pValues e = [e]
        val vals = List.map (fn (BE_Node2 (_, Keyword "=", BE_Leaf (_, Var x), e)) => (Var x, e) | _ => raise ParseError "invalid form of VALUES") (pValues alle)
      in
        (BC_VALUES vals) :: (pClauses rest)
      end
    | pClauses ((Keyword "CONCRETE_VARIABLES") :: btks) =
      let
        val (vs, rest) = pVarList btks
      in
        (BC_CVARIABLES vs) :: (pClauses rest)
      end
    | pClauses ((Keyword "ABSTRACT_VARIABLES") :: btks) =
      let
        val (vs, rest) = pVarList btks
      in
        (BC_AVARIABLES vs) :: (pClauses rest)
      end
    | pClauses ((Keyword "VARIABLES") :: btks)          =
      let
        val (vs, rest) = pVarList btks
      in
        (BC_AVARIABLES vs) :: (pClauses rest)
      end
    | pClauses ((Keyword "SETS") :: btks)               =
      let
        val (tys, rest) = pSets btks
      in
        (BC_SETS tys) :: (pClauses rest)
      end
    | pClauses ((Keyword "INITIALISATION") :: btks)     =
      let
        val (s, rest) = pSubstitution btks
      in
        (BC_INITIALISATION s) :: (pClauses rest)
      end
    | pClauses ((Keyword "OPERATIONS") :: btks)         =
      let
        val (ops, rest) = pOperations btks
      in
        (BC_OPERATIONS ops) :: (pClauses rest)
      end
    | pClauses ((Keyword "DEFINITIONS") :: btks)        =
      let
        val (defTokens, rest) = Utils.firstSlice (fn (Keyword x) => List.exists (fn (y, _) => x = y) Keywords.clauseKeywords | _ => false) btks
      in
        (BC_DEFINITIONS defTokens) :: (pClauses rest)
      end
    | pClauses _ = raise ParseError "unknown clause keyword"
  and
      (* SETS節をパースする関数 *)
      (* BToken list -> BType list * BToken list *)
      pSets [] = ([], [])
    | pSets ((Var x) :: (Keyword "=") :: (Keyword "{") :: btks) =
      let
        fun setsEnumElements ((Var xx) :: (Keyword "}") :: rr) = ([xx], rr)
          | setsEnumElements ((Var xx) :: (Keyword ",") :: rr) =
            let
              val (enext, rnext) = setsEnumElements rr
            in
              (xx :: enext, rnext)
            end
          | setsEnumElements _ = raise ParseError "parse error in enumset in SETS"
        val (e, r) = setsEnumElements btks
        val (next, rest) = pSets r
      in
        ((BT_Enum (x, e)) :: next, rest)
      end
    | pSets ((Var x) :: btks) =
      let
        val (next, rest) = pSets btks
      in
        ((BT_Deferred x) :: next, rest)
      end
    | pSets ((Keyword ";") :: rest) = pSets rest
    | pSets rest = ([], rest)
  and
      (* OPERATIONS節をパースする関数 *)
      (* BToken list -> BOperation list * BToken list *)
      pOperations [] = ([], [])
    (* 操作間のセミコロンは飛ばす *)
    | pOperations ((Keyword ";") :: btks) = pOperations btks
    (* outputなし、inputなし *)
    | pOperations ((Var x) :: (Keyword "=") :: btks) =
      let
        val (s, r) = pSubstitutionSimple btks
        val (next, rest) = pOperations r
      in
        (((BOp (x, [], [], s)) :: next), rest)
      end
    (* output複数 *)
    | pOperations ((Var x) :: (Keyword ",") :: btks) =
      let
        val ((BOp (n, oo, i, s) :: ops), rest) = pOperations btks
      in
        (((BOp (n, (Var x) :: oo, i, s)) :: ops), rest)
      end
    (* output1個 *)
    | pOperations ((Var x) :: (Keyword "<--") :: btks) =
      let
        val ((BOp (n, _, i, s) :: ops), rest) = pOperations btks
      in
        (((BOp (n, [Var x], i, s)) :: ops), rest)
      end
    (* outputなし、inputあり *)
    | pOperations ((Var x) :: (Keyword "(") :: btks) =
      let
        fun inputParameters ((Var y) :: (Keyword ")") :: (Keyword "=") :: rr) = ([Var y], rr)
          | inputParameters ((Var y) :: (Keyword ",") :: rr) =
            let
              val (ee, rrr) = inputParameters rr
            in
              ((Var y) :: ee, rrr)
            end
          | inputParameters _ = raise ParseError "failed to parse OPERATION header"
        val (e, rs) = inputParameters btks
        val (s, r) = pSubstitutionSimple rs
        val (next, rest) = pOperations r
      in
        ((BOp (x, [], e, s) :: next), rest)
      end
    | pOperations btks = ([], btks)
  and
      (* 識別子がコンマ区切りで並んでいる箇所のパース *)
      (* BToken list -> BToken list * BToken list *)
      pVarList [] = ([], [])
    | pVarList ((Var x) :: btks) =
      let
        val (next, rest) = pVarList btks
      in
        ((Var x) :: next, rest)
      end
    | pVarList ((Keyword ",") :: btks) = pVarList btks
    | pVarList btks = ([], btks)
  and
      (* INCLUDES系 他モデルのインスタンス化がコンマ区切りで並んでいる箇所のパース *)
      (* BToken list -> BMchInstanciation list * BToken list *)
      pMachineInstanciationList [] = ([], [])
    | pMachineInstanciationList ((Keyword ",") :: btokens) = pMachineInstanciationList btokens
    | pMachineInstanciationList ((Var x) :: (Keyword "(") :: btokens) =
      let
        val (ex1, rest1) = getNextEe 115 btokens
        fun paramlist ((Keyword ",") :: btks) =
            let
              val (e, r) = getNextEe 115 btks
              val (es, rr) = paramlist r
            in
              (e :: es, rr)
            end
          | paramlist ((Keyword ")") :: btks) = ([], btks)
          | paramlist _ = raise ParseError ""
        val (exs, rest2) = paramlist rest1
        val mc = BMchInst (Var x, ex1 :: exs)
        val (next, rest) = pMachineInstanciationList rest2
      in
        (mc :: next, rest)
      end
    | pMachineInstanciationList ((Var x) :: btokens) =
      let
        val (next, rest) = pMachineInstanciationList btokens
      in
        ((BMchInst (Var x, [])) :: next, rest)
      end
    | pMachineInstanciationList btokens = ([], btokens)
  and
      (* 同時代入のパース *)
      (* BToken list -> BSubstitution * BToken list *)
      pSubstitution [] = raise ParseError "missing Substitution"
    | pSubstitution btokens =
      let
        val separator = ref (Keyword "")
        fun pSubstitutionAux btks =
            let
              val (s, r) = pSubstitutionSimple btks
            in
              if
                r <> [] andalso (hd r = Keyword "||" orelse hd r = Keyword ";")
              then
                let
                  val (ss, rr) = pSubstitutionAux (tl r)
                in
                  separator := hd r ; (s :: ss, rr)
                end
              else
                ([s], r)
            end
        fun flatten []                          = []
          | flatten ((BS_Simultaneous x) :: xs) = x @  (flatten xs)
          | flatten ((BS_Sequencing x)   :: xs) = x @  (flatten xs)
          | flatten (x                   :: xs) = x :: (flatten xs)
        val (subs, rest)                        = pSubstitutionAux btokens
      in
        if
          List.length subs = 1
        then
          (hd subs, rest)
        else
          case !separator of
            (Keyword "||") => (BS_Simultaneous (Utils.repeatApply flatten subs), rest)
          | (Keyword ";")  => (BS_Sequencing   (Utils.repeatApply flatten subs), rest)
          | _              => raise ParseError "invalid substitution separator"
      end
  and
      (* 同時代入以外の代入文のパース *)
      (* BToken list -> BSubstitution * BToken list *)
      pSubstitutionSimple ((Keyword "BEGIN") :: btokens) =
      let
        val (s, r) = pSubstitution btokens
      in
        if
          r = []
        then
          raise ParseError "missing END of BEGIN"
        else
          if hd r = Keyword "END" then
            (BS_Block s, tl r)
          else
            raise ParseError "missing END of BEGIN"
      end
    | pSubstitutionSimple ((Keyword "skip") :: rest) = (BS_Identity, rest)
    | pSubstitutionSimple ((Keyword "PRE") :: rest) =
      let
        val (p, r) = pPredicate rest
        val (s, rr) = pSubstitution (tl r)
      in
        if rr <> [] andalso hd rr = Keyword "END" then
          (BS_Precondition (p, s), tl rr)
        else
          raise ParseError "missing END of PRE"
      end
    | pSubstitutionSimple ((Keyword "ASSERT") :: btokens) =
      let
        val (p, r) = pPredicate btokens
        val (s, rr) = pSubstitution (tl r)
      in
        if r <> [] andalso hd r = Keyword "END" then
          (BS_Assertion (p, s), tl r)
        else
          raise ParseError "missing END of ASSERT"
      end
    | pSubstitutionSimple ((Keyword "CHOICE") :: btokens) =
      let
        val (s1, r1) = pSubstitution btokens
        fun
          choicesublist ((Keyword "OR") :: btks) =
            let
              val (s, r) = pSubstitution btks
              val (ss, rr) = choicesublist r
            in
              ((s :: ss), rr)
            end
          | choicesublist ((Keyword "END") :: btks) = ([], btks)
          | choicesublist _ = raise ParseError "missing END of CHOICE"
        val (s2, r2) = choicesublist r1
      in
        (BS_Choice (s1 :: s2), r2)
      end
    | pSubstitutionSimple ((Keyword "IF") :: btokens) =
      let
        fun
          substitutionIfAux ((Keyword "IF") :: rest) = substitutionIfAux ((Keyword "ELSIF") :: rest)
          | substitutionIfAux ((Keyword "ELSIF") :: rest) =
            let
              val (p, ((Keyword "THEN") :: r)) = pPredicate rest
              val (s, rr) = pSubstitution r
              val (nextbranch, rrr) = substitutionIfAux rr
            in
              (((SOME p, s) :: nextbranch), rrr)
            end
          | substitutionIfAux ((Keyword "ELSE") :: rest) =
            let
              val (s, rr) = pSubstitution rest
              val (nextbranch, rrr) = substitutionIfAux rr
            in
              (((NONE, s) :: nextbranch), rrr)
            end
          | substitutionIfAux ((Keyword "END") :: rest) = ([], rest)
          | substitutionIfAux _ = raise ParseError "parse error in IF"
        val (ifBranches, restTokens) = substitutionIfAux ((Keyword "IF") :: btokens)
      in
        ((BS_If ifBranches), restTokens)
      end
    | pSubstitutionSimple ((Keyword "ANY") :: btokens) =
      let
        val (lvs, r) = pVarList btokens
        val (p, rr)  = pPredicate (tl r)
        val (s, rrr) = pSubstitution (tl rr)
      in
        if rrr <> [] andalso hd rrr = Keyword "END" then
          (BS_Any (lvs, p, s), tl rrr)
        else
          raise ParseError "missing END of ANY"
      end
    | pSubstitutionSimple ((Keyword "LET") :: btokens) =
      let
        val (_, rest) = Utils.firstSlice (Utils.eqto (Keyword "BE")) btokens
        (* LET～BEは要らないので捨てる *)
        val (BP eqs, r) = pPredicate (tl rest)
        fun makeLocalVarTable (BE_Node2 (_, Keyword "=", BE_Leaf (_, var), e)) = [(var, e)]
          | makeLocalVarTable (BE_Node2 (_, Keyword "&", e1, e2)) = (makeLocalVarTable e1) @ (makeLocalVarTable e2)
          | makeLocalVarTable _ = raise ParseError "invalid LET var definition"
        val p = makeLocalVarTable eqs
        val (s, rr) = pSubstitution (tl r)
      in
        if rr <> [] andalso hd rr = Keyword "END" then
          (BS_Let (p, s), tl rr)
        else
          raise ParseError "missing END of LET"
      end
    | pSubstitutionSimple ((Var x) :: restTokens) =
      let
        fun lvarList ((Var y) :: (Keyword "(") :: r) =
            let
              fun
                lvarFpara ((Keyword "(") :: rr) =
                  let
                    val (ex, rrr) = pExpr rr
                  in
                    if (hd rrr) = (Keyword ")") then
                      let
                        val (lfps, rrrr) = lvarFpara (tl rrr)
                      in
                        (ex :: lfps, rrrr)
                      end
                    else
                      raise ParseError "missing RIGHT BRACKET"
                  end
                | lvarFpara rr = ([], rr)
              fun
                lvarFtree f [] = f
                | lvarFtree f (e :: es) = lvarFtree (BE_Fnc (NONE, f, e)) es
              val (fps1, fps2) = lvarFpara ((Keyword "(") :: r)
              val (res1, res2) = lvarList fps2
            in
              ((lvarFtree (BE_Leaf (NONE, Var y)) fps1) :: res1, res2)
            end
          | lvarList (recordtokens as ((Var y) :: (Keyword "AccessRecordField") :: btokens)) =
            let
              fun
                lvarRfield ((Var z) :: (Keyword "AccessRecordField") :: rr) =
                  let
                    val (flst, rrr) = lvarRfield rr
                  in
                    (z :: flst, rrr)
                  end
                | lvarRfield ((Var z) :: rr) = ([z], rr)
                | lvarRfield rr = raise ParseError "missing record field identifier"
              fun
                lvarRtree rf [] = rf
                | lvarRtree rf (e :: es) = lvarRtree (BE_RcAc (NONE, rf, e)) es
              val (rfs, r1) = lvarRfield recordtokens
              val (res, r2) = lvarList r1
            in
              ((lvarRtree (BE_Leaf (NONE, Var (hd rfs))) (tl rfs)) :: res, r2)
            end
          | lvarList (Keyword "," :: r) = lvarList r
          | lvarList ((Var y) :: r) =
            let
              val (lvs, rr) = lvarList r
            in
              ((BE_Leaf (NONE, Var y)) :: lvs, rr)
            end
          | lvarList r = ([], r)
        val (lvars, rest) = lvarList ((Var x) :: restTokens)
        fun lrvar lvs ((Keyword ":") :: (Keyword "(") :: btks) =
            let
              val (p, r) = pPredicate btks
            in
              if (hd r) = (Keyword ")") then
                (BS_BecomesSuchThat (lvars, p), tl r)
              else
                raise ParseError "missing RIGHT BRACKET"
            end
          | lrvar lvs ((Keyword ":=") :: btks) =
            let
              fun rvarList (bts as (z :: zs)) = (* コンマで繋がれた右辺のリスト化 *)
                  let
                    val (rextree, rr) = pEeleft 30 bts
                    fun listingRex (BE_Node2 (_, Keyword ",", e1, e2)) = (listingRex e1) @ [e2]
                      | listingRex e = [e]
                  in
                    (listingRex rextree, rr)
                  end
                | rvarList [] = raise ParseError "missing Rhs of substitution"
              val (rvs, r) = rvarList btks
            in
              case lvs of
                [e] => (BS_BecomesEqual     (e  , hd rvs), r)
              | _   => (BS_BecomesEqualList (lvs, rvs   ), r)
            end
          | lrvar lvs ((Keyword "::") :: btks) =
            let
              val (rex, r) = pEeleft 30 btks
            in
              (BS_BecomesElt (lvs, rex), r)
            end
          | lrvar lvs ((Keyword "<--") :: (Var y) :: (Keyword "(") :: btks) =
            let
              val (extree, r) = pExpr btks
              fun listingInputs (BE_Node2 (_, Keyword ",", e1, e2)) = (listingInputs e1) @ [e2]
                | listingInputs e = [e]
            in
              if (hd r) = (Keyword ")") then
                (BS_Call (Var y, lvs, listingInputs extree), tl r)
              else
                raise ParseError "missing RIGHT BRACKET"
            end
          | lrvar lvs ((Keyword "<--") :: (Var y) :: btks) = (BS_Call (Var y, lvs, []), btks)
          | lrvar lvs ((Keyword "<--") :: rest) = raise ParseError "invalid operation calling"
          | lrvar [(BE_Fnc (_, BE_Leaf (_, x), ex))] btks =
          let
            fun listingRex (BE_Node2 (_, Keyword ",", e1, e2)) = (listingRex e1) @ [e2]
              | listingRex e = [e]
          in
            (BS_Call (x, [], listingRex ex), btks)
          end
          | lrvar [BE_Leaf (_, x)] btks = (BS_Call (x, [], []), btks)
          | lrvar _ _ = raise ParseError "invalid substitution operator" (* DEFINITIONS節で利用する *)
      in
        lrvar lvars rest
      end
    | pSubstitutionSimple ((Keyword "SELECT") :: btokens) =
      let
        fun
          substitutionSelectAux ((Keyword "SELECT") :: rest) = substitutionSelectAux ((Keyword "WHEN") :: rest)
          | substitutionSelectAux ((Keyword "WHEN") :: rest) =
            let
              val (p, ((Keyword "THEN") :: r)) = pPredicate rest
              val (s, rr) = pSubstitution r
              val (nextbranch, rrr) = substitutionSelectAux rr
            in
              (((SOME p, s) :: nextbranch), rrr)
            end
          | substitutionSelectAux ((Keyword "ELSE") :: rest) =
            let
              val (s, rr) = pSubstitution rest
              val (nextbranch, rrr) = substitutionSelectAux rr
            in
              (((NONE, s) :: nextbranch), rrr)
            end
          | substitutionSelectAux ((Keyword "END") :: rest) = ([], rest)
          | substitutionSelectAux _ = raise ParseError "parse error in SELECT"
        val (selectBranches, restTokens) = substitutionSelectAux ((Keyword "SELECT") :: btokens)
      in
        ((BS_Select selectBranches), restTokens)
      end
    | pSubstitutionSimple ((Keyword "CASE") :: btokens) =
      let
        val (e, ((Keyword "OF") :: r1)) = pExpr btokens
        fun simpleTermList ((Keyword "THEN") :: r) = ([], r)
          | simpleTermList ((Keyword ",") :: r) = simpleTermList r
          | simpleTermList ((Keyword "-") :: r) =
            let
              val (stl, rr) = simpleTermList r
            in
              (
              case stl of
                [] => raise ParseError "CASE list ends with \"-\""
              | (x :: xs) => ((BE_Node1 (NONE, Keyword "-", x)) :: xs, rr)
              )
            end
          | simpleTermList (stx :: r) =
            let
              val (res1, res2) = simpleTermList r
            in
              ((BE_Leaf (NONE, stx)) :: res1, res2)
            end
          | simpleTermList [] = raise ParseError "missing THEN of CASE"
        fun substitutionCaseAux ((Keyword "EITHER") :: r) = substitutionCaseAux ((Keyword "OR") :: r)
          | substitutionCaseAux ((Keyword "OR") :: r) =
            let
              val (stl,   rr)   = simpleTermList      r
              val (ss,    rrr)  = pSubstitution       rr
              val (ncase, rrrr) = substitutionCaseAux rrr
            in
              (((stl, ss) :: ncase), rrrr)
            end
          | substitutionCaseAux ((Keyword "ELSE") :: r) =
            let
              val (ss,    rr)  = pSubstitution r
              val (ncase, rrr) = substitutionCaseAux rr
            in
              ((([], ss) :: ncase), rrr)
            end
          | substitutionCaseAux ((Keyword "END") :: (Keyword "END") :: r) = ([], r)
          | substitutionCaseAux _ = raise ParseError "missing END of CASE"
        val (caseResult1, caseResult2) = substitutionCaseAux r1
      in
        (BS_Case (e, caseResult1), caseResult2)
      end
    | pSubstitutionSimple ((Keyword "VAR") :: btokens) =
      let
        val (lvs, r)  = pVarList      btokens
        val (s,   rr) = pSubstitution (tl r)
      in
        if rr <> [] andalso hd rr = Keyword "END" then
          (BS_LocalVariable (lvs, s), tl rr)
        else
          raise ParseError "missing END of VAR"
      end
    | pSubstitutionSimple ((Keyword "WHILE") :: btokens) =
      let
        val (p1, r)    = pPredicate    btokens
        val (s,  rr)   = pSubstitution (tl r)
        val (p2, rrr)  = pPredicate    (tl rr)
        val (e,  rrrr) = pExpr         (tl rrr)
      in
        if rrrr <> [] andalso hd rrrr = Keyword "END" then
          (BS_While (p1, s, p2, e), tl rrrr)
        else
          raise ParseError "missing END of WHILE"
      end
    | pSubstitutionSimple _ = raise ParseError "failed to parse substitution"
  and
      (* 式のパース *)
      (* pExpr BToken list -> BExpr * BToken list *)
      pExpr [] = raise ParseError "missing Expression"
    | pExpr btokens = pEeleft 20 btokens
  and
      (* 優先順位とトークン列を受け取り、
         左結合演算式としてのパース結果と残りのトークン列を返す関数 *)
      (* int -> BToken list -> BExpr * BToken list *)
      pEeleft _ [] = raise ParseError "missing Expression"
    | pEeleft pri btokens =
      let
        val oplst = List.map (fn (x, _, _) => Keyword x) (List.filter (fn (_, x, _) => x = pri) Priority.exprOperators)
        val pnext = getNextEe pri
        fun eeleftSubLst [] = ([], [])
          | eeleftSubLst (opleft :: btks) =
            if
              List.exists (Utils.eqto opleft) oplst
            then
              let
                val (ee, rr) = pnext btks
                val (nexte, rrr) = eeleftSubLst rr
              in
                ((opleft, ee) :: nexte, rrr)
              end
            else
              ([], (opleft :: btks))
        fun eeleftSubTree e1 ((opleft, e2) :: roe) = eeleftSubTree (BE_Node2 (NONE, opleft, e1, e2)) roe
          | eeleftSubTree e1 [] = e1
        val (firstexpr, rest1) = pnext btokens
        val (exprs, rest2) = eeleftSubLst rest1
      in
        (eeleftSubTree firstexpr exprs, rest2)
      end
  and
      (* 優先順位とトークン列を受け取り、
         右結合演算式としてのパース結果と残りのトークン列を返す関数 *)
      (* int -> BToken list -> BExpr * BToken list *)
      pEeright pri [] = raise ParseError "missing expresspion"
    | pEeright pri btokens =
      let
        val oplst = List.map (fn (x, _, _) => Keyword x) (List.filter (fn (_, x, _) => x = pri) Priority.exprOperators)
        val pnext = getNextEe pri
        val (firstexpr, rest1) = pnext btokens
      in
        if rest1 = [] orelse (not (List.exists (Utils.eqto (hd rest1)) oplst)) then
          (firstexpr, rest1)
        else
          let
            val (opright :: rest) = rest1
            val (exprs, rest2) = pEeright pri rest
          in
            ((BE_Node2 (NONE, opright, firstexpr, exprs)), rest2)
          end
      end
  and
      (* 式内の関数様の部分のパース *)
      (* BToken list -> BExpr * BToken list *)
      pFuncs btokens =
      let
        datatype P_FUNCS_DATA = PF_Evl of BExpr | PF_Img of BExpr | PF_Rvs
        val (funcexpr, rest1) = pRecordaccess btokens
        fun
          funcsSubLst ((Keyword "(") :: btks) =
            let
              val (e, r) = pExpr btks
            in
              if r = [] orelse (hd r) <> (Keyword ")") then
                raise ParseError "missing RIGHT BRACKET of function parameter"
              else
                let
                  val (elst, rr) = funcsSubLst (tl r)
                in
                  ((PF_Evl e) :: elst, rr)
                end
            end
          | funcsSubLst ((Keyword "[") :: btks) =
            let
              val (e, r) = pExpr btks
            in
              if r = [] orelse (hd r) <> (Keyword "]") then
                raise ParseError "missing \"]\" of function image"
              else
                let
                  val (elst, rr) = funcsSubLst (tl r)
                in
                  ((PF_Img e) :: elst, rr)
                end
            end
          | funcsSubLst ((Keyword "~") :: btks) =
            let
              val (elst, r) = funcsSubLst btks
            in
              (PF_Rvs :: elst, r)
            end
          | funcsSubLst x = ([], x)
        fun funcsSubTree f [] = f
          | funcsSubTree f ((PF_Evl e) :: es) = funcsSubTree (BE_Fnc   (NONE, f,           e)) es
          | funcsSubTree f ((PF_Img e) :: es) = funcsSubTree (BE_Img   (NONE, f,           e)) es
          | funcsSubTree f (PF_Rvs     :: es) = funcsSubTree (BE_Node1 (NONE, Keyword "~", f)) es
        val (paramlst, rest2) = funcsSubLst rest1
      in
        (funcsSubTree funcexpr paramlst, rest2)
      end
  and
      (* 単項マイナス - x をパース *)
      (* BToken list -> BExpr * BToken list *)
      pUminus ((Keyword "-") :: btokens) =
      let
        val (ex, rest) = (getNextEe 210) btokens
      in
        (BE_Node1 (NONE, (Keyword "-"), ex), rest)
      end
    | pUminus btokens = (getNextEe 210) btokens
  and
      (* レコードのフィールドへのアクセスの式 x ' y をパース *)
      (* BToken list -> BToken list *)
      pRecordaccess [] = raise ParseError "missing Expression"
    | pRecordaccess btokens =
      let
        val pnext = getNextEe 250
        fun raSubLst ((Keyword "'") :: (Var x) :: btks) =
            let
              val (nextx, rr) = raSubLst btks
            in
              (x :: nextx, rr)
            end
          | raSubLst btks = ([], btks)
        fun raSubTree e (x :: xs) = raSubTree (BE_RcAc (NONE, e, x)) xs
          | raSubTree e [] = e
        val (firstexpr, rest1) = pnext btokens
        val (ss, rest2) = raSubLst rest1
      in
        (raSubTree firstexpr ss, rest2)
      end
  and
      (* 式の構文木の末端、または括弧で囲まれた式をパース *)
      (* BToken list -> BExpr * BToken list *)
      pPrimary ((Keyword "(") :: btokens) =
      let
        val (brexpr, rest) = pExpr btokens
      in
        if rest = [] orelse (hd rest) <> (Keyword ")") then
          raise ParseError "missing RIGHT BRACKET"
        else
          (brexpr, tl rest)
      end
    | pPrimary ((Var x) ::              btokens) = (BE_Leaf (NONE,                                                     Var x),              btokens)
    | pPrimary ((IntegerLiteral x) ::   btokens) = (BE_Leaf (SOME BT_Integer,                                          IntegerLiteral x),   btokens)
    | pPrimary ((Keyword "MAXINT") ::   btokens) = (BE_Leaf (SOME BT_Integer,                                          Keyword "MAXINT"),   btokens)
    | pPrimary ((Keyword "MININT") ::   btokens) = (BE_Leaf (SOME BT_Integer,                                          Keyword "MININT"),   btokens)
    | pPrimary ((Keyword "INTEGER") ::  btokens) = (BE_Leaf (SOME (BT_Power (SOME BT_Integer)),                        Keyword "INTEGER"),  btokens)
    | pPrimary ((Keyword "NATURAL") ::  btokens) = (BE_Leaf (SOME (BT_Power (SOME BT_Integer)),                        Keyword "NATURAL"),  btokens)
    | pPrimary ((Keyword "NATURAL1") :: btokens) = (BE_Leaf (SOME (BT_Power (SOME BT_Integer)),                        Keyword "NATURAL1"), btokens)
    | pPrimary ((Keyword "INT") ::      btokens) = (BE_Leaf (SOME (BT_Power (SOME BT_Integer)),                        Keyword "INT"),      btokens)
    | pPrimary ((Keyword "NAT") ::      btokens) = (BE_Leaf (SOME (BT_Power (SOME BT_Integer)),                        Keyword "NAT"),      btokens)
    | pPrimary ((Keyword "NAT1") ::     btokens) = (BE_Leaf (SOME (BT_Power (SOME BT_Integer)),                        Keyword "NAT1"),     btokens)
    | pPrimary ((StringLiteral x) ::    btokens) = (BE_Leaf (SOME BT_String,                                           StringLiteral x),    btokens)
    | pPrimary ((Keyword "STRING") ::   btokens) = (BE_Leaf (SOME (BT_Power (SOME BT_String)),                         Keyword "STRING"),   btokens)
    | pPrimary ((RealLiteral x) ::      btokens) = (BE_Leaf (SOME BT_Real,                                             RealLiteral x),      btokens)
    | pPrimary ((Keyword "REAL") ::     btokens) = (BE_Leaf (SOME (BT_Power (SOME BT_Real)),                           Keyword "REAL"),     btokens)
    | pPrimary ((Keyword "FLOAT") ::    btokens) = (BE_Leaf (SOME (BT_Power (SOME BT_Real)),                           Keyword "FLOAT"),    btokens)
    | pPrimary ((Keyword "TRUE") ::     btokens) = (BE_Leaf (SOME BT_Bool,                                             Keyword "TRUE"),     btokens)
    | pPrimary ((Keyword "FALSE") ::    btokens) = (BE_Leaf (SOME BT_Bool,                                             Keyword "FALSE"),    btokens)
    | pPrimary ((Keyword "BOOL") ::     btokens) = (BE_Leaf (SOME (BT_Power (SOME BT_Bool)),                           Keyword "BOOL"),     btokens)
    | pPrimary ((Keyword "btrue") ::    btokens) = (BE_Leaf (SOME BT_Predicate,                                        Keyword "btrue"),    btokens)
    | pPrimary ((Keyword "bfalse") ::   btokens) = (BE_Leaf (SOME BT_Predicate,                                        Keyword "bfalse"),   btokens)
    | pPrimary ((Keyword "{}") ::       btokens) = (BE_Leaf (SOME (BT_Power NONE),                                     Keyword "{}"),       btokens)
    | pPrimary ((Keyword "[]") ::       btokens) = (BE_Leaf (SOME (BT_Power (SOME (BT_Pair (SOME BT_Integer, NONE)))), Keyword "[]"),       btokens)
    | pPrimary ((Keyword "{") ::        btokens) =
      let
        val (expr, rest1) = pExpr btokens
        fun listingElements (BE_Node2 (_, (Keyword ","), e1, e2)) = (listingElements e1) @ [e2]
          | listingElements e = [e]
      in
        case rest1 of
          ((Keyword "}") :: rest2) => (BE_ExSet (NONE, listingElements expr), rest2)
        | ((Keyword "|") :: rest2) =>
          let
            val (p, rest3) = pPredicate rest2
          in
            if rest3 = [] orelse (hd rest3) <> (Keyword "}") then
              raise ParseError "missing \"}\" of set"
            else
              (BE_InSet (NONE, List.map (fn (BE_Leaf (_, v)) => v | _ => raise ParseError "") (listingElements expr), p), tl rest3)
          end
        | _ => raise ParseError "missing \"}\" of set"
      end
    | pPrimary ((Keyword "[") :: btokens) =
      let
        val (expr, rest) = pExpr btokens
        fun listingElements (BE_Node2 (_, (Keyword ","), e1, e2)) = (listingElements e1) @ [e2]
          | listingElements e = [e]
      in
        if rest = [] orelse (hd rest) <> (Keyword "]") then
          raise ParseError "missing \"]\" of seq"
        else
          (BE_Seq (NONE, listingElements expr), tl rest)
      end
    | pPrimary ((Keyword "!") :: (Var x) :: (Keyword ".") :: (Keyword "(") :: btokens) =
      let
        val (allp, rest) = pPredicate btokens
      in
        case allp of
          (BP (BE_Node2 (_, Keyword "=>", p1, p2))) =>
            if rest = [] orelse (hd rest) <> (Keyword ")") then
               raise ParseError "missing RIGHT BRACKET in Predicate of \"!\""
            else
              (BE_ForAll ([Var x], BP p1, BP p2), tl rest)
        | _ => raise ParseError "\"=>\" is not used in Predicate of \"!\""
      end
    | pPrimary ((Keyword "!") :: (Keyword "(") :: (Var x) :: btokens) =
      let
        fun bindExprList ((Keyword ",") :: (Var y) :: r) =
            let
              val (lst, rr) = bindExprList r
            in
              ((Var y) :: lst, rr)
            end
          | bindExprList ((Keyword ")") :: (Keyword ".") :: (Keyword "(") :: r) = ([], r)
          | bindExprList _ = raise ParseError "failed to parse binding of \"!\""
        val (exls, rest1) = bindExprList btokens
        val (allp, rest2) = pPredicate rest1
      in
        case allp of
          (BP (BE_Node2 (_, Keyword "=>", p1, p2))) =>
            if rest2 = [] orelse (hd rest2) <> (Keyword ")") then
              raise ParseError "missing RIGHT BRACKET of Predicate of \"!\""
            else
              (BE_ForAll (((Var x) :: exls), BP p1, BP p2), tl rest2)
        | _ => raise ParseError "\"=>\" is not used in Predicate of \"!\""
      end
    | pPrimary ((Keyword "!") ::  _) =
      raise ParseError "failed to parse contents of \"!\""

    | pPrimary ((Keyword "#") :: (Var x) :: (Keyword ".") :: (Keyword "(") :: btokens) =
      let
        val (allp, rest) = pPredicate btokens
      in
        if rest = [] orelse (hd rest) <> (Keyword ")") then
          raise ParseError "missing RIGHT BRACKET in Predicate of \"#\""
        else
          (BE_Exists ([Var x], allp), tl rest)
      end
    | pPrimary ((Keyword "#") :: (Keyword "(") :: (Var x) :: btokens) =
      let
        fun bindExprList ((Keyword ",") :: (Var y) :: r) =
            let
              val (lst, rr) = bindExprList r
            in
              (((Var y) :: lst), rr)
            end
          | bindExprList ((Keyword ")") :: (Keyword ".") :: (Keyword "(") :: r) = ([], r)
          | bindExprList _ = raise ParseError "failed to parse binding of \"#\""
        val (exls, rest1) = bindExprList btokens
        val (allp, rest2) = pPredicate rest1
      in
        if rest2 = [] orelse (hd rest2) <> (Keyword ")") then
          raise ParseError "missing RIGHT BRACKET of Predicate of \"#\""
        else
          (BE_Exists (((Var x) :: exls), allp), tl rest2)
      end
    | pPrimary ((Keyword "#") ::  _) =
      raise ParseError "failed to parse contents of \"#\""
    | pPrimary (btokens as ((Keyword "%")     ::  _)) = pLambdas btokens
    | pPrimary (btokens as ((Keyword "SIGMA") ::  _)) = pSigmas btokens
    | pPrimary (btokens as ((Keyword "PI")    ::  _)) = pSigmas btokens
    | pPrimary (btokens as ((Keyword "INTER") ::  _)) = pLambdas btokens
    | pPrimary (btokens as ((Keyword "UNION") ::  _)) = pLambdas btokens
    | pPrimary ((Keyword "not") :: (Keyword "not") :: btokens) = (* 二重否定の時は外のnotの括弧は省略可能 *)
      let
        val (ex, rest) = pExpr ((Keyword "not") :: btokens)
      in
        (BE_Node1 ((SOME BT_Predicate), Keyword "not", ex), rest)
      end
    | pPrimary ((Keyword f) :: (Keyword "(") :: btokens) =
      if List.exists (Utils.eqto f) BuiltinFnc.biSimpleFncStr then
        let
          val (ex, rest) = pExpr btokens
        in
          if rest = [] orelse (hd rest) <> (Keyword ")") then
            raise ParseError ("missing RIGHT BRACKET of " ^ f)
          else
            (BE_Node1 (NONE, Keyword f, ex), tl rest)
        end
      else
        if List.exists (Utils.eqto f) BuiltinFnc.bi2FncStr then
          let
            val (eall, rest) = pExpr btokens
          in
            if rest = [] orelse (hd rest) <> (Keyword ")") then
              raise ParseError ("missing RIGHT BRACKET of " ^ f)
            else
              case eall of
                BE_Node2 (_, Keyword ",", e1, e2) => (BE_Node2 (NONE, (Keyword f), e1, e2), tl rest)
              | _ => raise ParseError ("invalid parameter of " ^ f)
          end
        else
          let
            fun listingExprs btks =
                let
                  val (e, r1) = (getNextEe 115) btks
                  fun lceAux ((Keyword ")") :: bt) = ([], bt)
                    | lceAux ((Keyword ",") :: bt) =
                      let
                        val (ee, rr) = (getNextEe 115) bt
                        val (ees, rrr) = lceAux rr
                      in
                        (ee :: ees, rrr)
                      end
                    | lceAux _ = raise ParseError "failed to parse comma-separated expressions"
                  val (es, r2) = lceAux r1
                in
                  (e :: es, r2)
                end
          in
            (case f of
                "son" =>
                  let
                    val (exs, rest) = listingExprs btokens
                  in
                    if length exs = 3 then
                      (BE_NodeN (NONE, Keyword "son", exs), rest)
                    else
                      raise ParseError "invalid number of \"son()\" parameter"
                  end
              | "bin" =>
                let
                  val (exs, rest) = listingExprs btokens
                in
                  if length exs = 1 orelse length exs = 3 then
                    (BE_NodeN (NONE, Keyword "bin", exs), rest)
                  else
                    raise ParseError "invalid number of \"bin()\" parameter"
                end
              | "struct" =>
                (case btokens of
                    ((Var x) :: (Keyword ":") :: btks) =>
                      let
                        fun pStructAux ((Keyword ",") :: (Var y) :: (Keyword ":") :: bt) =
                            let
                              val (ee, r1) = (getNextEe 115) bt
                              val (pps, r2) = pStructAux r1
                            in
                              ((y, ee) :: pps, r2)
                            end
                          | pStructAux ((Keyword ")") :: bt) = ([], bt)
                          | pStructAux _ = raise ParseError "failed to parse \"struct\" contents"
                        val (e, rest1) = (getNextEe 115) btks
                        val (ps, rest2) = pStructAux rest1
                      in
                        (BE_Struct (NONE, (x, e) :: ps), rest2)
                      end
                  | _ => raise ParseError "invalid \"struct\" contents")
              | "rec" =>
                let
                  fun pRecAux ((Keyword ",") :: (Var y) :: (Keyword ":") :: bt) =
                      let
                        val (ee, r1) = (getNextEe 115) bt
                        val (pps, r2) = pRecAux r1
                      in
                        ((SOME y, ee) :: pps, r2)
                      end
                    | pRecAux ((Keyword ")") :: bt) = ([], bt)
                    | pRecAux bt =
                      let
                        val (ee, r1) = (getNextEe 115) bt
                        val (pps, r2) = pRecAux r1
                      in
                        ((NONE, ee) :: pps, r2)
                      end
                in
                  (case btokens of
                      ((Var x) :: (Keyword ":") :: btks) =>
                        let
                          val (e, rest1) = (getNextEe 115) btks
                          val (ps, rest2) = pRecAux rest1
                        in
                          (BE_Rec (NONE, (SOME x, e) :: ps), rest2)
                        end
                    | btks =>
                      let
                        val (e, rest1) = (getNextEe 115) btks
                        val (ps, rest2) = pRecAux rest1
                      in
                        (BE_Rec (NONE, (NONE, e) :: ps), rest2)
                      end
                  )
                end
              | _ => raise ParseError "unknown reserved token")
          end
    | pPrimary _ = raise ParseError "failed to parse a primary expression"
  and
      pSigmas (kw :: (Keyword "(") :: (Var x) :: (Keyword ")") :: btokens) = pSigmas (kw :: (Var x) :: btokens)
    | pSigmas (kw :: (Var x) :: (Keyword ".") :: (Keyword "(") :: btokens) =
      let
        val (p, rest1) = pPredicate btokens
      in
        if rest1 = [] orelse (hd rest1) <> (Keyword "|") then
          raise ParseError "missing \"|\""
        else
          let
            val (e, rest2) = pExpr (tl rest1)
          in
            if rest2 = [] orelse (hd rest2) <> (Keyword ")") then
              raise ParseError "missing RIGHT BRACKET"
            else
              case kw of
                (Keyword "SIGMA") => (BE_Sigma (NONE, Var x, p, e), tl rest2)
              | (Keyword "PI") => (BE_Pi (NONE, Var x, p, e), tl rest2)
              | _ => raise ParseError ""
          end
      end
    | pSigmas _ = raise ParseError ""
  and
    pLambdas (kw :: (Var x) :: (Keyword ".") :: (Keyword "(") :: btokens) =
      let
        val (p, rest1) = pPredicate btokens
      in
        if rest1 = [] orelse (hd rest1) <> (Keyword "|") then
          raise ParseError "missing \"|\""
        else
          let
            val (e, rest2) = pExpr (tl rest1)
          in
            if rest2 = [] orelse (hd rest2) <> (Keyword ")") then
              raise ParseError "missing RIGHT BRACKET"
            else
              (pLambdas2 kw [Var x] p e, tl rest2)
          end
      end
    | pLambdas (kw :: (Keyword "(") :: (Var x) :: btokens) =
      let
        fun bindExprList ((Keyword ",") :: (Var y) :: r) =
            let
              val (lst, rr) = bindExprList r
            in
              (((Var y) :: lst), rr)
            end
          | bindExprList ((Keyword ")") :: (Keyword ".") :: (Keyword "(") :: r) = ([], r)
          | bindExprList _ = raise ParseError "failed to parse binding"
        val (vls, rest1) = bindExprList btokens
        val (p, rest2) = pPredicate rest1
      in
        if rest2 = [] orelse (hd rest2) <> (Keyword "|") then
          raise ParseError "missing \"|\""
        else
          let
            val es = (Var x) :: vls
            val (e, rest3) = pExpr (tl rest2)
          in
            if rest3 = [] orelse (hd rest3) <> (Keyword ")") then
              raise ParseError "missing RIGHT BRACKET"
            else
              (pLambdas2 kw es p e, tl rest3)
          end
      end
    | pLambdas _ = raise ParseError "failed to parse binding"
  and
    pLambdas2 kw vs p e =
      case kw of
        (Keyword "%")     => BE_Lambda (NONE, vs, p, e)
      | (Keyword "INTER") => BE_Inter  (NONE, vs, p, e)
      | (Keyword "UNION") => BE_Union  (NONE, vs, p, e)
      | _ => raise ParseError "unknown Lambdas"
  and
    (* 優先度を整数として受け取り、次の優先度の式をパースする関数を返す関数 *)
      getNextEe  20 = pEeleft  30
    | getNextEe  30 = pEeleft  40
    | getNextEe  40 = pEeleft  60
    | getNextEe  60 = pEeleft 110
    | getNextEe 110 = pEeleft 115
    | getNextEe 115 = pEeleft 125
    | getNextEe 125 = pEeleft 130
    | getNextEe 130 = pEeleft 160
    | getNextEe 160 = pEeleft 170
    | getNextEe 170 = pEeleft 180
    | getNextEe 180 = pEeleft 190
    | getNextEe 190 = pEeright 200
    | getNextEe 200 = pUminus
    | getNextEe 210 = pFuncs (* ff(xx) と f~ と ff[xx] 全部同じ優先順位 *)
    | getNextEe 230 = pRecordaccess
    | getNextEe 250 = pPrimary
    | getNextEe _ = raise ParseError "unknown priority of operator"
  and
    pPredicate btokens =
    let
      val (expr, rest) = pEeleft 30 btokens
    in
      (BP expr, rest)
    end
(*  and
      rewriteIfTree *)(* TODO *)(* ①IF文を平坦化するか②ELSIFを消すかの2つからどちらの方向性で統一を行うか決める必要がある*)
end
