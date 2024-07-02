structure Show =
struct
  exception ShowError of string

  fun tabs depth = Utils.repeatString "\t" depth

  and
      priOf (BE_Node1 (_, Keyword "~"  , _   )) = (230, Priority.L)
    | priOf (BE_Node1 (_, Keyword "-"  , _   )) = (210, Priority.N)
    | priOf (BE_Node2 (_, Keyword "mod", _, _)) = (190, Priority.L)
    | priOf (BE_Node2 (_, Keyword ":"  , _, _)) = ( 60, Priority.L)
    (*
      これは集合への帰属
      念の為レコードのフィールドの":"と区別する
    *)
    | priOf (BE_Node2 (_, t, _, _))             = priOfT t
    | priOf (BE_Commutative (_, t, _))          = priOfT t
    | priOf (BE_Fnc _)                          = (230, Priority.L)
    | priOf (BE_Img _)                          = (230, Priority.R)
    | priOf (BE_RcAc _)                         = (250, Priority.L)
    | priOf _                                   = (400, Priority.N)

  and
      priOfT (Keyword s) =
      let
        val e = List.find (fn (x, _, _) => x = s) Priority.exprOperators
      in
        case e of
          NONE => (400, Priority.N) (* 組み込み関数 *)
        | SOME (_, pr, rl) => (pr, rl) (* 優先順位と結合規則 *)
      end
    | priOfT _ = raise ShowError "a token should be operator but not"

  and
      showComponent (BMch (mchName,          [],     clauses)) = "MACHINE" ^        "\n\t" ^ mchName ^                                                                "\n\n" ^ (showClauseList clauses) ^ "END\n"
    | showComponent (BMch (mchName,          params, clauses)) = "MACHINE" ^        "\n\t" ^ mchName ^ "(" ^ (showTokenList params) ^ ")" ^                             "\n\n" ^ (showClauseList clauses) ^ "END\n"
    | showComponent (BRef (refName, mchName, [],     clauses)) = "REFINEMENT" ^     "\n\t" ^ refName ^                                    "\nREFINES\n\t" ^ mchName ^ "\n\n" ^ (showClauseList clauses) ^ "END\n"
    | showComponent (BRef (refName, mchName, params, clauses)) = "REFINEMENT" ^     "\n\t" ^ refName ^ "(" ^ (showTokenList params) ^ ")" ^ "\nREFINES\n\t" ^ mchName ^ "\n\n" ^ (showClauseList clauses) ^ "END\n"
    | showComponent (BImp (refName, mchName, [],     clauses)) = "IMPLEMENTATION" ^ "\n\t" ^ refName ^                                    "\nREFINES\n\t" ^ mchName ^ "\n\n" ^ (showClauseList clauses) ^ "END\n"
    | showComponent (BImp (refName, mchName, params, clauses)) = "IMPLEMENTATION" ^ "\n\t" ^ refName ^ "(" ^ (showTokenList params) ^ ")" ^ "\nREFINES\n\t" ^ mchName ^ "\n\n" ^ (showClauseList clauses) ^ "END\n"

  and
      showClauseList clauses =
      let
        val sortedClauses = ListMergeSort.sort (fn (c1, c2) => #2 (valOf (List.find (fn (ss1, _) => clauseToClauseName c1 = ss1) Keywords.clauseKeywords)) >= #2 (valOf (List.find (fn (ss2, _) => clauseToClauseName c2 = ss2) Keywords.clauseKeywords))) clauses
        fun showClauseListAux [] = ""
          | showClauseListAux (x :: xs) = (showClause x) ^ (showClauseListAux xs)
      in
        showClauseListAux sortedClauses
      end

  and
      clauseToClauseName (BC_CONSTRAINTS _)    = "CONSTRAINTS"
    | clauseToClauseName (BC_PROPERTIES _)     = "PROPERTIES"
    | clauseToClauseName (BC_INVARIANT _)      = "INVARIANT"
    | clauseToClauseName (BC_ASSERTIONS _)     = "ASSERTIONS"

    | clauseToClauseName (BC_VALUES _)         = "VALUES"

    | clauseToClauseName (BC_SEES _)           = "SEES"
    | clauseToClauseName (BC_INCLUDES _)       = "INCLUDES"
    | clauseToClauseName (BC_PROMOTES _)       = "PROMOTES"
    | clauseToClauseName (BC_EXTENDS _)        = "EXTENDS"
    | clauseToClauseName (BC_USES _)           = "USES"
    | clauseToClauseName (BC_IMPORTS _)        = "IMPORTS"

    | clauseToClauseName (BC_CCONSTANTS _)     = "CONCRETE_CONSTANTS"
    | clauseToClauseName (BC_ACONSTANTS _)     = "ABSTRACT_CONSTANTS"
    | clauseToClauseName (BC_CVARIABLES _)     = "CONCRETE_VARIABLES"
    | clauseToClauseName (BC_AVARIABLES _)     = "ABSTRACT_VARIABLES"

    | clauseToClauseName (BC_SETS _)           = "SETS"
    | clauseToClauseName (BC_INITIALISATION _) = "INITIALISATION"
    | clauseToClauseName (BC_OPERATIONS _)     = "OPERATIONS"
    | clauseToClauseName (BC_DEFINITIONS _)    = "DEFINITIONS"

  and
      showClause (c as BC_CONSTRAINTS p)    = (clauseToClauseName c) ^ "\n" ^ (showPredicate 1 p) ^ "\n\n"
    | showClause (c as BC_PROPERTIES p)     = (clauseToClauseName c) ^ "\n" ^ (showPredicate 1 p) ^ "\n\n"
    | showClause (c as BC_INVARIANT p)      = (clauseToClauseName c) ^ "\n" ^ (showPredicate 1 p) ^ "\n\n"
    | showClause (c as BC_ASSERTIONS p)     = (clauseToClauseName c) ^ "\n" ^ (showPredicate 1 p) ^ "\n\n"

    | showClause (c as BC_VALUES l)         = (clauseToClauseName c) ^ "\n\t" ^ (Utils.concatWith ";\n\t" (List.map (fn (v, e) => (showToken v) ^ " = " ^ (showExpr e)) l)) ^ "\n\n"

    | showClause (c as BC_SEES l)           = (clauseToClauseName c) ^ "\n" ^ (showMachine l) ^ "\n"
    | showClause (c as BC_INCLUDES l)       = (clauseToClauseName c) ^ "\n" ^ (showMachine l) ^ "\n"
    | showClause (c as BC_PROMOTES l)       = (clauseToClauseName c) ^ "\n" ^ (showMachine l) ^ "\n"
    | showClause (c as BC_EXTENDS l)        = (clauseToClauseName c) ^ "\n" ^ (showMachine l) ^ "\n"
    | showClause (c as BC_USES l)           = (clauseToClauseName c) ^ "\n" ^ (showMachine l) ^ "\n"
    | showClause (c as BC_IMPORTS l)        = (clauseToClauseName c) ^ "\n" ^ (showMachine l) ^ "\n"

    | showClause (c as BC_CCONSTANTS l)     = (clauseToClauseName c) ^ "\n\t" ^ (showTokenList l) ^ "\n\n"
    | showClause (c as BC_ACONSTANTS l)     = (clauseToClauseName c) ^ "\n\t" ^ (showTokenList l) ^ "\n\n"
    | showClause (c as BC_CVARIABLES l)     = (clauseToClauseName c) ^ "\n\t" ^ (showTokenList l) ^ "\n\n"
    | showClause (c as BC_AVARIABLES l)     = (clauseToClauseName c) ^ "\n\t" ^ (showTokenList l) ^ "\n\n"
    | showClause (c as BC_DEFINITIONS l)    = "/*DEFINITIONS CLAUSE EXISTS*/\n" (* 未対応 *)

    | showClause (c as BC_SETS l)           =
      let
        fun setToString (BT_Deferred s) = "[DeferredSet]" ^s
          | setToString (BT_Enum (s, elts)) ="[EnumSet]" ^ s ^ " = {" ^ (Utils.concatWith ", " elts) ^ "}"
          | setToString _ = raise ShowError "unknown type in SETS"
      in
        (clauseToClauseName c) ^ "\n\t" ^ (Utils.concatWith "; " (List.map setToString l)) ^ "\n\n"
      end
    | showClause (c as BC_OPERATIONS l)     = (clauseToClauseName c) ^ "\n" ^ (Utils.concatWith ";\n\n" (List.map showOperation l)) ^ "\n"
    | showClause (c as BC_INITIALISATION s) = (clauseToClauseName c) ^ "\n" ^ (showSubstitution 1 s) ^ "\n\n"

  and
      showOperation (BOp (name, [],      [],     subs)) =
      (tabs 1) ^ name ^ " =\n" ^
      (showTopSubstitution subs)
    | showOperation (BOp (name, [],      inputs, subs)) =
      (tabs 1) ^ name ^ "(" ^ (showTokenList inputs) ^ ") =\n" ^
      (showTopSubstitution subs)
    | showOperation (BOp (name, outputs, [],     subs)) =
      (tabs 1) ^ (showTokenList outputs) ^ " <-- " ^ name ^ " =\n" ^
      (showTopSubstitution subs)
    | showOperation (BOp (name, outputs, inputs, subs)) =
      (tabs 1) ^ (showTokenList outputs) ^ " <-- " ^ name ^ "(" ^ (showTokenList inputs) ^ ") =\n" ^
      (showTopSubstitution subs)

  and
    (* Becomes such that 代入、同時代入、逐次代入、所属代入は操作のトップレベルに置けないためBEGIN ENDで囲む *)
      showTopSubstitution (BS_BecomesSuchThat x) = showSubstitution 2 (BS_Block (BS_BecomesSuchThat x))
    | showTopSubstitution (BS_Sequencing l)      = showSubstitution 2 (BS_Block (BS_Sequencing l))
    | showTopSubstitution (BS_Simultaneous l)    = showSubstitution 2 (BS_Block (BS_Simultaneous l))
    | showTopSubstitution (BS_BecomesElt x)      = showSubstitution 2 (BS_Block (BS_BecomesElt x))
    | showTopSubstitution s                      = showSubstitution 2 s

  and
      showSubstitution n (BS_Block s) =
      (tabs n) ^ "BEGIN\n" ^
      (showSubstitution (n + 1) s) ^ "\n" ^
      (tabs n) ^ "END"
    | showSubstitution n BS_Identity = (tabs n) ^ "skip"
    | showSubstitution n (BS_Precondition (p, s)) =
      (tabs n) ^ "PRE\n" ^
      (showPredicate (n + 1) p) ^ "\n" ^
      (tabs n) ^ "THEN\n" ^
      (showSubstitution (n + 1) s) ^ "\n" ^
      (tabs n) ^ "END"
    | showSubstitution n (BS_Assertion (p, s)) =
      (tabs n) ^ "PRE\n" ^
      (showPredicate (n + 1) p) ^ "\n" ^
      (tabs n) ^ "THEN\n" ^
      (showSubstitution (n + 1) s) ^ "\n" ^
      (tabs n) ^ "END"
    | showSubstitution n (BS_Choice l) =
      let
        fun choiceAux [] = raise ShowError ""
          | choiceAux [s] = (showSubstitution (n + 1) s) ^ "\n"
          | choiceAux (s :: ss) =
            (showSubstitution (n + 1) s) ^ "\n" ^
            (tabs n) ^ "OR\n" ^ (choiceAux ss)
      in
        (tabs n) ^ "CHOICE\n" ^
        (choiceAux l) ^
        (tabs n) ^ "END"
      end
    | showSubstitution n (BS_If ([(SOME p, s)])) =
      (tabs n) ^ "IF\n" ^
      (showPredicate (n + 1) p) ^ "\n" ^
      (tabs n) ^ "THEN\n" ^
      (showSubstitution (n + 1) s) ^ "\n" ^
      (tabs n) ^ "END"
    | showSubstitution n (BS_If ((SOME p, s) :: l)) =
      let
        fun ifAux [(NONE, ss)] =
            (tabs n) ^ "ELSE\n" ^
            (showSubstitution (n + 1) ss) ^ "\n" ^
            (tabs n) ^ "END"
          | ifAux [(SOME pp, ss)] =
            (tabs n) ^ "ELSIF\n" ^
            (showPredicate (n + 1) pp) ^ "\n" ^
            (tabs n) ^ "THEN\n" ^
            (showSubstitution (n + 1) ss) ^ "\n" ^
            (tabs n) ^ "END"
          | ifAux ((SOME pp, ss) :: ll) =
            (tabs n) ^ "ELSIF\n" ^
            (showPredicate (n + 1) pp) ^ "\n" ^
            (tabs n) ^ "THEN\n" ^
            (showSubstitution (n + 1) ss) ^ "\n" ^
            (ifAux ll)
          | ifAux _ = raise ShowError ""
      in
        (tabs n) ^ "IF\n" ^
        (showPredicate (n + 1) p) ^ "\n" ^
        (tabs n) ^ "THEN\n" ^
        (showSubstitution (n + 1) s) ^ "\n" ^
        (ifAux l)
      end
    | showSubstitution _ (BS_If _) = raise ShowError "invalid IF"
    | showSubstitution n (BS_Select ([(SOME p, s)])) =
      (tabs n) ^ "SELECT\n" ^
      (showPredicate (n + 1) p) ^ "\n" ^
      (tabs n) ^ "THEN\n" ^
      (showSubstitution (n + 1) s) ^ "\n" ^
      (tabs n) ^ "END"
    | showSubstitution n (BS_Select ((SOME p, s) :: l)) =
      let
        fun selectAux [(NONE, ss)] =
            (tabs n) ^ "ELSE\n" ^
            (showSubstitution (n + 1) ss) ^ "\n" ^
            (tabs n) ^ "END"
          | selectAux [(SOME pp, ss)] =
            (tabs n) ^ "WHEN\n" ^
            (showPredicate (n + 1) pp) ^ "\n" ^
            (tabs n) ^ "THEN\n" ^
            (showSubstitution (n + 1) ss) ^ "\n" ^
            (tabs n) ^ "END"
          | selectAux ((SOME pp, ss) :: ll) =
            (tabs n) ^ "WHEN\n" ^
            (showPredicate (n + 1) pp) ^ "\n" ^
            (tabs n) ^ "THEN\n" ^
            (showSubstitution (n + 1) ss) ^ "\n" ^
            (selectAux ll)
          | selectAux _ = raise ShowError ""
      in
        (tabs n) ^ "SELECT\n" ^
        (showPredicate (n + 1) p) ^ "\n" ^
        (tabs n) ^ "THEN\n" ^
        (showSubstitution (n + 1) s) ^ "\n" ^
        (selectAux l)
      end
    | showSubstitution _ (BS_Select _) = raise ShowError "invalid IF"
    | showSubstitution n (BS_Case (ex, [(es, s)])) =
      (tabs n) ^ "CASE " ^ (showExpr ex) ^ " OF\n" ^
      (tabs (n + 1)) ^ "EITHER " ^ (showExprListInCase es) ^ " THEN\n" ^
      (showSubstitution (n + 2) s) ^ "\n" ^
      (tabs (n + 1)) ^ "END\n" ^
      (tabs n) ^ "END"
    | showSubstitution n (BS_Case (ex, ((es, s) :: l))) =
      let
        fun caseAux [([], ss)] =
            (tabs (n + 1)) ^ "ELSE\n" ^
            (showSubstitution (n + 2) ss) ^ "\n" ^
            (tabs (n + 1)) ^ "END\n" ^
            (tabs n) ^ "END"
          | caseAux [(ees, ss)] =
            (tabs (n + 1)) ^ "OR " ^ (showExprListInCase ees) ^ " THEN\n" ^
            (showSubstitution (n + 2) ss) ^ "\n" ^
            (tabs (n + 1)) ^ "END\n" ^
            (tabs n) ^ "END"
          | caseAux ((ees, ss) :: l) =
            (tabs (n + 1)) ^ "OR " ^ (showExprListInCase ees) ^ " THEN\n" ^
            (showSubstitution (n + 2) ss) ^ "\n" ^
            (caseAux l)
          | caseAux _ = raise ShowError ""
      in
        (tabs n) ^ "CASE " ^ (showExpr ex) ^ " OF\n" ^
        (tabs (n + 1)) ^ "EITHER " ^ (showExprList es) ^ " THEN\n" ^
        (showSubstitution (n + 2) s) ^ "\n" ^
        (caseAux l)
      end
    | showSubstitution _ (BS_Case _) = raise ShowError "invalid CASE"
    | showSubstitution n (BS_Any (tlst, p, s)) =
      (tabs n) ^ "ANY\n" ^
      (tabs (n + 1)) ^ (showTokenList tlst) ^ "\n" ^
      (tabs n) ^ "WHERE\n" ^
      (showPredicate (n + 1) p) ^ "\n" ^
      (tabs n) ^ "THEN\n" ^
      (showSubstitution (n + 1) s) ^ "\n" ^
      (tabs n) ^ "END"

    | showSubstitution n (BS_Let (l, s)) =
      (tabs n) ^ "LET\n" ^
      (tabs (n + 1)) ^ (showTokenList (List.map (fn (v, e) => v) l)) ^ "\n" ^
      (tabs n) ^ "BE\n" ^
      (Utils.concatWith " &\n" (List.map (fn (Var x, e) => ((tabs (n + 1)) ^ x ^ " = " ^ (showExpr e)) | _ => raise ShowError "") l)) ^ "\n" ^
      (tabs n) ^ "IN\n" ^
      (showSubstitution (n + 1) s) ^ "\n" ^
      (tabs n) ^ "END"

    | showSubstitution n (BS_BecomesElt (el, re)) =
      (tabs n) ^ (showExprList el) ^ " :: " ^ (showExpr re)

    | showSubstitution n (BS_BecomesSuchThat (es, BP p)) =
      (tabs n) ^ (showExprList es) ^ " :( " ^ (showExpr p) ^ ")"


    | showSubstitution n (BS_Call (opName, outputs, inputs)) =
      (tabs n) ^ (if outputs = [] then "" else (showExprList outputs) ^ " <-- ") ^ (showToken opName) ^ (if inputs = [] then "" else "(" ^ (showExprList inputs) ^ ")")

    | showSubstitution n (BS_BecomesEqual (e1, e2)) =
      (tabs n) ^ (showExpr e1) ^ " := " ^ (showExpr e2)

    | showSubstitution n (BS_BecomesEqualList (e1, e2)) =
      (tabs n) ^ (showExprList e1) ^ " := " ^ (showExprList e2)

    | showSubstitution n (BS_Simultaneous l) =
      Utils.concatWith " ||\n" (List.map (showSubstitution n) l)

    | showSubstitution n (BS_LocalVariable (tks, s)) =
      (tabs n) ^ "VAR\n" ^
      (tabs (n + 1)) ^ (showTokenList tks) ^ "\n" ^
      (tabs n) ^ "IN\n" ^
      (showSubstitution (n + 1) s) ^ "\n" ^
      (tabs n) ^ "END"

    | showSubstitution n (BS_Sequencing l) =
      Utils.concatWith " ;\n" (List.map (showSubstitution n) l)

    | showSubstitution n (BS_While (p1, s, p2, e)) =
      (tabs n) ^ "WHILE\n" ^
      (showPredicate (n + 1) p1) ^ "\n" ^
      (tabs n) ^ "DO\n" ^
      (showSubstitution (n + 1) s) ^ "\n" ^
      (tabs n) ^ "INVARIANT\n" ^
      (showPredicate (n + 1) p2) ^ "\n" ^
      (tabs n) ^ "VARIANT\n" ^
      (tabs (n + 1)) ^ (showExpr e) ^ "\n" ^
      (tabs n) ^ "END"

  and
      showMachine []                           = raise ShowError "empty machine list"
    | showMachine [(BMchInst (v, es))]         = "\t" ^ (showToken v) ^ "[ExprList]"^ (if es = [] then "" else "(" ^ (showExprList es) ^ ")") ^ "\n"
    | showMachine ((BMchInst (v, es)) :: rest) = "\t" ^ (showToken v) ^ (if es = [] then "" else "(" ^ (showExprList es) ^ ")") ^ ",\n" ^ (showMachine rest)

  and
      showPredicate n (BP (BE_Commutative (_, Keyword "&", (e :: es)))) =
      let
        val s = if #1 (priOf e) < 40 then (tabs n) ^ "(" ^ (showExpr e) ^ ")" else (tabs n) ^ (showExpr e)
        val ss = List.map (fn x => if #1 (priOf x) <= 40 then (tabs n) ^ "(" ^ (showExpr x) ^ ")" else (tabs n) ^ (showExpr x)) es
      in
        (Utils.concatWith " &\n" (s :: ss))
      end
    | showPredicate n (BP e) = (tabs n) ^ (showExpr e)

  and
      showExpr (BE_Leaf (_, token)) = showToken token
    | showExpr (BE_Node1 (_, Keyword "~", e)) =
      if #1 (priOf e) <= 230 then
        "(" ^ (showExpr e) ^ ")~"
      else
        (showExpr e) ^ "~"
    | showExpr (BE_Node1 (_, Keyword "-", e)) =
      if #1 (priOf e) <= 210 then
        "(-(" ^ (showExpr e) ^ "))"
      else
        "(-" ^ (showExpr e) ^ ")"
    (* 単項マイナス演算子の外側の括弧はB言語マニュアルによると必要ないはずだがAtelier Bでは無いとエラーとなる場合がある *)
    | showExpr (BE_Node1 (_, Keyword s, e)) = s ^ "(" ^ (showExpr e) ^ ")"

    | showExpr (BE_Node2 (_, Keyword "mod", e1, e2)) =
      let
        val p1 = #1 (priOf e1)
        val p2 = #1 (priOf e2)
      in
        (if p1 <  190 then "(" ^ (showExpr e1) ^ ")" else showExpr e1) ^ " mod " ^
        (if p2 <= 190 then "(" ^ (showExpr e2) ^ ")" else showExpr e2)
      end
    | showExpr (BE_Node2 (_ ,Keyword "or", e1, e2)) =
      let
        val p1 = #1 (priOf e1)
        val p2 = #1 (priOf e2)
      in
        (if p1 < 40  then "(" ^ (showExpr e1) ^ ")" else showExpr e1) ^ " or " ^
        (if p2 <= 40 then "(" ^ (showExpr e2) ^ ")" else showExpr e2)
      end
    | showExpr (BE_Node2 (_, Keyword ";" , e1, e2)) = "(" ^ (showExpr e1) ^ " ; "  ^ (showExpr e2) ^ ")" (* 操作の区切りなどを表す;と区別するため括弧をかならず付ける *)
    | showExpr (BE_Node2 (_, Keyword "||", e1, e2)) = "(" ^ (showExpr e1) ^ " || " ^ (showExpr e2) ^ ")"
    | showExpr (BE_Node2 (_, Keyword s, e1, e2)) =
      if
        List.exists (Utils.eqto s) Keywords.alphaKeywords
      then
        s ^ "(" ^ (showExpr e1) ^ ", " ^ (showExpr e2) ^ ")"
      else
        let
          val (p, a) = priOfT (Keyword s)
          val p1 = #1 (priOf e1)
          val p2 = #1 (priOf e2)
        in
          if a = Priority.L then
            (if p1 <  p then "(" ^ (showExpr e1) ^ ")" else showExpr e1) ^ " " ^ s ^ " " ^
            (if p2 <= p then "(" ^ (showExpr e2) ^ ")" else showExpr e2)
          else
            (if p1 <= p then "(" ^ (showExpr e1) ^ ")" else showExpr e1) ^ " " ^ s ^ " " ^
            (if p2 <  p then "(" ^ (showExpr e2) ^ ")" else showExpr e2)
        end

    | showExpr (BE_Commutative (_, Keyword s, es)) =
      let
        val p = #1 (priOfT (Keyword s)) (* 可換演算子はすべて左結合 *)
        val pl = List.map (fn e => (e, #1 (priOf e))) es
        fun concatExprList [] = ""
          | concatExprList ((e, ep) :: xs) = " " ^ s ^ " " ^ (if ep <= p then "(" ^ (showExpr e) ^ ")" else showExpr e) ^ (concatExprList xs)
        val (fste, fstep) = hd pl
      in
        (if fstep < p then "(" ^ (showExpr fste) ^ ")" else showExpr fste) ^ (concatExprList (tl pl))
      end
    | showExpr (BE_Fnc (_, e1, e2)) = (
        if #1 (priOf e1) < 230 then
          "(" ^ (showExpr e1) ^ ")"
        else
          case e1 of
            BE_RcAc _ => "(" ^ (showExpr e1) ^ ")"
          | BE_Img  _ => "(" ^ (showExpr e1) ^ ")"
          | _         => showExpr e1              ) ^
        "(" ^ (showExpr e2) ^ ")"
    | showExpr (BE_Img (_, e1, e2)) = (
        if #1 (priOf e1) < 230 then
          "(" ^ (showExpr e1) ^ ")"
        else
          case e1 of
            BE_RcAc _ => "(" ^ (showExpr e1) ^ ")"
          | BE_Img _ => "(" ^ (showExpr e1) ^ ")"
          | _ => showExpr e1) ^ "[" ^ (showExpr e2) ^ "]"

    | showExpr (BE_NodeN (_, Keyword s, es)) = s ^ "(" ^ (showExprList es) ^ ")"
    | showExpr (BE_Bool (BP e)) = "bool(" ^ (showExpr e) ^ ")"

    | showExpr (BE_ExSet (_, l)) = "{" ^ (showExprList l) ^ "}"

    | showExpr (BE_InSet (_, v, BP p)) = "{" ^ (showTokenList v) ^ " | " ^ (showExpr p) ^ "}"

    | showExpr (BE_Seq (_, e)) = "[" ^ (showExprList e) ^ "]"

    | showExpr (BE_ForAll ([], _, _)) = raise ShowError "missing variables of \"!\""
    | showExpr (BE_ForAll ([x], BP p1, BP p2)) = "!" ^  (showToken x) ^       ".(" ^ (showExpr p1) ^ " => " ^ (showExpr p2) ^ ")"
    | showExpr (BE_ForAll (xs,  BP p1, BP p2)) = "!(" ^ (showTokenList xs) ^ ").(" ^ (showExpr p1) ^ " => " ^ (showExpr p2) ^ ")"

    | showExpr (BE_Exists ([],  _)) = raise ShowError "missing variables of \"#\""
    | showExpr (BE_Exists ([x], BP p)) = "#" ^  (showToken x) ^       ".(" ^ (showExpr p) ^ ")"
    | showExpr (BE_Exists (xs,  BP p)) = "#(" ^ (showTokenList xs) ^ ").(" ^ (showExpr p) ^ ")"

    | showExpr (BE_Lambda (_, xs, BP p, e)) = showLambdas "%"     xs p e
    | showExpr (BE_Sigma  (_, xs, BP p, e)) = showSigma  "SIGMA" xs p e
    | showExpr (BE_Pi     (_, xs, BP p, e)) = showSigma  "PI"    xs p e
    | showExpr (BE_Inter  (_, xs, BP p, e)) = showLambdas "INTER" xs p e
    | showExpr (BE_Union  (_, xs, BP p, e)) = showLambdas "UNION" xs p e

    | showExpr (BE_Struct (_, l)) =
      let
        fun fields [] = raise ShowError "empty struct"
          | fields [(s, e)] =
            if
              #1 (priOf e) < 120
            then
              s ^ ":(" ^ (showExpr e) ^ ")"
            else
              s ^ ":"  ^ (showExpr e)
          | fields ((s, e) :: rest) =
            if
              #1 (priOf e) < 120
            then
              s ^ ":(" ^ (showExpr e) ^ "), " ^ (fields rest)
            else
              s ^ ":"  ^ (showExpr e) ^  ", " ^ (fields rest)
      in
        "struct(" ^ (fields l) ^ ")"
      end

    | showExpr (BE_Rec (_, l)) =
      let
        fun unwrapLabel NONE = ""
          | unwrapLabel (SOME s) = s ^ ":"
        fun fields [] = raise ShowError "empty struct"
          | fields [(sOpt, e)] =
            if
              #1 (priOf e) < 120
            then
              (unwrapLabel sOpt) ^ "(" ^ (showExpr e) ^ ")"
            else
              (unwrapLabel sOpt) ^       (showExpr e)
          | fields ((sOpt, e) :: rest) =
            if
              #1 (priOf e) < 120
            then
              (unwrapLabel sOpt) ^ "(" ^ (showExpr e) ^ "), " ^ (fields rest)
            else
              (unwrapLabel sOpt) ^       (showExpr e) ^  ", " ^ (fields rest)
      in
        "rec(" ^ (fields l) ^ ")"
      end
    | showExpr (BE_RcAc (_, e, s)) = (showExpr e) ^ s
    | showExpr _ = raise ShowError "unknown expression"

  and
      showSigma kw x p e = kw ^ " " ^ (showToken x) ^ ".(" ^ (showExpr p) ^ " | " ^ (showExpr e) ^ ")"

  and
      showLambdas "%" [x] p e = "%" ^       (showToken x) ^       ".(" ^ (showExpr p) ^ " | " ^ (showExpr e) ^ ")"
    | showLambdas kw  xs  p e = kw  ^ "(" ^ (showTokenList xs) ^ ").(" ^ (showExpr p) ^ " | " ^ (showExpr e) ^ ")"

  and
      showExprList el =
      let
        val sl = List.map (fn x => if #1 (priOf x) <= 115 then "(" ^ (showExpr x) ^ ")" else showExpr x) el
      in
        Utils.concatWith ", " sl
      end

  and
      showExprListInCase el = Utils.concatWith ", " (List.map showExpr el)

  and
      showTokenList l = Utils.concatWith ", " (List.map showToken l)

  and
      showToken (Var l)            = "[Var]" ^ l
    | showToken (Renamed (rn, v))  = "[Renamed]" ^ rn ^ "." ^ v
    | showToken (IntegerLiteral n) = "[IntegerLiteral]" ^ IntInf.toString n
    | showToken (StringLiteral s)  = "[StringLiteral]" ^ "\"" ^ s ^ "\""
    | showToken (RealLiteral r)    = "[RealLiteral]" ^ BReal.toString r
    | showToken (Keyword s)        = "[Keyword]" ^ s
    | showToken (VarLit l)         = "[VarLit]" ^ l
    | showToken (VarSingle l)      = "[VarSingle]" ^ l

  and
      showHistory [] = "/*\n*/\n"
    | showHistory l =
      let
        fun showHistoryAux (b, a, NONE)   = b ^ "@->@" ^ a ^                    "\n"
          | showHistoryAux (b, a, SOME e) = b ^ "@->@" ^ a ^ "@" ^ (showExpr e) ^ "\n"
      in
        "/*\n" ^ (List.foldl (fn (str1, str2) => str1 ^ str2) "" (List.map showHistoryAux l)) ^ "*/\n"
      end

  and
      showModelDependencies [] = "/*\n*/\n"
    | showModelDependencies l  = "/*\n" ^ (String.concat (List.map (fn s => s ^ "\n") l)) ^ "*/\n"
end


