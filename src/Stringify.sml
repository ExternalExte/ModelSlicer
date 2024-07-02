structure Stringify =
struct
  exception StringifyError of string
  
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
    | priOfT _ = raise StringifyError "a token should be operator but not"
  and
      componentToString (BMch (mchName,          [],     clauses)) = "MACHINE" ^        "\n\t" ^ mchName ^                                                                "\n\n" ^ (clauseListToString clauses) ^ "END\n"
    | componentToString (BMch (mchName,          params, clauses)) = "MACHINE" ^        "\n\t" ^ mchName ^ "(" ^ (tokenListToString params) ^ ")" ^                             "\n\n" ^ (clauseListToString clauses) ^ "END\n"
    | componentToString (BRef (refName, mchName, [],     clauses)) = "REFINEMENT" ^     "\n\t" ^ refName ^                                    "\nREFINES\n\t" ^ mchName ^ "\n\n" ^ (clauseListToString clauses) ^ "END\n"
    | componentToString (BRef (refName, mchName, params, clauses)) = "REFINEMENT" ^     "\n\t" ^ refName ^ "(" ^ (tokenListToString params) ^ ")" ^ "\nREFINES\n\t" ^ mchName ^ "\n\n" ^ (clauseListToString clauses) ^ "END\n"
    | componentToString (BImp (refName, mchName, [],     clauses)) = "IMPLEMENTATION" ^ "\n\t" ^ refName ^                                    "\nREFINES\n\t" ^ mchName ^ "\n\n" ^ (clauseListToString clauses) ^ "END\n"
    | componentToString (BImp (refName, mchName, params, clauses)) = "IMPLEMENTATION" ^ "\n\t" ^ refName ^ "(" ^ (tokenListToString params) ^ ")" ^ "\nREFINES\n\t" ^ mchName ^ "\n\n" ^ (clauseListToString clauses) ^ "END\n"

  and
      clauseListToString clauses =
      let
        val sortedClauses = ListMergeSort.sort (fn (c1, c2) => #2 (valOf (List.find (fn (ss1, _) => clauseToClauseName c1 = ss1) Keywords.clauseKeywords)) >= #2 (valOf (List.find (fn (ss2, _) => clauseToClauseName c2 = ss2) Keywords.clauseKeywords))) clauses
        fun clauseListToStringAux [] = ""
          | clauseListToStringAux (x :: xs) = (clauseToString x) ^ (clauseListToStringAux xs)
      in
        clauseListToStringAux sortedClauses
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
      clauseToString (c as BC_CONSTRAINTS p)    = (clauseToClauseName c) ^ "\n" ^ (predicateToString 1 p) ^ "\n\n"
    | clauseToString (c as BC_PROPERTIES p)     = (clauseToClauseName c) ^ "\n" ^ (predicateToString 1 p) ^ "\n\n"
    | clauseToString (c as BC_INVARIANT p)      = (clauseToClauseName c) ^ "\n" ^ (predicateToString 1 p) ^ "\n\n"
    | clauseToString (c as BC_ASSERTIONS p)     = (clauseToClauseName c) ^ "\n" ^ (predicateToString 1 p) ^ "\n\n"

    | clauseToString (c as BC_VALUES l)         = (clauseToClauseName c) ^ "\n\t" ^ (Utils.concatWith ";\n\t" (List.map (fn (v, e) => (tokenToString v) ^ " = " ^ (exprToString e)) l)) ^ "\n\n"

    | clauseToString (c as BC_SEES l)           = (clauseToClauseName c) ^ "\n" ^ (machinesToString l) ^ "\n"
    | clauseToString (c as BC_INCLUDES l)       = (clauseToClauseName c) ^ "\n" ^ (machinesToString l) ^ "\n"
    | clauseToString (c as BC_PROMOTES l)       = (clauseToClauseName c) ^ "\n" ^ (machinesToString l) ^ "\n"
    | clauseToString (c as BC_EXTENDS l)        = (clauseToClauseName c) ^ "\n" ^ (machinesToString l) ^ "\n"
    | clauseToString (c as BC_USES l)           = (clauseToClauseName c) ^ "\n" ^ (machinesToString l) ^ "\n"
    | clauseToString (c as BC_IMPORTS l)        = (clauseToClauseName c) ^ "\n" ^ (machinesToString l) ^ "\n"

    | clauseToString (c as BC_CCONSTANTS l)     = (clauseToClauseName c) ^ "\n\t" ^ (tokenListToString l) ^ "\n\n"
    | clauseToString (c as BC_ACONSTANTS l)     = (clauseToClauseName c) ^ "\n\t" ^ (tokenListToString l) ^ "\n\n"
    | clauseToString (c as BC_CVARIABLES l)     = (clauseToClauseName c) ^ "\n\t" ^ (tokenListToString l) ^ "\n\n"
    | clauseToString (c as BC_AVARIABLES l)     = (clauseToClauseName c) ^ "\n\t" ^ (tokenListToString l) ^ "\n\n"
    | clauseToString (c as BC_DEFINITIONS l)    = "/*DEFINITIONS CLAUSE EXISTS*/\n" (* 未対応 *)

    | clauseToString (c as BC_SETS l)           = 
      let
        fun setToString (BT_Deferred s) = s
          | setToString (BT_Enum (s, elts)) = s ^ " = {" ^ (Utils.concatWith ", " elts) ^ "}"
          | setToString _ = raise StringifyError "unknown type in SETS"
      in
        (clauseToClauseName c) ^ "\n\t" ^ (Utils.concatWith "; " (List.map setToString l)) ^ "\n\n"
      end
    | clauseToString (c as BC_OPERATIONS l)     = (clauseToClauseName c) ^ "\n" ^ (Utils.concatWith ";\n\n" (List.map operationToString l)) ^ "\n"
    | clauseToString (c as BC_INITIALISATION s) = (clauseToClauseName c) ^ "\n" ^ (substitutionToString 1 s) ^ "\n\n"

  and
      operationToString (BOp (name, [],      [],     subs)) =
      (tabs 1) ^ name ^ " =\n" ^ 
      (topSubstitutionToString subs)
    | operationToString (BOp (name, [],      inputs, subs)) =
      (tabs 1) ^ name ^ "(" ^ (tokenListToString inputs) ^ ") =\n" ^ 
      (topSubstitutionToString subs)
    | operationToString (BOp (name, outputs, [],     subs)) =
      (tabs 1) ^ (tokenListToString outputs) ^ " <-- " ^ name ^ " =\n" ^ 
      (topSubstitutionToString subs)
    | operationToString (BOp (name, outputs, inputs, subs)) = 
      (tabs 1) ^ (tokenListToString outputs) ^ " <-- " ^ name ^ "(" ^ (tokenListToString inputs) ^ ") =\n" ^ 
      (topSubstitutionToString subs)
  and
    (* Becomes such that 代入、同時代入、逐次代入、所属代入は操作のトップレベルに置けないためBEGIN ENDで囲む *)
      topSubstitutionToString (BS_BecomesSuchThat x) = substitutionToString 2 (BS_Block (BS_BecomesSuchThat x))
    | topSubstitutionToString (BS_Sequencing l)      = substitutionToString 2 (BS_Block (BS_Sequencing l))
    | topSubstitutionToString (BS_Simultaneous l)    = substitutionToString 2 (BS_Block (BS_Simultaneous l))
    | topSubstitutionToString (BS_BecomesElt x)      = substitutionToString 2 (BS_Block (BS_BecomesElt x))
    | topSubstitutionToString s                      = substitutionToString 2 s
  and
      substitutionToString n (BS_Block s) =
      (tabs n) ^ "BEGIN\n" ^ 
      (substitutionToString (n + 1) s) ^ "\n" ^ 
      (tabs n) ^ "END"
    | substitutionToString n BS_Identity = (tabs n) ^ "skip"
    | substitutionToString n (BS_Precondition (p, s)) = 
      (tabs n) ^ "PRE\n" ^ 
      (predicateToString (n + 1) p) ^ "\n" ^
      (tabs n) ^ "THEN\n" ^ 
      (substitutionToString (n + 1) s) ^ "\n" ^ 
      (tabs n) ^ "END"
    | substitutionToString n (BS_Assertion (p, s)) =
      (tabs n) ^ "PRE\n" ^ 
      (predicateToString (n + 1) p) ^ "\n" ^
      (tabs n) ^ "THEN\n" ^ 
      (substitutionToString (n + 1) s) ^ "\n" ^ 
      (tabs n) ^ "END"
    | substitutionToString n (BS_Choice l) = 
      let
        fun choiceAux [] = raise StringifyError ""
          | choiceAux [s] = (substitutionToString (n + 1) s) ^ "\n"
          | choiceAux (s :: ss) = 
            (substitutionToString (n + 1) s) ^ "\n" ^ 
            (tabs n) ^ "OR\n" ^ (choiceAux ss)
      in
        (tabs n) ^ "CHOICE\n" ^ 
        (choiceAux l) ^ 
        (tabs n) ^ "END"
      end
    | substitutionToString n (BS_If ([(SOME p, s)])) = 
      (tabs n) ^ "IF\n" ^ 
      (predicateToString (n + 1) p) ^ "\n" ^
      (tabs n) ^ "THEN\n" ^ 
      (substitutionToString (n + 1) s) ^ "\n" ^ 
      (tabs n) ^ "END"
    | substitutionToString n (BS_If ((SOME p, s) :: l)) =
      let
        fun ifAux [(NONE, ss)] =
            (tabs n) ^ "ELSE\n" ^ 
            (substitutionToString (n + 1) ss) ^ "\n" ^ 
            (tabs n) ^ "END"
          | ifAux [(SOME pp, ss)] =
            (tabs n) ^ "ELSIF\n" ^ 
            (predicateToString (n + 1) pp) ^ "\n" ^
            (tabs n) ^ "THEN\n" ^ 
            (substitutionToString (n + 1) ss) ^ "\n" ^ 
            (tabs n) ^ "END"
          | ifAux ((SOME pp, ss) :: ll) =
            (tabs n) ^ "ELSIF\n" ^ 
            (predicateToString (n + 1) pp) ^ "\n" ^
            (tabs n) ^ "THEN\n" ^ 
            (substitutionToString (n + 1) ss) ^ "\n" ^ 
            (ifAux ll)
          | ifAux _ = raise StringifyError ""
      in
        (tabs n) ^ "IF\n" ^ 
        (predicateToString (n + 1) p) ^ "\n" ^
        (tabs n) ^ "THEN\n" ^ 
        (substitutionToString (n + 1) s) ^ "\n" ^ 
        (ifAux l)
      end 
    | substitutionToString _ (BS_If _) = raise StringifyError "invalid IF"
    | substitutionToString n (BS_Select ([(SOME p, s)])) = 
      (tabs n) ^ "SELECT\n" ^ 
      (predicateToString (n + 1) p) ^ "\n" ^
      (tabs n) ^ "THEN\n" ^ 
      (substitutionToString (n + 1) s) ^ "\n" ^ 
      (tabs n) ^ "END"
    | substitutionToString n (BS_Select ((SOME p, s) :: l)) =
      let
        fun selectAux [(NONE, ss)] =
            (tabs n) ^ "ELSE\n" ^ 
            (substitutionToString (n + 1) ss) ^ "\n" ^ 
            (tabs n) ^ "END"
          | selectAux [(SOME pp, ss)] =
            (tabs n) ^ "WHEN\n" ^ 
            (predicateToString (n + 1) pp) ^ "\n" ^ 
            (tabs n) ^ "THEN\n" ^ 
            (substitutionToString (n + 1) ss) ^ "\n" ^ 
            (tabs n) ^ "END"
          | selectAux ((SOME pp, ss) :: ll) =
            (tabs n) ^ "WHEN\n" ^ 
            (predicateToString (n + 1) pp) ^ "\n" ^
            (tabs n) ^ "THEN\n" ^ 
            (substitutionToString (n + 1) ss) ^ "\n" ^ 
            (selectAux ll)
          | selectAux _ = raise StringifyError ""
      in
        (tabs n) ^ "SELECT\n" ^ 
        (predicateToString (n + 1) p) ^ "\n" ^
        (tabs n) ^ "THEN\n" ^ 
        (substitutionToString (n + 1) s) ^ "\n" ^ 
        (selectAux l)
      end 
    | substitutionToString _ (BS_Select _) = raise StringifyError "invalid IF"
    | substitutionToString n (BS_Case (ex, [(es, s)])) =
      (tabs n) ^ "CASE " ^ (exprToString ex) ^ " OF\n" ^ 
      (tabs (n + 1)) ^ "EITHER " ^ (exprListInCaseToString es) ^ " THEN\n" ^ 
      (substitutionToString (n + 2) s) ^ "\n" ^ 
      (tabs (n + 1)) ^ "END\n" ^ 
      (tabs n) ^ "END"
    | substitutionToString n (BS_Case (ex, ((es, s) :: l))) =
      let
        fun caseAux [([], ss)] =
            (tabs (n + 1)) ^ "ELSE\n" ^ 
            (substitutionToString (n + 2) ss) ^ "\n" ^ 
            (tabs (n + 1)) ^ "END\n" ^ 
            (tabs n) ^ "END"
          | caseAux [(ees, ss)] =
            (tabs (n + 1)) ^ "OR " ^ (exprListInCaseToString ees) ^ " THEN\n" ^ 
            (substitutionToString (n + 2) ss) ^ "\n" ^ 
            (tabs (n + 1)) ^ "END\n" ^ 
            (tabs n) ^ "END"
          | caseAux ((ees, ss) :: l) = 
            (tabs (n + 1)) ^ "OR " ^ (exprListInCaseToString ees) ^ " THEN\n" ^ 
            (substitutionToString (n + 2) ss) ^ "\n" ^ 
            (caseAux l)
          | caseAux _ = raise StringifyError ""
      in
        (tabs n) ^ "CASE " ^ (exprToString ex) ^ " OF\n" ^ 
        (tabs (n + 1)) ^ "EITHER " ^ (exprListToString es) ^ " THEN\n" ^ 
        (substitutionToString (n + 2) s) ^ "\n" ^ 
        (caseAux l)
      end
    | substitutionToString _ (BS_Case _) = raise StringifyError "invalid CASE"
    | substitutionToString n (BS_Any (tlst, p, s)) =
      (tabs n) ^ "ANY\n" ^ 
      (tabs (n + 1)) ^ (tokenListToString tlst) ^ "\n" ^ 
      (tabs n) ^ "WHERE\n" ^ 
      (predicateToString (n + 1) p) ^ "\n" ^
      (tabs n) ^ "THEN\n" ^ 
      (substitutionToString (n + 1) s) ^ "\n" ^ 
      (tabs n) ^ "END"

    | substitutionToString n (BS_Let (l, s)) =
      (tabs n) ^ "LET\n" ^ 
      (tabs (n + 1)) ^ (tokenListToString (List.map (fn (v, e) => v) l)) ^ "\n" ^ 
      (tabs n) ^ "BE\n" ^ 
      (Utils.concatWith " &\n" (List.map (fn (Var x, e) => ((tabs (n + 1)) ^ x ^ " = " ^ (exprToString e)) | _ => raise StringifyError "") l)) ^ "\n" ^ 
      (tabs n) ^ "IN\n" ^ 
      (substitutionToString (n + 1) s) ^ "\n" ^ 
      (tabs n) ^ "END"

    | substitutionToString n (BS_BecomesElt (el, re)) =
      (tabs n) ^ (exprListToString el) ^ " :: " ^ (exprToString re)

    | substitutionToString n (BS_BecomesSuchThat (es, BP p)) =
      (tabs n) ^ (exprListToString es) ^ " :( " ^ (exprToString p) ^ ")"


    | substitutionToString n (BS_Call (opName, outputs, inputs)) =
      (tabs n) ^ (if outputs = [] then "" else (exprListToString outputs) ^ " <-- ") ^ (tokenToString opName) ^ (if inputs = [] then "" else "(" ^ (exprListToString inputs) ^ ")")

    | substitutionToString n (BS_BecomesEqual (e1, e2)) =
      (tabs n) ^ (exprToString e1) ^ " := " ^ (exprToString e2)

    | substitutionToString n (BS_BecomesEqualList (e1, e2)) =
      (tabs n) ^ (exprListToString e1) ^ " := " ^ (exprListToString e2)

    | substitutionToString n (BS_Simultaneous l) =
      Utils.concatWith " ||\n" (List.map (substitutionToString n) l)

    | substitutionToString n (BS_LocalVariable (tks, s)) =
      (tabs n) ^ "VAR\n" ^
      (tabs (n + 1)) ^ (tokenListToString tks) ^ "\n" ^
      (tabs n) ^ "IN\n" ^
      (substitutionToString (n + 1) s) ^ "\n" ^
      (tabs n) ^ "END"

    | substitutionToString n (BS_Sequencing l) =
      Utils.concatWith " ;\n" (List.map (substitutionToString n) l)

    | substitutionToString n (BS_While (p1, s, p2, e)) =
      (tabs n) ^ "WHILE\n" ^
      (predicateToString (n + 1) p1) ^ "\n" ^
      (tabs n) ^ "DO\n" ^
      (substitutionToString (n + 1) s) ^ "\n" ^
      (tabs n) ^ "INVARIANT\n" ^
      (predicateToString (n + 1) p2) ^ "\n" ^
      (tabs n) ^ "VARIANT\n" ^
      (tabs (n + 1)) ^ (exprToString e) ^ "\n" ^
      (tabs n) ^ "END"
  and
      machinesToString []                           = raise StringifyError "empty machine list"
    | machinesToString [(BMchInst (v, es))]         = "\t" ^ (tokenToString v) ^ (if es = [] then "" else "(" ^ (exprListToString es) ^ ")") ^ "\n"
    | machinesToString ((BMchInst (v, es)) :: rest) = "\t" ^ (tokenToString v) ^ (if es = [] then "" else "(" ^ (exprListToString es) ^ ")") ^ ",\n" ^ (machinesToString rest)
  and
      predicateToString n (BP (BE_Commutative (_, Keyword "&", (e :: es)))) = 
      let
        val s = if #1 (priOf e) < 40 then (tabs n) ^ "(" ^ (exprToString e) ^ ")" else (tabs n) ^ (exprToString e)
        val ss = List.map (fn x => if #1 (priOf x) <= 40 then (tabs n) ^ "(" ^ (exprToString x) ^ ")" else (tabs n) ^ (exprToString x)) es
      in
        (Utils.concatWith " &\n" (s :: ss))
      end
    | predicateToString n (BP e) = (tabs n) ^ (exprToString e)
  and
      exprToString (BE_Leaf (_, token)) = tokenToString token
    | exprToString (BE_Node1 (_, Keyword "~", e)) = 
      if #1 (priOf e) <= 230 then
        "(" ^ (exprToString e) ^ ")~"
      else
        (exprToString e) ^ "~"
    | exprToString (BE_Node1 (_, Keyword "-", e)) = 
      if #1 (priOf e) <= 210 then
        "(-(" ^ (exprToString e) ^ "))"
      else
        "(-" ^ (exprToString e) ^ ")"
    (* 単項マイナス演算子の外側の括弧はB言語マニュアルによると必要ないはずだがAtelier Bでは無いとエラーとなる場合がある *)
    | exprToString (BE_Node1 (_, Keyword s, e)) = s ^ "(" ^ (exprToString e) ^ ")"

    | exprToString (BE_Node2 (_, Keyword "mod", e1, e2)) =
      let
        val p1 = #1 (priOf e1)
        val p2 = #1 (priOf e2)
      in
        (if p1 <  190 then "(" ^ (exprToString e1) ^ ")" else exprToString e1) ^ " mod " ^ 
        (if p2 <= 190 then "(" ^ (exprToString e2) ^ ")" else exprToString e2)
      end
    | exprToString (BE_Node2 (_ ,Keyword "or", e1, e2)) =
      let
        val p1 = #1 (priOf e1)
        val p2 = #1 (priOf e2)
      in
        (if p1 < 40  then "(" ^ (exprToString e1) ^ ")" else exprToString e1) ^ " or " ^ 
        (if p2 <= 40 then "(" ^ (exprToString e2) ^ ")" else exprToString e2)
      end
    | exprToString (BE_Node2 (_, Keyword ";" , e1, e2)) = "(" ^ (exprToString e1) ^ " ; "  ^ (exprToString e2) ^ ")" (* 操作の区切りなどを表す;と区別するため括弧をかならず付ける *)
    | exprToString (BE_Node2 (_, Keyword "||", e1, e2)) = "(" ^ (exprToString e1) ^ " || " ^ (exprToString e2) ^ ")" 
    | exprToString (BE_Node2 (_, Keyword s, e1, e2)) = 
      if
        List.exists (Utils.eqto s) Keywords.alphaKeywords
      then
        s ^ "(" ^ (exprToString e1) ^ ", " ^ (exprToString e2) ^ ")"
      else
        let
          val (p, a) = priOfT (Keyword s)
          val p1 = #1 (priOf e1)
          val p2 = #1 (priOf e2)
        in
          if a = Priority.L then
            (if p1 <  p then "(" ^ (exprToString e1) ^ ")" else exprToString e1) ^ " " ^ s ^ " " ^ 
            (if p2 <= p then "(" ^ (exprToString e2) ^ ")" else exprToString e2)
          else
            (if p1 <= p then "(" ^ (exprToString e1) ^ ")" else exprToString e1) ^ " " ^ s ^ " " ^ 
            (if p2 <  p then "(" ^ (exprToString e2) ^ ")" else exprToString e2)
        end

    | exprToString (BE_Commutative (_, Keyword s, es)) =
      let
        val p = #1 (priOfT (Keyword s)) (* 可換演算子はすべて左結合 *)
        val pl = List.map (fn e => (e, #1 (priOf e))) es
        fun concatExprList [] = ""
          | concatExprList ((e, ep) :: xs) = " " ^ s ^ " " ^ (if ep <= p then "(" ^ (exprToString e) ^ ")" else exprToString e) ^ (concatExprList xs)
        val (fste, fstep) = hd pl
      in
        (if fstep < p then "(" ^ (exprToString fste) ^ ")" else exprToString fste) ^ (concatExprList (tl pl))
      end
    | exprToString (BE_Fnc (_, e1, e2)) = (
        if #1 (priOf e1) < 230 then 
          "(" ^ (exprToString e1) ^ ")" 
        else
          case e1 of
            BE_RcAc _ => "(" ^ (exprToString e1) ^ ")"
          | BE_Img  _ => "(" ^ (exprToString e1) ^ ")"
          | _         => exprToString e1              ) ^
        "(" ^ (exprToString e2) ^ ")"
    | exprToString (BE_Img (_, e1, e2)) = (
        if #1 (priOf e1) < 230 then 
          "(" ^ (exprToString e1) ^ ")" 
        else
          case e1 of
            BE_RcAc _ => "(" ^ (exprToString e1) ^ ")"
          | BE_Img _ => "(" ^ (exprToString e1) ^ ")"
          | _ => exprToString e1) ^ "[" ^ (exprToString e2) ^ "]"
          
    | exprToString (BE_NodeN (_, Keyword s, es)) = s ^ "(" ^ (exprListToString es) ^ ")"
    | exprToString (BE_Bool (BP e)) = "bool(" ^ (exprToString e) ^ ")"
    
    | exprToString (BE_ExSet (_, l)) = "{" ^ (exprListToString l) ^ "}"

    | exprToString (BE_InSet (_, v, BP p)) = "{" ^ (tokenListToString v) ^ " | " ^ (exprToString p) ^ "}"
    
    | exprToString (BE_Seq (_, e)) = "[" ^ (exprListToString e) ^ "]"

    | exprToString (BE_ForAll ([], _, _)) = raise StringifyError "missing variables of \"!\""
    | exprToString (BE_ForAll ([x], BP p1, BP p2)) = "!" ^  (tokenToString x) ^       ".(" ^ (exprToString p1) ^ " => " ^ (exprToString p2) ^ ")"
    | exprToString (BE_ForAll (xs,  BP p1, BP p2)) = "!(" ^ (tokenListToString xs) ^ ").(" ^ (exprToString p1) ^ " => " ^ (exprToString p2) ^ ")"

    | exprToString (BE_Exists ([],  _)) = raise StringifyError "missing variables of \"#\""
    | exprToString (BE_Exists ([x], BP p)) = "#" ^  (tokenToString x) ^       ".(" ^ (exprToString p) ^ ")"
    | exprToString (BE_Exists (xs,  BP p)) = "#(" ^ (tokenListToString xs) ^ ").(" ^ (exprToString p) ^ ")"

    | exprToString (BE_Lambda (_, xs, BP p, e)) = lambdasToString "%"     xs p e
    | exprToString (BE_Sigma  (_, xs, BP p, e)) = sigmasToString  "SIGMA" xs p e
    | exprToString (BE_Pi     (_, xs, BP p, e)) = sigmasToString  "PI"    xs p e
    | exprToString (BE_Inter  (_, xs, BP p, e)) = lambdasToString "INTER" xs p e
    | exprToString (BE_Union  (_, xs, BP p, e)) = lambdasToString "UNION" xs p e

    | exprToString (BE_Struct (_, l)) =
      let
        fun fields [] = raise StringifyError "empty struct"
          | fields [(s, e)] = 
            if
              #1 (priOf e) < 120
            then
              s ^ ":(" ^ (exprToString e) ^ ")"
            else
              s ^ ":"  ^ (exprToString e)
          | fields ((s, e) :: rest) =
            if
              #1 (priOf e) < 120
            then
              s ^ ":(" ^ (exprToString e) ^ "), " ^ (fields rest)
            else
              s ^ ":"  ^ (exprToString e) ^  ", " ^ (fields rest)
      in
        "struct(" ^ (fields l) ^ ")"
      end
    
    | exprToString (BE_Rec (_, l)) =
      let
        fun unwrapLabel NONE = ""
          | unwrapLabel (SOME s) = s ^ ":" 
        fun fields [] = raise StringifyError "empty struct"
          | fields [(sOpt, e)] = 
            if
              #1 (priOf e) < 120
            then
              (unwrapLabel sOpt) ^ "(" ^ (exprToString e) ^ ")"
            else
              (unwrapLabel sOpt) ^       (exprToString e)
          | fields ((sOpt, e) :: rest) =
            if
              #1 (priOf e) < 120
            then
              (unwrapLabel sOpt) ^ "(" ^ (exprToString e) ^ "), " ^ (fields rest)
            else
              (unwrapLabel sOpt) ^       (exprToString e) ^  ", " ^ (fields rest)
      in
        "rec(" ^ (fields l) ^ ")"
      end
    | exprToString (BE_RcAc (_, e, s)) = (exprToString e) ^ s
    | exprToString _ = raise StringifyError "unknown expression"

  and
      sigmasToString kw x p e = kw ^ " " ^ (tokenToString x) ^ ".(" ^ (exprToString p) ^ " | " ^ (exprToString e) ^ ")"
  and
      lambdasToString "%" [x] p e = "%" ^       (tokenToString x) ^       ".(" ^ (exprToString p) ^ " | " ^ (exprToString e) ^ ")"
    | lambdasToString kw  xs  p e = kw  ^ "(" ^ (tokenListToString xs) ^ ").(" ^ (exprToString p) ^ " | " ^ (exprToString e) ^ ")"
  and
      exprListToString el =
      let
        val sl = List.map (fn x => if #1 (priOf x) <= 115 then "(" ^ (exprToString x) ^ ")" else exprToString x) el
      in
        Utils.concatWith ", " sl
      end
  and
      exprListInCaseToString el = Utils.concatWith ", " (List.map exprToString el)
  and
      tokenListToString l = Utils.concatWith ", " (List.map tokenToString l)
  and
      tokenToString (Var l)            = l
    | tokenToString (Renamed (rn, v))  = rn ^ "." ^ v
    | tokenToString (IntegerLiteral n) = IntInf.toString n
    | tokenToString (StringLiteral s)  = "\"" ^ s ^ "\""
    | tokenToString (RealLiteral r)    = BReal.toString r
    | tokenToString (Keyword s)        = s
    | tokenToString (VarLit l)         = l
    | tokenToString (VarSingle l)      = l
  and
      historyToString [] = "/*\n*/\n"
    | historyToString l =
      let
        fun historyToStringAux (b, a, NONE)   = b ^ "@->@" ^ a ^                    "\n"
          | historyToStringAux (b, a, SOME e) = b ^ "@->@" ^ a ^ "@" ^ (exprToString e) ^ "\n"
      in
        "/*\n" ^ (List.foldl (fn (str1, str2) => str1 ^ str2) "" (List.map historyToStringAux l)) ^ "*/\n"
      end
  and
      modelDependenciesToString [] = "/*\n*/\n"
    | modelDependenciesToString l  = "/*\n" ^ (String.concat (List.map (fn s => s ^ "\n") l)) ^ "*/\n"
end


