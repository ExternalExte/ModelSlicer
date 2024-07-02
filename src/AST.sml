datatype BToken = 
  Var            of string
| Renamed        of string * string
| VarLit         of string (* 書き換え・暗黙の条件の導出規則においてリテラルのみにマッチする変数 *)
| VarSingle      of string (* 制限付き変数 (可換で結合的な演算においてただ1個のオペランドにマッチする *)
| VarTypeSet     of string (* 型集合にマッチする変数 *)
| IntegerLiteral of IntInf.int 
| StringLiteral  of string 
| RealLiteral    of BReal.bReal 
| Keyword        of string 
and
  BType = 
  BT_Real
| BT_Integer 
| BT_String 
| BT_Float 
| BT_Bool 
| BT_Power    of BType option 
| BT_Pair     of BType option * BType option 
| BT_Struct   of (BType * string) list 
| BT_Deferred of string 
| BT_Enum     of string * string list 
| BT_Predicate
  (* 関数、関係は BT_Power (SOME BT_Pair _) *)
  (* 集合定数"INTEGER"の型は BT_Power (SOME BT_Integer) *)
and
  BExpr =
  BE_Leaf   of (BType option * BToken)                            (* リテラル, 変数 *)
| BE_Node1  of (BType option * BToken * BExpr)                    (* 単項演算子、card、bool等 *)
| BE_Node2  of (BType option * BToken * BExpr * BExpr)            (* 二項演算式, 2引数組込関数 *)
| BE_NodeN  of (BType option * BToken * BExpr list)               (* son (), bin () *)
| BE_Fnc    of (BType option * BExpr * BExpr)                     (* 関数適用 *)
| BE_Img    of (BType option * BExpr * BExpr)                     (* 像 *)
| BE_Bool   of BPredicate
| BE_ExSet  of (BType option * BExpr list)                        (* 集合の外延表記 *)
| BE_InSet  of (BType option * BToken list * BPredicate)          (* 集合の内包表記 *)
| BE_Seq    of (BType option * BExpr list)                        (* シーケンス *)
| BE_ForAll of (BToken list * BPredicate * BPredicate)
| BE_Exists of (BToken list * BPredicate)
| BE_Lambda of (BType option * BToken list * BPredicate * BExpr)
| BE_Sigma  of (BType option * BToken * BPredicate * BExpr)
| BE_Pi     of (BType option * BToken * BPredicate * BExpr)
| BE_Inter  of (BType option * BToken list * BPredicate * BExpr)  (* Quantified Intersection *)
| BE_Union  of (BType option * BToken list * BPredicate * BExpr)  (* Quantified Union *)
| BE_Struct of BType option * (string * BExpr) list
| BE_Rec    of BType option * (string option * BExpr) list (* *)
| BE_RcAc   of BType option * BExpr * string
| BE_Commutative of (BType option * BToken * BExpr list)          (* 可換演算子 *)
and
  BPredicate = BP of BExpr (* 条件式 *)
and
  (* 制約条件系・Assertion *)
  BClause = 
  BC_CONSTRAINTS of BPredicate 
| BC_PROPERTIES  of BPredicate
| BC_INVARIANT   of BPredicate
| BC_ASSERTIONS  of BPredicate
| BC_VALUES      of (BToken * BExpr) list (* 追加 *)

(* モジュール系 *)
(* モデル展開後にはこれらは登場しない *)
| BC_SEES     of BMchInstanciation list 
| BC_INCLUDES of BMchInstanciation list
| BC_PROMOTES of BMchInstanciation list
| BC_EXTENDS  of BMchInstanciation list
| BC_USES     of BMchInstanciation list
| BC_IMPORTS  of BMchInstanciation list (* 追加 *)

(* 変数導入系 *)
| BC_CCONSTANTS of BToken list
| BC_ACONSTANTS of BToken list
| BC_CVARIABLES of BToken list
| BC_AVARIABLES of BToken list

(* その他 *)
| BC_SETS           of BType list
| BC_INITIALISATION of BSubstitution
| BC_OPERATIONS     of BOperation list
| BC_DEFINITIONS    of BToken list
and
  BComponent = 
  BMch of string * BToken list * BClause list 
| BRef of string * string * BToken list * BClause list 
| BImp of string * string * BToken list * BClause list
and
  (*                  操作名,  outputs,      inputs,       操作 *)
  BOperation = BOp of string * BToken list * BToken list * BSubstitution
and
  BMchInstanciation = BMchInst of BToken * BExpr list
and
  BSubstitution = 
  BS_Block              of BSubstitution (* BEGIN *)
| BS_Identity (* skip *)
| BS_Precondition       of BPredicate * BSubstitution
| BS_Assertion          of BPredicate * BSubstitution
| BS_Choice             of BSubstitution list
| BS_If                 of (BPredicate option * BSubstitution) list (* [(SOME 条件, 代入文)] ELSEのときNONE *)
| BS_Select             of (BPredicate option * BSubstitution) list (* [(SOME 条件, 代入文)] ELSEのときNONE *)
| BS_Case               of BExpr * (BExpr list * BSubstitution) list
| BS_Any                of (BToken list) * BPredicate * BSubstitution
| BS_Let                of (BToken * BExpr) list * BSubstitution
| BS_BecomesElt         of BExpr list * BExpr
| BS_BecomesSuchThat    of (BExpr list) * BPredicate
| BS_Call               of BToken * (BExpr list) * (BExpr list) (* 操作名 (VarかRenamed)、出力パラメータ、入力パラメータ *)
| BS_BecomesEqual       of BExpr * BExpr
| BS_BecomesEqualList   of (BExpr list) * (BExpr list) (* a, b := c, d *)
| BS_Simultaneous       of BSubstitution list
| BS_LocalVariable      of (BToken list) * BSubstitution
| BS_Sequencing         of BSubstitution list
| BS_While              of BPredicate * BSubstitution * BPredicate * BExpr (* WHILE C DO S INVARIANT P VARIANT E END *)

structure AST =
struct
  exception ASTError of string

  fun mapExprTree f (BE_Leaf        (t, token))         = f (BE_Leaf        (t, token))
    | mapExprTree f (BE_Node1       (t, e, x))          = f (BE_Node1       (t, e, mapExprTree f x))
    | mapExprTree f (BE_Node2       (t, e, x, y))       = f (BE_Node2       (t, e, mapExprTree f x, mapExprTree f y))
    | mapExprTree f (BE_Commutative (t, e, l))          = f (BE_Commutative (t, e, List.map (mapExprTree f) l))
    | mapExprTree f (BE_Fnc         (t, g, x))          = f (BE_Fnc         (t, mapExprTree f g, mapExprTree f x))
    | mapExprTree f (BE_Img         (t, g, x))          = f (BE_Img         (t, mapExprTree f g, mapExprTree f x))
    | mapExprTree f (BE_NodeN       (t, token, l))      = f (BE_NodeN       (t, token, List.map (mapExprTree f) l))
    | mapExprTree f (BE_Bool        (BP e))             = f (BE_Bool        (BP (mapExprTree f e)))
    | mapExprTree f (BE_ExSet       (t, l))             = f (BE_ExSet       (t, List.map (mapExprTree f) l))
    | mapExprTree f (BE_InSet       (t, l1, BP e))      = f (BE_InSet       (t, l1, BP (mapExprTree f e)))
    | mapExprTree f (BE_Seq         (t, l))             = f (BE_Seq         (t, List.map (mapExprTree f) l))
    | mapExprTree f (BE_ForAll      (l1, BP e1, BP e2)) = f (BE_ForAll      (l1, BP (mapExprTree f e1), BP (mapExprTree f e2)))
    | mapExprTree f (BE_Lambda      (t, l, BP e1, e2))  = f (BE_Lambda      (t, l, BP (mapExprTree f e1), mapExprTree f e2))
    | mapExprTree f (BE_Exists      (l, BP e))          = f (BE_Exists      (l, BP (mapExprTree f e)))
    | mapExprTree f (BE_Sigma       (t, l, BP e1, e2))  = f (BE_Sigma       (t, l, BP (mapExprTree f e1), mapExprTree f e2))
    | mapExprTree f (BE_Pi          (t, l1, BP e1, e2)) = f (BE_Pi          (t, l1, BP (mapExprTree f e1), mapExprTree f e2))
    | mapExprTree f (BE_Inter       (t, l, BP e1, e2))  = f (BE_Inter       (t, l, BP (mapExprTree f e1), mapExprTree f e2))
    | mapExprTree f (BE_Union       (t, l, BP e1, e2))  = f (BE_Union       (t, l, BP (mapExprTree f e1), mapExprTree f e2))
    | mapExprTree f (BE_Struct      (t, l))             = f (BE_Struct      (t, List.map (fn (s, e) => (s, mapExprTree f e)) l))
    | mapExprTree f (BE_Rec         (t, l))             = f (BE_Rec         (t, List.map (fn (s, e) => (s, mapExprTree f e)) l))
    | mapExprTree f (BE_RcAc        (t, e, s))          = f (BE_RcAc        (t, mapExprTree f e, s))
    
  fun appExprTree f (expr as (BE_Leaf        _                       )) = f expr
    | appExprTree f (expr as (BE_Node1       (_   , _    , e        ))) = (appExprTree f e; f expr)
    | appExprTree f (expr as (BE_Node2       (_   , _    , e1   , e2))) = (appExprTree f e1; appExprTree f e2; f expr)
    | appExprTree f (expr as (BE_Commutative (_   , _    , l        ))) = (List.app (appExprTree f) l; f expr)
    | appExprTree f (expr as (BE_Fnc         (_   , e1   , e2       ))) = (appExprTree f e1; appExprTree f e2; f expr)
    | appExprTree f (expr as (BE_Img         (_   , e1   , e2       ))) = (appExprTree f e1; appExprTree f e2; f expr)
    | appExprTree f (expr as (BE_NodeN       (_   , _    , l        ))) = (List.app (appExprTree f) l; f expr)
    | appExprTree f (expr as (BE_Bool        (BP e                  ))) = (appExprTree f e; f expr)
    | appExprTree f (expr as (BE_ExSet       (_   , l               ))) = (List.app (appExprTree f) l; f expr)
    | appExprTree f (expr as (BE_InSet       (_   , _    , BP e     ))) = (appExprTree f e; f expr)
    | appExprTree f (expr as (BE_Seq         (_   , l               ))) = (List.app (appExprTree f) l; f expr)
    | appExprTree f (expr as (BE_ForAll      (_   , BP e1, BP e2    ))) = (appExprTree f e1; appExprTree f e2; f expr)
    | appExprTree f (expr as (BE_Lambda      (_   , _    , BP e1, e2))) = (appExprTree f e1; appExprTree f e2; f expr)
    | appExprTree f (expr as (BE_Exists      (_   , BP e            ))) = (appExprTree f e; f expr)
    | appExprTree f (expr as (BE_Sigma       (_   , _    , BP e1, e2))) = (appExprTree f e1; appExprTree f e2; f expr)
    | appExprTree f (expr as (BE_Pi          (_   , _    , BP e1, e2))) = (appExprTree f e1; appExprTree f e2; f expr)
    | appExprTree f (expr as (BE_Inter       (_   , _    , BP e1, e2))) = (appExprTree f e1; appExprTree f e2; f expr)
    | appExprTree f (expr as (BE_Union       (_   , _    , BP e1, e2))) = (appExprTree f e1; appExprTree f e2; f expr)
    | appExprTree f (expr as (BE_Struct      (_   , l               ))) = (List.app (fn (_, e) => appExprTree f e) l; f expr)
    | appExprTree f (expr as (BE_Rec         (_   , l               ))) = (List.app (fn (_, e) => appExprTree f e) l; f expr)
    | appExprTree f (expr as (BE_RcAc        (_   , e    , s        ))) = (appExprTree f e; f expr)

  fun subExprTrees (BE_Leaf        (t, token))         = [] : BExpr list
    | subExprTrees (BE_Node1       (t, e, x))          = [x]
    | subExprTrees (BE_Node2       (t, e, x, y))       = [x, y]
    | subExprTrees (BE_Commutative (t, e, l))          = l
    | subExprTrees (BE_Fnc         (t, g, x))          = [g, x]
    | subExprTrees (BE_Img         (t, g, x))          = [g, x]
    | subExprTrees (BE_NodeN       (t, token, l))      = l
    | subExprTrees (BE_Bool        (BP x))             = [x]
    | subExprTrees (BE_ExSet       (t, l))             = l
    | subExprTrees (BE_InSet       (t, l1, BP x))      = [x]
    | subExprTrees (BE_Seq         (t, l))             = l
    | subExprTrees (BE_ForAll      (l1, BP x1, BP x2)) = [x1, x2]
    | subExprTrees (BE_Lambda      (t, l1, BP x, e))   = [x, e]
    | subExprTrees (BE_Exists      (l1, BP x))         = [x]
    | subExprTrees (BE_Sigma       (t, l1, BP x, e))   = [x, e]
    | subExprTrees (BE_Pi          (t, l1, BP x, e))   = [x, e]
    | subExprTrees (BE_Inter       (t, l1, BP x, e))   = [x, e]
    | subExprTrees (BE_Union       (t, l1, BP x, e))   = [x, e]
    | subExprTrees (BE_Struct      (t, l))             = List.map (fn (s, e) => e) l
    | subExprTrees (BE_Rec         (t, l))             = List.map (fn (s, e) => e) l
    | subExprTrees (BE_RcAc        (t, e, s))          = [e]

  fun findExprTree f e = 
      if
        f e
      then 
        SOME e 
      else 
        let
          val tmp = List.find (Utils.neqto NONE) (List.map (findExprTree f) (subExprTrees e))
        in
          case tmp of
            NONE => NONE
          | SOME x => x
        end

  fun findExprs f e = 
      let
        val tmp = List.concat (List.map (findExprs f) (subExprTrees e))
      in
        if
          f e
        then
          e :: tmp
        else
          tmp
      end


  (* 代入文の書き換え用 *)
  fun mapSubstitutionTree f (BS_Block s)                     = f (BS_Block (mapSubstitutionTree f s))    
    | mapSubstitutionTree f BS_Identity                      = f BS_Identity
    | mapSubstitutionTree f (BS_Precondition (p, s))         = f (BS_Precondition (p, mapSubstitutionTree f s))
    | mapSubstitutionTree f (BS_Assertion (p, s))            = f (BS_Assertion (p, mapSubstitutionTree f s))
    | mapSubstitutionTree f (BS_Choice ss)                   = f (BS_Choice (List.map (mapSubstitutionTree f) ss))
    | mapSubstitutionTree f (BS_If l)                        = f (BS_If (List.map (fn (po, s) => (po, mapSubstitutionTree f s)) l))
    | mapSubstitutionTree f (BS_Select l)                    = f (BS_Select (List.map (fn (po, s) => (po, mapSubstitutionTree f s)) l))
    | mapSubstitutionTree f (BS_Case (e, l))                 = f (BS_Case (e, List.map (fn (es, s) => (es, mapSubstitutionTree f s)) l))
    | mapSubstitutionTree f (BS_Any (ts, p, s))              = f (BS_Any (ts, p, mapSubstitutionTree f s))
    | mapSubstitutionTree f (BS_Let (l, s))                  = f (BS_Let (l, mapSubstitutionTree f s))
    | mapSubstitutionTree f (BS_BecomesElt (el, e))          = f (BS_BecomesElt (el, e))
    | mapSubstitutionTree f (BS_BecomesSuchThat (es, p))     = f (BS_BecomesSuchThat (es, p))
    | mapSubstitutionTree f (BS_Call (t, es1, es2))          = f (BS_Call (t, es1, es2))
    | mapSubstitutionTree f (BS_BecomesEqual (e1, e2))       = f (BS_BecomesEqual (e1, e2))
    | mapSubstitutionTree f (BS_BecomesEqualList (es1, es2)) = f (BS_BecomesEqualList (es1, es2))
    | mapSubstitutionTree f (BS_Simultaneous ss)             = f (BS_Simultaneous (List.map (mapSubstitutionTree f) ss))
    | mapSubstitutionTree f (BS_LocalVariable (tks, s))      = f (BS_LocalVariable (tks, mapSubstitutionTree f s))
    | mapSubstitutionTree f (BS_Sequencing sl)               = f (BS_Sequencing (List.map (mapSubstitutionTree f) sl))
    | mapSubstitutionTree f (BS_While (p1, s, p2, e))        = f (BS_While (p1, mapSubstitutionTree f s, p2, e))

  fun subSubstitutionTrees (BS_Block s) = [s]
    | subSubstitutionTrees (BS_Precondition (_, s)) = [s]
    | subSubstitutionTrees (BS_Assertion (_, s)) = [s]
    | subSubstitutionTrees (BS_Choice ss) = ss
    | subSubstitutionTrees (BS_If l) = List.map (fn (_, s) => s) l
    | subSubstitutionTrees (BS_Select l) = List.map (fn (_, s) => s) l
    | subSubstitutionTrees (BS_Case (_, l)) = List.map (fn (_, s) => s) l
    | subSubstitutionTrees (BS_Any (_, _, s)) = [s]
    | subSubstitutionTrees (BS_Let (_, s)) = [s]
    | subSubstitutionTrees (BS_Simultaneous ss) = ss
    | subSubstitutionTrees (BS_LocalVariable (_, s)) = [s]
    | subSubstitutionTrees (BS_Sequencing ss) = ss
    | subSubstitutionTrees (BS_While (_, s, _, _)) = [s]
    | subSubstitutionTrees _ = []

  fun findSubstitutionTree f s =
      if
        f s
      then
        SOME s
      else
        let
          val tmp = List.find (Utils.neqto NONE) (List.map (findSubstitutionTree f) (subSubstitutionTrees s))
        in
          case tmp of
            NONE => NONE
          | SOME x => x
        end

  fun findSubstitutions f s = 
      let
        val tmp = List.concat (List.map (findSubstitutions f) (subSubstitutionTrees s))
      in
        if
          f s
        then
          s :: tmp
        else
          tmp
      end

  fun appSubstitutionTree f (sbst as (BS_Block            s           )) = (appSubstitutionTree f s; f sbst)
    | appSubstitutionTree f (sbst as (BS_Precondition     (_, s      ))) = (appSubstitutionTree f s; f sbst)
    | appSubstitutionTree f (sbst as (BS_Assertion        (_, s      ))) = (appSubstitutionTree f s; f sbst)
    | appSubstitutionTree f (sbst as (BS_Choice           l           )) = (List.app (appSubstitutionTree f) l; f sbst)
    | appSubstitutionTree f (sbst as (BS_If               l           )) = (List.app (fn (_, s) => appSubstitutionTree f s) l; f sbst)
    | appSubstitutionTree f (sbst as (BS_Select           l           )) = (List.app (fn (_, s) => appSubstitutionTree f s) l; f sbst)
    | appSubstitutionTree f (sbst as (BS_Case             (_, l      ))) = (List.app (fn (_, s) => appSubstitutionTree f s) l; f sbst)
    | appSubstitutionTree f (sbst as (BS_Any              (_, _, s   ))) = (appSubstitutionTree f s; f sbst)
    | appSubstitutionTree f (sbst as (BS_Let              (_, s      ))) = (appSubstitutionTree f s; f sbst)
    | appSubstitutionTree f (sbst as (BS_Simultaneous     l           )) = (List.app (appSubstitutionTree f) l; f sbst)
    | appSubstitutionTree f (sbst as (BS_LocalVariable    (_, s      ))) = (appSubstitutionTree f s; f sbst)
    | appSubstitutionTree f (sbst as (BS_Sequencing       l           )) = (List.app (appSubstitutionTree f) l; f sbst)
    | appSubstitutionTree f (sbst as (BS_While            (_, s, _, _))) = (appSubstitutionTree f s; f sbst)
    | appSubstitutionTree f sbst                                         = f sbst

  fun mapSubstitutionsInOperation f (BOp (opname, inps, outps, s)) = BOp (opname, inps, outps, mapSubstitutionTree f s)

  fun mapSubstitutionsInClause f (BC_OPERATIONS os)    = BC_OPERATIONS (List.map (mapSubstitutionsInOperation f) os)
    | mapSubstitutionsInClause f (BC_INITIALISATION s) = BC_INITIALISATION (mapSubstitutionTree f s)
    | mapSubstitutionsInClause _ c = c

  fun mapSubstitutionsInComponent f (BMch (mchName,          prms, clauses)) = BMch (mchName,          prms, List.map (mapSubstitutionsInClause f) clauses)
    | mapSubstitutionsInComponent f (BRef (refName, mchName, prms, clauses)) = BRef (refName, mchName, prms, List.map (mapSubstitutionsInClause f) clauses)
    | mapSubstitutionsInComponent f (BImp (impName, mchName, prms, clauses)) = BImp (impName, mchName, prms, List.map (mapSubstitutionsInClause f) clauses)

  (* 式の書き換え用 *)
  fun mapExprsInPredicate f (BP e) = BP (mapExprTree f e)

  fun mapExprsInSubstitutionTree f (BS_Block s)                     = BS_Block (mapExprsInSubstitutionTree f s)    
    | mapExprsInSubstitutionTree f BS_Identity                      = BS_Identity
    | mapExprsInSubstitutionTree f (BS_Precondition (p, s))         = BS_Precondition (mapExprsInPredicate f p, mapExprsInSubstitutionTree f s)
    | mapExprsInSubstitutionTree f (BS_Assertion (p, s))            = BS_Assertion (mapExprsInPredicate f p, mapExprsInSubstitutionTree f s)
    | mapExprsInSubstitutionTree f (BS_Choice ss)                   = BS_Choice (List.map (mapExprsInSubstitutionTree f) ss)
    | mapExprsInSubstitutionTree f (BS_If l)                        = BS_If (List.map (fn (SOME p, s) => (SOME (mapExprsInPredicate f p), mapExprsInSubstitutionTree f s) | (NONE, s) => (NONE, mapExprsInSubstitutionTree f s)) l)
    | mapExprsInSubstitutionTree f (BS_Select l)                    = BS_Select (List.map (fn (SOME p, s) => (SOME (mapExprsInPredicate f p), mapExprsInSubstitutionTree f s) | (NONE, s) => (NONE, mapExprsInSubstitutionTree f s)) l)
    | mapExprsInSubstitutionTree f (BS_Case (e, l))                 = BS_Case (mapExprTree f e, List.map (fn (es, s) => (List.map (mapExprTree f) es, mapExprsInSubstitutionTree f s)) l)
    | mapExprsInSubstitutionTree f (BS_Any (ts, p, s))              = BS_Any (ts, mapExprsInPredicate f p, mapExprsInSubstitutionTree f s)
    | mapExprsInSubstitutionTree f (BS_Let (l, s))                  = BS_Let (List.map (fn (var, e) => (var, mapExprTree f e)) l, mapExprsInSubstitutionTree f s)
    | mapExprsInSubstitutionTree f (BS_BecomesElt (el, e))         = BS_BecomesElt (List.map (mapExprTree f) el, mapExprTree f e)
    | mapExprsInSubstitutionTree f (BS_BecomesSuchThat (es, p))     = BS_BecomesSuchThat (List.map (mapExprTree f) es, mapExprsInPredicate f p)
    | mapExprsInSubstitutionTree f (BS_Call (t, es1, es2))          = BS_Call (t, List.map (mapExprTree f) es1, List.map (mapExprTree f) es2)
    | mapExprsInSubstitutionTree f (BS_BecomesEqual (e1, e2))       = BS_BecomesEqual (mapExprTree f e1, mapExprTree f e2)
    | mapExprsInSubstitutionTree f (BS_BecomesEqualList (es1, es2)) = BS_BecomesEqualList (List.map (mapExprTree f) es1, List.map (mapExprTree f) es2)
    | mapExprsInSubstitutionTree f (BS_Simultaneous ss)             = BS_Simultaneous (List.map (mapExprsInSubstitutionTree f) ss)
    | mapExprsInSubstitutionTree f (BS_LocalVariable (tks, s))      = BS_LocalVariable (tks, mapExprsInSubstitutionTree f s)
    | mapExprsInSubstitutionTree f (BS_Sequencing ss)               = BS_Sequencing (List.map (mapExprsInSubstitutionTree f) ss)
    | mapExprsInSubstitutionTree f (BS_While (BP e1, s, BP e2, e3)) = BS_While (BP (mapExprTree f e1), mapExprsInSubstitutionTree f s, BP (mapExprTree f e2), mapExprTree f e3)

  fun mapExprsInOperation f (BOp (opname, inps, outps, s)) = BOp (opname, inps, outps, mapExprsInSubstitutionTree f s)

  fun mapExprsInClause f (BC_CONSTRAINTS p) = BC_CONSTRAINTS (mapExprsInPredicate f p)
    | mapExprsInClause f (BC_PROPERTIES p)  = BC_PROPERTIES  (mapExprsInPredicate f p)
    | mapExprsInClause f (BC_INVARIANT p)   = BC_INVARIANT   (mapExprsInPredicate f p)
    | mapExprsInClause f (BC_ASSERTIONS p)  = BC_ASSERTIONS  (mapExprsInPredicate f p)
    | mapExprsInClause f (BC_VALUES l)      = BC_VALUES      (List.map (fn (v, e) => (v, mapExprTree f e)) l)

    | mapExprsInClause f (BC_SEES l)     = BC_SEES     (List.map (fn (BMchInst (x, es)) => BMchInst (x, List.map (mapExprTree f) es)) l)
    | mapExprsInClause f (BC_INCLUDES l) = BC_INCLUDES (List.map (fn (BMchInst (x, es)) => BMchInst (x, List.map (mapExprTree f) es)) l)
    | mapExprsInClause f (BC_PROMOTES l) = BC_PROMOTES (List.map (fn (BMchInst (x, es)) => BMchInst (x, List.map (mapExprTree f) es)) l)
    | mapExprsInClause f (BC_EXTENDS l)  = BC_EXTENDS  (List.map (fn (BMchInst (x, es)) => BMchInst (x, List.map (mapExprTree f) es)) l)
    | mapExprsInClause f (BC_USES l)     = BC_USES     (List.map (fn (BMchInst (x, es)) => BMchInst (x, List.map (mapExprTree f) es)) l)
    | mapExprsInClause f (BC_IMPORTS l)  = BC_IMPORTS  (List.map (fn (BMchInst (x, es)) => BMchInst (x, List.map (mapExprTree f) es)) l)

    | mapExprsInClause f (BC_INITIALISATION s) = BC_INITIALISATION (mapExprsInSubstitutionTree f s)
    | mapExprsInClause f (BC_OPERATIONS os) = BC_OPERATIONS (List.map (mapExprsInOperation f) os)
    | mapExprsInClause _ x = x

  fun mapExprsInComponent f (BMch (mchName,          prms, clauses)) = BMch (mchName,          prms, List.map (mapExprsInClause f) clauses)
    | mapExprsInComponent f (BRef (refName, mchName, prms, clauses)) = BRef (refName, mchName, prms, List.map (mapExprsInClause f) clauses)
    | mapExprsInComponent f (BImp (impName, mchName, prms, clauses)) = BImp (impName, mchName, prms, List.map (mapExprsInClause f) clauses)

  fun identExistsInExpr (BE_Leaf (to, tk)) v = (v = tk)
    | identExistsInExpr (BE_Node1 (to, operator, e)) v = identExistsInExpr e v
    | identExistsInExpr (BE_Node2 (to, operator, e1, e2)) v =
        (identExistsInExpr e1 v) orelse (identExistsInExpr e2 v)
    | identExistsInExpr (BE_NodeN (to, operator, el)) v = List.exists (fn e => identExistsInExpr e v) el
    | identExistsInExpr (BE_Fnc (to, e1, e2)) v =
      (identExistsInExpr e1 v) orelse (identExistsInExpr e2 v)
    | identExistsInExpr (BE_Img (to, e1, e2)) v =
        (identExistsInExpr e1 v) orelse (identExistsInExpr e2 v)
    | identExistsInExpr (BE_Bool (BP e)) v = identExistsInExpr e v
    | identExistsInExpr (BE_ExSet (to, el)) v = List.exists (fn e => identExistsInExpr e v) el
    | identExistsInExpr (BE_InSet (to, tl, BP e)) v =
        (List.exists (Utils.eqto v) tl) orelse identExistsInExpr e v
    | identExistsInExpr (BE_Seq (to, el)) v = List.exists (fn e => identExistsInExpr e v) el
    | identExistsInExpr (BE_ForAll (tl, BP e1, BP e2)) v =
        (List.exists (Utils.eqto v) tl) orelse (identExistsInExpr e1 v) orelse (identExistsInExpr e2 v)
    | identExistsInExpr (BE_Exists (tl, BP e)) v =
        (List.exists (Utils.eqto v) tl) orelse identExistsInExpr e v
    | identExistsInExpr (BE_Lambda (to, tl, BP e1, e2)) v =
        (List.exists (Utils.eqto v) tl) orelse (identExistsInExpr e1 v) orelse (identExistsInExpr e2 v)
    | identExistsInExpr (BE_Sigma (to, t, BP e1, e2)) v =
        (t = v) orelse (identExistsInExpr e1 v) orelse (identExistsInExpr e2 v)
    | identExistsInExpr (BE_Pi (to, t, BP e1, e2)) v =
        (t = v) orelse (identExistsInExpr e1 v) orelse (identExistsInExpr e2 v)
    | identExistsInExpr (BE_Inter (to, tl, BP e1, e2)) v =
        (List.exists (Utils.eqto v) tl) orelse (identExistsInExpr e1 v) orelse (identExistsInExpr e2 v)
    | identExistsInExpr (BE_Union (to, tl, BP e1, e2)) v =
        (List.exists (Utils.eqto v) tl) orelse (identExistsInExpr e1 v) orelse (identExistsInExpr e2 v)
    | identExistsInExpr (BE_Struct (to, l)) v = List.exists (fn (str, e) => identExistsInExpr e v) l
    | identExistsInExpr (BE_Rec (to, l)) v = List.exists (fn (_, e) => identExistsInExpr e v) l
    | identExistsInExpr (BE_RcAc (to, e, str)) v = identExistsInExpr e v
    | identExistsInExpr (BE_Commutative (to, operator, el)) v = List.exists (fn e => identExistsInExpr e v) el
  
  fun identExistsInSubstitution (BS_Block s) v = identExistsInSubstitution s v
    | identExistsInSubstitution BS_Identity v = false
    | identExistsInSubstitution (BS_Precondition (BP e, s)) v =
      let
        val re = identExistsInExpr e v
        val rs = identExistsInSubstitution s v
      in
        re orelse rs
      end
    | identExistsInSubstitution (BS_Assertion (BP e, s)) v =
      let
        val re = identExistsInExpr e v
        val rs = identExistsInSubstitution s v
      in
        re orelse rs
      end
    | identExistsInSubstitution (BS_Choice ss) v = List.exists (fn s => identExistsInSubstitution s v) ss
    | identExistsInSubstitution (BS_If l) v =
      List.exists (fn (NONE, s) => identExistsInSubstitution s v | (SOME (BP e), s) => (identExistsInExpr e v) orelse (identExistsInSubstitution s v)) l
    | identExistsInSubstitution (BS_Select l) v =
      List.exists (fn (NONE, s) => identExistsInSubstitution s v | (SOME (BP e), s) => (identExistsInExpr e v) orelse (identExistsInSubstitution s v)) l
    | identExistsInSubstitution (BS_Case (e1, l)) v =
      let
        val re1 = identExistsInExpr e1 v
        val rl = List.exists (fn (el, s) => (List.exists (fn e => identExistsInExpr e v) el) orelse identExistsInSubstitution s v) l
      in
        re1 orelse rl
      end
    | identExistsInSubstitution (BS_Any (tl, BP e, s)) v =
        (List.exists (Utils.eqto v) tl) orelse (identExistsInExpr e v) orelse (identExistsInSubstitution s v)
    | identExistsInSubstitution (BS_Let (l, s)) v =
        List.exists (fn (var, e) => var = v) l orelse (List.exists (fn (str, e) => identExistsInExpr e v) l) orelse (identExistsInSubstitution s v)
    | identExistsInSubstitution (BS_BecomesElt (el, e)) v =
        (List.exists (fn x => identExistsInExpr x v) el) orelse (identExistsInExpr e v)
    | identExistsInSubstitution (BS_BecomesSuchThat (el, BP e1)) v =
        (List.exists (fn e => identExistsInExpr e v) el) orelse (identExistsInExpr e1 v)
    | identExistsInSubstitution (BS_Call (opName, el1, el2)) v =
        List.exists (fn e => identExistsInExpr e v) (el1 @ el2)
    | identExistsInSubstitution (BS_BecomesEqual (e1, e2)) v = (identExistsInExpr e1 v) orelse (identExistsInExpr e2 v)
    | identExistsInSubstitution (BS_BecomesEqualList (el1, el2)) v =
        List.exists (fn e => identExistsInExpr e v) (el1 @ el2)
    | identExistsInSubstitution (BS_Simultaneous sl) v = List.exists (fn s => identExistsInSubstitution s v) sl
    | identExistsInSubstitution (BS_LocalVariable (tl, s)) v =
        (List.exists (Utils.eqto v) tl) orelse identExistsInSubstitution s v
    | identExistsInSubstitution (BS_Sequencing sl) v = List.exists (fn s => identExistsInSubstitution s v) sl
    | identExistsInSubstitution (BS_While (BP e1, s, BP e2, e3)) v =
        (identExistsInExpr e1 v) orelse (identExistsInSubstitution s v) orelse (identExistsInExpr e2 v) orelse (identExistsInExpr e3 v)

(* Renamed ←→ Varの変換用 *)
  fun mapVarsInExpr f (BE_Leaf (to, tk)) = BE_Leaf (to, f tk)
    | mapVarsInExpr f (BE_InSet (to, vl, p)) = BE_InSet (to, List.map f vl, p)
    | mapVarsInExpr f (BE_ForAll (vl, p1, p2)) = BE_ForAll (List.map f vl, p1, p2)
    | mapVarsInExpr f (BE_Exists (vl, p)) = BE_Exists (List.map f vl, p)
    | mapVarsInExpr f (BE_Lambda (to, vl, p, e)) = BE_Lambda (to, List.map f vl, p, e)
    | mapVarsInExpr f (BE_Sigma (to, t, p, e)) = BE_Sigma (to, f t, p, e)
    | mapVarsInExpr f (BE_Pi (to, t, p, e)) = BE_Pi (to, f t, p, e)
    | mapVarsInExpr f (BE_Inter (to, tl, p, e)) = BE_Inter (to, List.map f tl, p, e)
    | mapVarsInExpr f (BE_Union (to, tl, p, e)) = BE_Union (to, List.map f tl, p, e)
    | mapVarsInExpr _ e = e

  fun mapVarsInMachineInst f (BMchInst (v, el)) = BMchInst (f v, List.map (mapVarsInExpr f) el)
  
  fun mapVarsInSubstitution f (BS_Any           (tl, p, s))             = BS_Any (List.map f tl, p, s)
    | mapVarsInSubstitution f (BS_Let           (l,  s))                = BS_Let (List.map (fn (v, e) => (f v, mapVarsInExpr f e)) l, s)
    | mapVarsInSubstitution f (BS_LocalVariable (tl, s))                = BS_LocalVariable (List.map f tl, s)
    | mapVarsInSubstitution f (BS_Call          (opr, outputs, inputs)) = BS_Call (f opr, List.map (mapVarsInExpr f) outputs, List.map (mapExprTree (mapVarsInExpr f)) inputs)
    | mapVarsInSubstitution f s                                         = s
    
  fun mapVarsInOperation f (BOp (oprName, outputs, inputs, s)) = BOp (oprName , List.map f outputs, List.map f inputs, mapSubstitutionTree (mapVarsInSubstitution f) (mapExprsInSubstitutionTree (mapVarsInExpr f) s))

  fun mapVarsInClause f (BC_CONSTRAINTS (BP e)) = BC_CONSTRAINTS (BP (mapExprTree (mapVarsInExpr f) e))
    | mapVarsInClause f (BC_PROPERTIES  (BP e)) = BC_PROPERTIES  (BP (mapExprTree (mapVarsInExpr f) e))
    | mapVarsInClause f (BC_INVARIANT   (BP e)) = BC_INVARIANT   (BP (mapExprTree (mapVarsInExpr f) e))
    | mapVarsInClause f (BC_ASSERTIONS  (BP e)) = BC_ASSERTIONS  (BP (mapExprTree (mapVarsInExpr f) e))

    | mapVarsInClause f (BC_VALUES l) = BC_VALUES (List.map (fn (v, e) => (f v, mapExprTree (mapVarsInExpr f) e)) l)

    | mapVarsInClause f (BC_SEES     ml) = BC_SEES     (List.map (mapVarsInMachineInst f) ml)
    | mapVarsInClause f (BC_INCLUDES ml) = BC_INCLUDES (List.map (mapVarsInMachineInst f) ml)
    | mapVarsInClause f (BC_PROMOTES ml) = BC_PROMOTES (List.map (mapVarsInMachineInst f) ml)
    | mapVarsInClause f (BC_EXTENDS  ml) = BC_EXTENDS  (List.map (mapVarsInMachineInst f) ml)
    | mapVarsInClause f (BC_USES     ml) = BC_USES     (List.map (mapVarsInMachineInst f) ml)
    | mapVarsInClause f (BC_IMPORTS  ml) = BC_IMPORTS  (List.map (mapVarsInMachineInst f) ml)

    | mapVarsInClause f (BC_CCONSTANTS l) = BC_CCONSTANTS (List.map f l)
    | mapVarsInClause f (BC_ACONSTANTS l) = BC_ACONSTANTS (List.map f l)
    | mapVarsInClause f (BC_CVARIABLES l) = BC_CVARIABLES (List.map f l)
    | mapVarsInClause f (BC_AVARIABLES l) = BC_AVARIABLES (List.map f l)

    | mapVarsInClause f (BC_INITIALISATION s) = BC_INITIALISATION (mapSubstitutionTree (mapVarsInSubstitution f) (mapExprsInSubstitutionTree (mapVarsInExpr f) s))
    | mapVarsInClause f (BC_OPERATIONS l) = BC_OPERATIONS (List.map (mapVarsInOperation f) l)

    | mapVarsInClause f c = c

  fun mapVarsInComponent f (BMch (mchName,          prms, clauses)) = BMch (mchName,          List.map f prms, List.map (mapVarsInClause f) clauses)
    | mapVarsInComponent f (BRef (refName, mchName, prms, clauses)) = BRef (refName, mchName, List.map f prms, List.map (mapVarsInClause f) clauses)
    | mapVarsInComponent f (BImp (impName, mchName, prms, clauses)) = BImp (impName, mchName, List.map f prms, List.map (mapVarsInClause f) clauses)

  (* 識別子の書き換え用 *)
  fun mapIdsInToken f (Var x) = Var (f x)
    | mapIdsInToken _ other   = other

  fun mapIdsInExpr f (BE_Leaf   (to, v))                = BE_Leaf   (to, mapIdsInToken f v)
    | mapIdsInExpr f (BE_InSet  (to, vl,    BP e))      = BE_InSet  (to, List.map (mapIdsInToken f) vl, BP e)
    | mapIdsInExpr f (BE_ForAll (vl, BP e1, BP e2))     = BE_ForAll (List.map (mapIdsInToken f) vl, BP e1, BP e2)
    | mapIdsInExpr f (BE_Exists (vl, BP e))             = BE_Exists (List.map (mapIdsInToken f) vl, BP e)
    | mapIdsInExpr f (BE_Lambda (to, vl,    BP e1, e2)) = BE_Lambda (to, List.map (mapIdsInToken f) vl, BP e1, e2)
    | mapIdsInExpr f (BE_Sigma  (to, t,     BP e1, e2)) = BE_Sigma  (to, mapIdsInToken f t, BP e1, e2)
    | mapIdsInExpr f (BE_Pi     (to, t,     BP e1, e2)) = BE_Pi     (to, mapIdsInToken f t, BP e1, e2)
    | mapIdsInExpr f (BE_Inter  (to, tl,    BP e1, e2)) = BE_Inter  (to, List.map (mapIdsInToken f) tl, BP e1, e2)
    | mapIdsInExpr f (BE_Union  (to, tl,    BP e1, e2)) = BE_Union  (to, List.map (mapIdsInToken f) tl, BP e1, e2)
    | mapIdsInExpr f (BE_Struct (to, l))                = BE_Struct (to, List.map (fn (str, e) => (f str, e)) l)
    | mapIdsInExpr f (BE_Rec    (to, l))                = BE_Rec    (to, List.map (fn (NONE, e) => (NONE, e) | (SOME x, e) => (SOME (f x), e)) l)
    | mapIdsInExpr f (BE_RcAc   (to, e,     s))         = BE_RcAc   (to, e, f s)
    | mapIdsInExpr f e                                  = e

  fun mapIdsInSubstitutionTree f (BS_Any           (tl, p, s)) = BS_Any (List.map (mapIdsInToken f) tl, p, s)
    | mapIdsInSubstitutionTree f (BS_Let           (l,  s))    = BS_Let (List.map (fn (v, e) => (mapIdsInToken f v, e)) l, s)
    | mapIdsInSubstitutionTree f (BS_LocalVariable (tl, s))    = BS_LocalVariable (List.map (mapIdsInToken f) tl, s)
    | mapIdsInSubstitutionTree f s                             = mapExprsInSubstitutionTree (mapIdsInExpr f) s (* BS_Call の操作名は書き換えない *)

  fun mapIdsInTypeTree f (BT_Deferred x)  = BT_Deferred (f x)
    | mapIdsInTypeTree f (BT_Enum (x, l)) = BT_Enum (f x, List.map f l)
    | mapIdsInTypeTree f (BT_Power (SOME t)) = BT_Power (SOME (mapIdsInTypeTree f t))
    | mapIdsInTypeTree f (BT_Pair (SOME t1, SOME t2)) = BT_Pair (SOME (mapIdsInTypeTree f t1), SOME (mapIdsInTypeTree f t2))
    | mapIdsInTypeTree f t                = t

  fun mapIdsInOperation f (BOp (oprName, oparams, iparams, s)) =
      BOp (oprName, List.map (mapIdsInToken f) oparams, List.map (mapIdsInToken f) iparams, mapIdsInSubstitutionTree f s)

  fun mapIdsInClause f (BC_SETS       l)     = BC_SETS (List.map (mapIdsInTypeTree f) l)
    | mapIdsInClause f (BC_ACONSTANTS l)     = BC_ACONSTANTS (List.map (mapIdsInToken f) l)
    | mapIdsInClause f (BC_CCONSTANTS l)     = BC_CCONSTANTS (List.map (mapIdsInToken f) l)
    | mapIdsInClause f (BC_VALUES     l)     = BC_VALUES     (List.map (fn (v, e) => (mapIdsInToken f v, mapIdsInExpr f e)) l)
    | mapIdsInClause f (BC_AVARIABLES l)     = BC_AVARIABLES (List.map (mapIdsInToken f) l)
    | mapIdsInClause f (BC_CVARIABLES l)     = BC_CVARIABLES (List.map (mapIdsInToken f) l)
    | mapIdsInClause f (BC_OPERATIONS l)     = BC_OPERATIONS (List.map (mapIdsInOperation f) l)
    | mapIdsInClause f (BC_INITIALISATION s) = BC_INITIALISATION (mapIdsInSubstitutionTree f s)
    | mapIdsInClause f x                     = mapExprsInClause (mapIdsInExpr f) x

  fun mapIdsInComponent f (BMch (mchName,          prms, clauses)) = BMch (mchName,          List.map (mapIdsInToken f) prms, List.map (mapIdsInClause f) clauses)
    | mapIdsInComponent f (BRef (refName, mchName, prms, clauses)) = BRef (refName, mchName, List.map (mapIdsInToken f) prms, List.map (mapIdsInClause f) clauses)
    | mapIdsInComponent f (BImp (impName, mchName, prms, clauses)) = BImp (impName, mchName, List.map (mapIdsInToken f) prms, List.map (mapIdsInClause f) clauses)


  (* 仮の変数名用の番号を生成 *)
  val count_ = ref 0
  fun genInt () =
      let
        val ret = (!count_)
        val _ = (count_ := ret + 1)
      in
        ret
      end

   fun genString () = Int.toString (genInt ())
   
   fun genStringList 0 = []
     | genStringList n = (genString ()) :: (genStringList (n - 1))

  (* 型は無視する式の等価性判定 (a + b = b + a) *)
  (* 空のコメントをつけた式は局所変数関連で改善が必要 *)
  (* 変数名の重複はないと仮定する *) (* ←重複解消前に使わないこと *)
  fun eqExprs (BE_Leaf        (_    , tk1                     )) (BE_Leaf        (_    , tk2                     )) = (tk1 = tk2) 
    | eqExprs (BE_Node1       (_    , tk1        , e1         )) (BE_Node1       (_    , tk2        , e2         )) = (tk1 = tk2) andalso (eqExprs e1 e2) 
    | eqExprs (BE_Node2       (_    , Keyword "=", e11   , e12)) (BE_Node2       (_    , Keyword "=", e21   , e22)) = ((eqExprs e11 e21) andalso (eqExprs e12 e22)) orelse ((eqExprs e12 e21) andalso (eqExprs e11 e22))
    | eqExprs (BE_Node2       (_    , tk1        , e11   , e12)) (BE_Node2       (_    , tk2        , e21   , e22)) = (tk1 = tk2) andalso (eqExprs e11 e21) andalso (eqExprs e12 e22)
    | eqExprs (BE_NodeN       (_    , tk1        , es1        )) (BE_NodeN       (_    , tk2        , es2        )) = (tk1 = tk2) andalso ListPair.allEq (Utils.uncurry eqExprs) (es1, es2)
    | eqExprs (BE_Fnc         (_    , e11        , e12        )) (BE_Fnc         (_    , e21        , e22        )) = (eqExprs e11 e21) andalso (eqExprs e12 e22)
    | eqExprs (BE_Img         (_    , e11        , e12        )) (BE_Img         (_    , e21        , e22        )) = (eqExprs e11 e21) andalso (eqExprs e12 e22)
    | eqExprs (BE_Bool        (BP e1                          )) (BE_Bool        (BP e2                          )) = eqExprs e1 e2
    | eqExprs (BE_ExSet       (_    , es1                     )) (BE_ExSet       (_    , es2                     )) = Utils.eqAsSet eqExprs es1 es2
    | eqExprs (BE_InSet       (_    , tks1       , BP e1      )) (BE_InSet       (_    , tks2       , BP e2      )) = eqExprListUsingLocalVar tks1  [e1]       tks2  [e2]
    | eqExprs (BE_Seq         (_    , es1                     )) (BE_Seq         (_    , es2                     )) = ListPair.allEq (Utils.uncurry eqExprs) (es1, es2)
    | eqExprs (BE_ForAll      (tks1 , BP e11     , BP e12     )) (BE_ForAll      (tks2 , BP e21     , BP e22     )) = eqExprListUsingLocalVar tks1  [e11, e12] tks2  [e21, e22]
    | eqExprs (BE_Exists      (tks1 , BP e1                   )) (BE_Exists      (tks2 , BP e2                   )) = eqExprListUsingLocalVar tks1  [e1]       tks2  [e2]
    | eqExprs (BE_Lambda      (_    , tks1       , BP e11, e12)) (BE_Lambda      (_    , tks2       , BP e21, e22)) = eqExprListUsingLocalVar tks1  [e11, e12] tks2  [e21, e22]
    | eqExprs (BE_Sigma       (_    , tk1        , BP e11, e12)) (BE_Sigma       (_    , tk2        , BP e21, e22)) = eqExprListUsingLocalVar [tk1] [e11, e12] [tk2] [e21, e22]
    | eqExprs (BE_Pi          (_    , tk1        , BP e11, e12)) (BE_Pi          (_    , tk2        , BP e21, e22)) = eqExprListUsingLocalVar [tk1] [e11, e12] [tk2] [e21, e22]
    | eqExprs (BE_Inter       (_    , tks1       , BP e11, e12)) (BE_Inter       (_    , tks2       , BP e21, e22)) = eqExprListUsingLocalVar tks1  [e11, e12] tks2  [e21, e22]
    | eqExprs (BE_Union       (_    , tks1       , BP e11, e12)) (BE_Union       (_    , tks2       , BP e21, e22)) = eqExprListUsingLocalVar tks1  [e11, e12] tks2  [e21, e22]
    | eqExprs (BE_Struct      (_    , l1                      )) (BE_Struct      (_    , l2                      )) = ListPair.allEq (fn ((s1, e1), (s2, e2)) => (s1 = s2) andalso (eqExprs e1 e2)) (l1, l2)
    | eqExprs (BE_Rec         (_    , l1                      )) (BE_Rec         (_    , l2                      )) = ListPair.allEq (fn ((s1Opt, e1), (s2Opt, e2)) => (s1Opt = s2Opt) andalso (eqExprs e1 e2)) (l1, l2)
    | eqExprs (BE_RcAc        (_    , e1         , s1         )) (BE_RcAc        (_    , e2         , s2         )) = (eqExprs e1 e2) andalso (s1 = s2)
    | eqExprs (BE_Commutative (_    , tk1        , es1        )) (BE_Commutative (_    , tk2        , es2        )) = (tk1 = tk2) andalso (Utils.eqAsMset eqExprs es1 es2)
    | eqExprs _ _ = false
    and
      eqExprListUsingLocalVar varList1 exprList1 varList2 exprList2 = (* 変数は順不同、式は同順 *)
      let
        val len1 = List.length varList1
        val len2 = List.length varList2
      in
        if
          len1 <> len2
        then
          false
        else
          let
            val newIdStrList = genStringList len1
            fun rw (localVarStr, newIdStr) e = mapExprTree (mapIdsInExpr (fn idStr => if idStr = localVarStr then newIdStr else idStr)) e
            fun rwList ((localVarStr, newIdStr) :: rest) e = rw (localVarStr, newIdStr) (rwList rest e)
              | rwList []                                e = e
            val varStrList1 = List.map (fn (Var x) => x | _ => raise ASTError "") varList1
            val varStrList2 = List.map (fn (Var x) => x | _ => raise ASTError "") varList2
            val rewrittenExprList1 = List.map (rwList (ListPair.zip (varStrList1, newIdStrList))) exprList1
            val perms = Utils.perm newIdStrList
            val rewrittenExprList2List = List.map (fn nl => List.map (rwList (ListPair.zip (varStrList2, nl))) exprList2) perms
            val result = List.exists (fn rewrittenExprList2 => ListPair.all (Utils.uncurry eqExprs) (rewrittenExprList1, rewrittenExprList2)) rewrittenExprList2List
          in
            result
          end
      end

  fun eqPredicates (BP e1) (BP e2) = eqExprs e1 e2

  fun eqSubstitutions (BS_Block s1)                      (BS_Block s2)                      =
        eqSubstitutions s1 s2
    | eqSubstitutions BS_Identity                        BS_Identity                        = true
    | eqSubstitutions (BS_Precondition (p1, s1))          (BS_Precondition (p2, s2))          =
        eqPredicates p1 p2 andalso
        eqSubstitutions s1 s2
    | eqSubstitutions (BS_Assertion (p1, s1))             (BS_Assertion (p2, s2))             =
        eqPredicates p1 p2 andalso
        eqSubstitutions s1 s2
    | eqSubstitutions (BS_Choice ss1)                     (BS_Choice ss2)                   =
        List.length ss1 = List.length ss2 andalso
        Utils.eqAsMset eqSubstitutions ss1 ss2
    | eqSubstitutions (BS_If l1)                          (BS_If l2)                        =
        ListPair.all (fn ((NONE,    s1), (NONE,    s2)) => eqSubstitutions s1 s2
                       | ((SOME p1, s1), (SOME p2, s2)) => eqSubstitutions s1 s2 andalso eqPredicates p1 p2
                       | _ => false)
                     (l1, l2)
    | eqSubstitutions (BS_Select l1)                      (BS_Select l2)                    =
        ListPair.all (fn ((NONE,    s1), (NONE,    s2)) => eqSubstitutions s1 s2
                       | ((SOME p1, s1), (SOME p2, s2)) => eqSubstitutions s1 s2 andalso eqPredicates p1 p2
                       | _ => false)
                     (l1, l2)
    | eqSubstitutions (BS_Case (e1, l1))                  (BS_Case (e2, l2))                  = (* 順不同 *)
        List.length l1 = List.length l2 andalso
        eqExprs e1 e2 andalso
        Utils.eqAsMset (fn (es1, s1) => fn (es2, s2) => Utils.eqAsSet eqExprs es1 es2 andalso eqSubstitutions s1 s2) l1 l2
    | eqSubstitutions (BS_Any (tks1, BP e1, s1))          (BS_Any (tks2, BP e2, s2))              = (* 順不同・局所変数 *)
      let
        val len1 = List.length tks1
        val len2 = List.length tks2
      in
        if
          len1 <> len2
        then
          false
        else
          let
            val newIdStrList = genStringList len1
            
            fun rwExpr (localVarStr, newIdStr) e = mapExprTree (mapIdsInExpr (fn idStr => if idStr = localVarStr then newIdStr else idStr)) e
            fun rwListExpr ((localVarStr, newIdStr) :: rest) e = rwExpr (localVarStr, newIdStr) (rwListExpr rest e)
              | rwListExpr []                                e = e
              
            fun rwSubstitution (localVarStr, newIdStr) s = mapExprsInSubstitutionTree (mapIdsInExpr (fn idStr => if idStr = localVarStr then newIdStr else idStr)) s
            fun rwListSubstitution ((localVarStr, newIdStr) :: rest) s = rwSubstitution (localVarStr, newIdStr) (rwListSubstitution rest s)
              | rwListSubstitution []                                s = s

            val varStrList1 = List.map (fn (Var x) => x | _ => raise ASTError "") tks1
            val varStrList2 = List.map (fn (Var x) => x | _ => raise ASTError "") tks2

            val rewrittenExpr1 = rwListExpr (ListPair.zip (varStrList1, newIdStrList)) e1
            val rewrittenSubstitution1 = rwListSubstitution (ListPair.zip (varStrList1, newIdStrList)) s1

            val perms = Utils.perm newIdStrList

            val rewrittenExpr2AndSubstitution2List = List.map (fn nl => (rwListExpr (ListPair.zip (varStrList2, nl)) e2 , rwListSubstitution (ListPair.zip (varStrList2, nl)) s2)) perms
          in
            List.exists (fn (rewrittenExpr2, rewrittenSubstitution2) => eqExprs rewrittenExpr1 rewrittenExpr2 andalso eqSubstitutions rewrittenSubstitution1 rewrittenSubstitution2) rewrittenExpr2AndSubstitution2List
          end

      end
    | eqSubstitutions (BS_Let (l1, s1))                   (BS_Let (l2, s2))                   = (* LETの局所変数の定義に依存関係がある場合があるため、順番を考慮する *)
      let
        val len1 = List.length l1
        val len2 = List.length l2
      in
        if
          len1 <> len2
        then
          false
        else
          let
            val newIdStrList = genStringList len1
            
            fun rwExpr (localVarStr, newIdStr) e = mapExprTree (mapIdsInExpr (fn idStr => if idStr = localVarStr then newIdStr else idStr)) e
            fun rwListExpr ((localVarStr, newIdStr) :: rest) e = rwExpr (localVarStr, newIdStr) (rwListExpr rest e)
              | rwListExpr []                                e = e
              
            fun rwSubstitution (localVarStr, newIdStr) s = mapExprsInSubstitutionTree (mapIdsInExpr (fn idStr => if idStr = localVarStr then newIdStr else idStr)) s
            fun rwListSubstitution ((localVarStr, newIdStr) :: rest) s = rwSubstitution (localVarStr, newIdStr) (rwListSubstitution rest s)
              | rwListSubstitution []                                s = s

            val varStrList1 = List.map (fn (Var x, _) => x | _ => raise ASTError "") l1
            val varStrList2 = List.map (fn (Var x, _) => x | _ => raise ASTError "") l2

            val rewriteTable1 = ListPair.zip (varStrList1, newIdStrList)
            val rewriteTable2 = ListPair.zip (varStrList2, newIdStrList)
            
            val rewrittenExprList1 = List.map (fn (_, e) => rwListExpr rewriteTable1 e) l1
            val rewrittenExprList2 = List.map (fn (_, e) => rwListExpr rewriteTable2 e) l2

            val rewrittenSubstitution1 = rwListSubstitution rewriteTable1 s1
            val rewrittenSubstitution2 = rwListSubstitution rewriteTable2 s2
          in
            ListPair.all (Utils.uncurry eqExprs) (rewrittenExprList1, rewrittenExprList2) andalso
            eqSubstitutions rewrittenSubstitution1 rewrittenSubstitution2
          end
      end

    | eqSubstitutions (BS_BecomesElt (el1, e1))          (BS_BecomesElt (el2, e2))          =
        ListPair.all (Utils.uncurry eqExprs) (el1, el2) andalso eqExprs e1 e2
    | eqSubstitutions (BS_BecomesSuchThat (es1, p1))      (BS_BecomesSuchThat (es2, p2))      =
        List.length es1 = List.length es2 andalso
        Utils.eqAsMset eqExprs es1 es2 andalso
        eqPredicates p1 p2
    | eqSubstitutions (BS_Call (t1, es11, es12))         (BS_Call (t2, es21, es22))        =
        ListPair.all (Utils.uncurry eqExprs) (es11, es21) andalso
        t1 = t2 andalso
        ListPair.all (Utils.uncurry eqExprs) (es12, es22)
    | eqSubstitutions (BS_BecomesEqual (e11, e12))       (BS_BecomesEqual (e21, e22))        =
        eqExprs e11 e21 andalso
        eqExprs e12 e22
    | eqSubstitutions (BS_BecomesEqualList (es11, es12)) (BS_BecomesEqualList (es21, es22)) =
      let
        val esList1 = ListPair.zip (es11, es12)
        val esList2 = ListPair.zip (es21, es22)
      in
        List.length esList1 = List.length esList2 andalso 
        Utils.eqAsMset (fn (e11, e12) => fn (e21, e22) => eqExprs e11 e21 andalso eqExprs e12 e22) esList1 esList2
      end

    | eqSubstitutions (BS_Simultaneous ss1)             (BS_Simultaneous ss2)             =
        List.length ss1 = List.length ss2 andalso Utils.eqAsMset eqSubstitutions ss1 ss2                  (* 順不同 *)
        
    | eqSubstitutions (BS_LocalVariable (tks1, s1)) (BS_LocalVariable (tks2, s2)) = (* 順不同・局所変数 *)
      let
        val len1 = List.length tks1
        val len2 = List.length tks2
      in
        if
          len1 <> len2
        then
          false
        else
          let
            val newIdStrList = genStringList len1
            fun rw (localVarStr, newIdStr) s = mapExprsInSubstitutionTree (mapIdsInExpr (fn idStr => if idStr = localVarStr then newIdStr else idStr)) s
            fun rwList ((localVarStr, newIdStr) :: rest) s = rw (localVarStr, newIdStr) (rwList rest s)
              | rwList []                                s = s
            val varStrList1 = List.map (fn (Var x) => x | _ => raise ASTError "") tks1
            val varStrList2 = List.map (fn (Var x) => x | _ => raise ASTError "") tks2
            val rewrittenS1 = rwList (ListPair.zip (varStrList1, newIdStrList)) s1
            val perms = Utils.perm newIdStrList
            val rewrittenS2List = List.map (fn nl => rwList (ListPair.zip (varStrList2, nl)) s2) perms
          in
            List.exists (eqSubstitutions rewrittenS1) rewrittenS2List
          end
      end
    
    | eqSubstitutions (BS_Sequencing ss1)               (BS_Sequencing ss2)               =
        List.length ss1 = List.length ss2 andalso
        ListPair.all (Utils.uncurry eqSubstitutions) (ss1, ss2) (* 代入文の順番が異なる場合はfalse *)
    | eqSubstitutions (BS_While (p11, s1, p12, e1))     (BS_While (p21, s2, p22, e2))     =
        eqPredicates p11 p21 andalso
        eqSubstitutions s1 s2 andalso
        eqPredicates p12 p22 andalso
        eqExprs e1 e2
    | eqSubstitutions s1 s2 = false (* 代入文の種類が異なる場合はfalse *)
 
  fun eqOperations (BOp (name1, outputs1, inputs1, s1), BOp (name2, outputs2, inputs2, s2)) =
      name1    = name2    andalso
      outputs1 = outputs2 andalso
      inputs1  = inputs2  andalso
      eqSubstitutions s1 s2

  fun eqClauses (BC_CONSTRAINTS p1) (BC_CONSTRAINTS p2) = eqPredicates p1 p2
    | eqClauses (BC_PROPERTIES  p1) (BC_PROPERTIES  p2) = eqPredicates p1 p2
    | eqClauses (BC_INVARIANT   p1) (BC_INVARIANT   p2) = eqPredicates p1 p2
    | eqClauses (BC_ASSERTIONS  p1) (BC_ASSERTIONS  p2) = eqPredicates p1 p2
    | eqClauses (BC_VALUES l1)      (BC_VALUES l2)      =
        List.length l1 = List.length l2 andalso
        ListPair.all (fn ((v1, e1), (v2, e2)) => v1 = v2 andalso eqExprs e1 e2) (l1, l2) (* 代入文の順番が異なる場合はfalse *)

    | eqClauses (BC_SEES l1)     (BC_SEES l2)     =
        ListPair.all (fn (BMchInst (x1, es1), BMchInst (x2, es2)) => x1 = x2 andalso ListPair.all (Utils.uncurry eqExprs) (es1, es2)) (l1, l2)
    | eqClauses (BC_INCLUDES l1) (BC_INCLUDES l2) =
        ListPair.all (fn (BMchInst (x1, es1), BMchInst (x2, es2)) => x1 = x2 andalso ListPair.all (Utils.uncurry eqExprs) (es1, es2)) (l1, l2)
    | eqClauses (BC_PROMOTES l1) (BC_PROMOTES l2) =
        ListPair.all (fn (BMchInst (x1, es1), BMchInst (x2, es2)) => x1 = x2 andalso ListPair.all (Utils.uncurry eqExprs) (es1, es2)) (l1, l2)
    | eqClauses (BC_EXTENDS l1)  (BC_EXTENDS l2)  =
        ListPair.all (fn (BMchInst (x1, es1), BMchInst (x2, es2)) => x1 = x2 andalso ListPair.all (Utils.uncurry eqExprs) (es1, es2)) (l1, l2)
    | eqClauses (BC_USES l1)     (BC_USES l2)     =
        ListPair.all (fn (BMchInst (x1, es1), BMchInst (x2, es2)) => x1 = x2 andalso ListPair.all (Utils.uncurry eqExprs) (es1, es2)) (l1, l2)
    | eqClauses (BC_IMPORTS l1)  (BC_IMPORTS l2)  =
        ListPair.all (fn (BMchInst (x1, es1), BMchInst (x2, es2)) => x1 = x2 andalso ListPair.all (Utils.uncurry eqExprs) (es1, es2)) (l1, l2)
        
    | eqClauses (BC_INITIALISATION s1) (BC_INITIALISATION s2) = eqSubstitutions s1 s2

    | eqClauses (BC_OPERATIONS os1)    (BC_OPERATIONS os2)    = ListPair.all eqOperations (os1, os2)

    | eqClauses (BC_CCONSTANTS l1)     (BC_CCONSTANTS l2)     = l1 = l2
    | eqClauses (BC_ACONSTANTS l1)     (BC_ACONSTANTS l2)     = l1 = l2
    | eqClauses (BC_CVARIABLES l1)     (BC_CVARIABLES l2)     = l1 = l2
    | eqClauses (BC_AVARIABLES l1)     (BC_AVARIABLES l2)     = l1 = l2

    | eqClauses (BC_SETS l1)           (BC_SETS l2)           = l1 = l2
    | eqClauses (BC_DEFINITIONS l1)    (BC_DEFINITIONS l2)    = l1 = l2
 
    | eqClauses _ _ = false
 
  fun eqComponents (BMch (mchName1,           prms1, clauses1)) (BMch (mchName2,           prms2, clauses2)) =
        mchName1 = mchName2 andalso
        Utils.eqAsMset Utils.eqto prms1 prms2 andalso 
        List.length clauses1 = List.length clauses2 andalso
        Utils.eqAsSet eqClauses clauses1 clauses2
    | eqComponents (BRef (refName1, mchName1, prms1, clauses1)) (BRef (refName2, mchName2, prms2, clauses2)) =
        refName1 = refName2 andalso
        mchName1 = mchName2 andalso
        Utils.eqAsMset Utils.eqto prms1 prms2 andalso
        List.length clauses1 = List.length clauses2 andalso
        Utils.eqAsSet eqClauses clauses1 clauses2
    | eqComponents (BImp (impName1, mchName1, prms1, clauses1)) (BImp (impName2, mchName2, prms2, clauses2)) =
        impName1 = impName2 andalso
        mchName1 = mchName2 andalso
        Utils.eqAsMset Utils.eqto prms1 prms2 andalso
        List.length clauses1 = List.length clauses2 andalso
        Utils.eqAsSet eqClauses clauses1 clauses2
    | eqComponents _ _ = false

  fun mapPredicatesInSubstitution f (BS_Precondition    (p, s        )) = BS_Precondition (f p, s)
    | mapPredicatesInSubstitution f (BS_Assertion       (p, s        )) = BS_Assertion (f p, s)
    | mapPredicatesInSubstitution f (BS_If              l             ) = BS_If     (List.map (fn (SOME p, s) => (SOME (f p), s) | elseBranch => elseBranch) l)
    | mapPredicatesInSubstitution f (BS_Select          l             ) = BS_Select (List.map (fn (SOME p, s) => (SOME (f p), s) | elseBranch => elseBranch) l)
    | mapPredicatesInSubstitution f (BS_Any             (tks, p, s   )) = BS_Any (tks, f p, s)
    | mapPredicatesInSubstitution f (BS_BecomesSuchThat (el, p       )) = BS_BecomesSuchThat (el, f p)
    | mapPredicatesInSubstitution f (BS_While           (p1, s, p2, e)) = BS_While (f p1, s, f p2, e)
    | mapPredicatesInSubstitution f s                                   = s

  fun mapPredicatesInExpr f (BE_Bool   p               ) = BE_Bool (f p)
    | mapPredicatesInExpr f (BE_InSet  (to,  tks, p   )) = BE_InSet (to, tks, f p)
    | mapPredicatesInExpr f (BE_ForAll (tks, p1,  p2  )) = BE_ForAll (tks, f p1, f p2)
    | mapPredicatesInExpr f (BE_Exists (tks, p        )) = BE_Exists (tks, f p)
    | mapPredicatesInExpr f (BE_Lambda (to,  tks, p, e)) = BE_Lambda (to, tks, f p, e)
    | mapPredicatesInExpr f (BE_Sigma  (to,  tk,  p, e)) = BE_Sigma (to, tk, f p, e)
    | mapPredicatesInExpr f (BE_Pi     (to,  tk,  p, e)) = BE_Pi (to, tk, f p, e)
    | mapPredicatesInExpr f (BE_Inter  (to,  tks, p, e)) = BE_Inter (to, tks, f p, e)
    | mapPredicatesInExpr f (BE_Union  (to,  tks, p, e)) = BE_Union (to, tks, f p, e)
    | mapPredicatesInExpr f e                            = e
  
  fun mapPredicatesInSubstitutionTree f s = mapExprsInSubstitutionTree (mapPredicatesInExpr f) (mapSubstitutionTree (mapPredicatesInSubstitution f) s)

  fun isSubExpr e1 e2 = (findExprTree (eqExprs e1) e2) <> NONE (* 「e1がe2の部分式のとき」trueを返す。e1とe2が等しい場合もtrueとなる。 *)

  (* 元 OperationDivision.extractChangedVars *)
  (* 代入文の左辺の式から参照する識別子を抽出する *)
      (* BExpr -> BToken list *)
      (* 左辺式 -> [変更変数] *)
  fun extractChangedVarsLhs (BE_Leaf (to, Var xl)) = [(Var xl)]
    | extractChangedVarsLhs (BE_Fnc  (to, e1, e2)) = extractChangedVarsLhs e1
    | extractChangedVarsLhs (BE_RcAc (to, e, str)) = extractChangedVarsLhs e
    | extractChangedVarsLhs _ = raise ASTError "invalid left-hand side of a substitution"

  (* 元 OperationDivision.extractReferenceVarsRhs *)
  (* 式内で使用されている識別子を抽出する *)
      (* BExpr -> BToken list *)
      (* 右辺式 -> [参照変数] *)
  fun extractReferenceVarsRhs (BE_Leaf (to, Var xl)) = [(Var xl)]
    | extractReferenceVarsRhs (BE_Leaf _) = []
    | extractReferenceVarsRhs (BE_Node1 (to, opToken, e)) = extractReferenceVarsRhs e
    | extractReferenceVarsRhs (BE_Node2 (to, opToken, e1, e2)) =
      Utils.deleteDouble Utils.eqto ((extractReferenceVarsRhs e1) @ (extractReferenceVarsRhs e2))
    | extractReferenceVarsRhs (BE_NodeN (to, opToken, el)) =
      Utils.deleteDouble Utils.eqto (List.concat (List.map extractReferenceVarsRhs el))
    | extractReferenceVarsRhs (BE_Fnc (to, e1, e2)) =
      Utils.deleteDouble Utils.eqto ((extractReferenceVarsRhs e1) @ (extractReferenceVarsRhs e2))
    | extractReferenceVarsRhs (BE_Img (to, e1, e2)) =
      Utils.deleteDouble Utils.eqto ((extractReferenceVarsRhs e1) @ (extractReferenceVarsRhs e2))
    | extractReferenceVarsRhs (BE_Bool (BP e)) = extractReferenceVarsRhs e
    | extractReferenceVarsRhs (BE_ExSet (to, el)) =
      Utils.deleteDouble Utils.eqto (List.concat (List.map extractReferenceVarsRhs el))
    | extractReferenceVarsRhs (BE_InSet (to, localVars, BP e)) =
      Utils.substractionAsSet Utils.eqto (extractReferenceVarsRhs e) localVars
    | extractReferenceVarsRhs (BE_Seq (to, el)) = Utils.deleteDouble
      Utils.eqto (List.concat (List.map extractReferenceVarsRhs el))
    | extractReferenceVarsRhs (BE_ForAll (localVars, BP e1, BP e2)) =
      Utils.substractionAsSet Utils.eqto (Utils.deleteDouble Utils.eqto ((extractReferenceVarsRhs e1) @ (extractReferenceVarsRhs e2))) localVars
    | extractReferenceVarsRhs (BE_Exists (localVars, BP e)) =
      Utils.substractionAsSet Utils.eqto (extractReferenceVarsRhs e) localVars
    | extractReferenceVarsRhs (BE_Lambda (to, localVars, BP e1, e2)) =
      Utils.substractionAsSet Utils.eqto (Utils.deleteDouble Utils.eqto ((extractReferenceVarsRhs e1) @ (extractReferenceVarsRhs e2))) localVars
    | extractReferenceVarsRhs (BE_Sigma (to, localVar, BP e1, e2)) =
      Utils.substractionAsSet Utils.eqto (Utils.deleteDouble Utils.eqto ((extractReferenceVarsRhs e1) @ (extractReferenceVarsRhs e2))) [localVar]
    | extractReferenceVarsRhs (BE_Pi (to, localVar, BP e1, e2)) =
      Utils.substractionAsSet Utils.eqto (Utils.deleteDouble Utils.eqto ((extractReferenceVarsRhs e1) @ (extractReferenceVarsRhs e2))) [localVar]
    | extractReferenceVarsRhs (BE_Inter (to, localVars, BP e1, e2)) =
      Utils.substractionAsSet Utils.eqto (Utils.deleteDouble Utils.eqto ((extractReferenceVarsRhs e1) @ (extractReferenceVarsRhs e2))) localVars
    | extractReferenceVarsRhs (BE_Union (to, localVars, BP e1, e2)) =
      Utils.substractionAsSet Utils.eqto (Utils.deleteDouble Utils.eqto ((extractReferenceVarsRhs e1) @ (extractReferenceVarsRhs e2))) localVars
    | extractReferenceVarsRhs (BE_Struct (to, l)) =
      Utils.deleteDouble Utils.eqto (List.concat (List.map (fn (_, e) => extractReferenceVarsRhs e) l))
    | extractReferenceVarsRhs (BE_Rec (to, l)) =
      Utils.deleteDouble Utils.eqto (List.concat (List.map (fn (_, e) => extractReferenceVarsRhs e) l))
    | extractReferenceVarsRhs (BE_RcAc (to, e, str)) = extractReferenceVarsRhs e
    | extractReferenceVarsRhs (BE_Commutative (to, opName, el)) =
      Utils.deleteDouble Utils.eqto (List.concat (List.map extractReferenceVarsRhs el))
      
  (* 元 OperationDivision.extractReferenceVarsLhs *)
  (* 代入文の左辺の式から参照する識別子を抽出する *)
      (* BExpr -> BToken list *)
      (* 左辺式 -> [参照変数] *)
  fun extractReferenceVarsLhs (BE_Leaf (to, Var _)) = []
    | extractReferenceVarsLhs (BE_Fnc (to, e1, e2)) = extractReferenceVarsRhs e2
    | extractReferenceVarsLhs _ = []
    
  (* 元 OperationDivision.extractReferenceVarsLhs *)
  (* 代入文の左辺の式から参照する識別子を抽出する *)
      (* BExpr -> BToken list *)
      (* 左辺式 -> [参照変数] *)
  fun extractReferenceVarsLhs (BE_Leaf (to, Var _)) = []
    | extractReferenceVarsLhs (BE_Fnc (to, e1, e2)) = extractReferenceVarsRhs e2
    | extractReferenceVarsLhs _ = []

  (* 元 OperationDivision.extractVars *)
  (* 代入文から変更する識別子と参照する識別子を抽出する *)
      (* BSubstitution -> (BToken list) * (BToken list) *)
      (* 代入文 -> ([変更変数], [参照変数]) *)
  fun extractVars (BS_Block s) = extractVars s
    | extractVars BS_Identity = ([], [])
    | extractVars (BS_Precondition (BP e, s)) = 
      let
        val (nextChangedVars, nextReferenceVars) = extractVars s
        val referenceVars = extractReferenceVarsRhs e
      in
        (nextChangedVars, (Utils.deleteDouble Utils.eqto (nextReferenceVars @ referenceVars)))
      end
    | extractVars (BS_Assertion (BP e, s)) =
      let
        val (nextChangedVars, nextReferenceVars) = extractVars s
        val referenceVars = extractReferenceVarsRhs e
      in
        (nextChangedVars, (Utils.deleteDouble Utils.eqto (nextReferenceVars @ referenceVars)))
      end
    | extractVars (BS_Choice l) =
      let
        val (changedVars, referenceVars) =
          List.foldr (fn ((c1, r1), (c2, r2)) => ((c1 @ c2), (r1 @ r2))) ([], []) (List.map extractVars l)
      in
        ((Utils.deleteDouble Utils.eqto changedVars), (Utils.deleteDouble Utils.eqto referenceVars))
      end
    | extractVars (BS_If l) =
      let
        val sl = List.map (fn (_, s) => s) l
        val el = List.concat (List.map (fn (NONE, _) => [] | (SOME (BP e), _) => [e]) l)
        val (changedVars, referenceVarsInSubstitutions) =
          List.foldr (fn ((c1, r1), (c2, r2)) => ((c1 @ c2), (r1 @ r2))) ([], []) (List.map extractVars sl)
        val referenceVars = referenceVarsInSubstitutions @ (List.concat (List.map extractReferenceVarsRhs el))
      in
        ((Utils.deleteDouble Utils.eqto changedVars), (Utils.deleteDouble Utils.eqto referenceVars))
      end
    | extractVars (BS_Select l) =
      let
        val sl = List.map (fn (_, s) => s) l
        val el = List.concat (List.map (fn (NONE, _) => [] | (SOME (BP e), _) => [e]) l)
        val (changedVars, referenceVarsInSubstitutions) =
          List.foldr (fn ((c1, r1), (c2, r2)) => ((c1 @ c2), (r1 @ r2))) ([], []) (List.map extractVars sl)
        val referenceVars = referenceVarsInSubstitutions @ (List.concat (List.map extractReferenceVarsRhs el))
      in
        ((Utils.deleteDouble Utils.eqto changedVars), (Utils.deleteDouble Utils.eqto referenceVars))
      end
    | extractVars (BS_Case (e, l)) =
      let
        val allSl = List.map (fn (_, s) => s) l
        val allEl = e :: (List.concat (List.map (fn (el, _) => el) l))
        val (changedVars, referenceVarsInSubstitutions) =
          List.foldr (fn ((c1, r1), (c2, r2)) => ((c1 @ c2), (r1 @ r2))) ([], []) (List.map extractVars allSl)
        val referenceVars = referenceVarsInSubstitutions @ (List.concat (List.map extractReferenceVarsRhs allEl))
      in
        ((Utils.deleteDouble Utils.eqto changedVars), (Utils.deleteDouble Utils.eqto referenceVars))
      end
    | extractVars (BS_Any (lvl, BP e, s)) =
      let
        val (changedVarsInSubstitutions, referenceVarsInSubstitutions) = extractVars s
        val changedVars = Utils.substractionAsSet Utils.eqto changedVarsInSubstitutions lvl
        val referenceVars = Utils.substractionAsSet Utils.eqto (referenceVarsInSubstitutions @ (extractReferenceVarsRhs e)) lvl
      in
        ((Utils.deleteDouble Utils.eqto changedVars), (Utils.deleteDouble Utils.eqto referenceVars))
      end
    | extractVars (BS_Let (l, s)) = 
      let
        val lvl = List.foldr (fn ((var, _), vl) => var :: vl) [] l
        val (changedVarsInSubstitutions, referenceVarsInSubstitutions) = extractVars s
        val referenceVarsInLet = List.concat (List.map (fn (_, e) => extractReferenceVarsRhs e) l)
        val changedVars = Utils.substractionAsSet Utils.eqto changedVarsInSubstitutions lvl
        val referenceVars = Utils.substractionAsSet Utils.eqto (referenceVarsInSubstitutions @ referenceVarsInLet) lvl
      in
        ((Utils.deleteDouble Utils.eqto changedVars), (Utils.deleteDouble Utils.eqto referenceVars))
      end
    | extractVars (BS_BecomesElt (el, re)) =
      let
        val changedVars = List.concat (List.map extractChangedVarsLhs el)
        val referenceVars = extractReferenceVarsRhs re
      in
        ((Utils.deleteDouble Utils.eqto changedVars), (Utils.deleteDouble Utils.eqto referenceVars))
      end
    | extractVars (BS_BecomesSuchThat (el, BP e)) =
      let
        val changedVars = List.concat (List.map extractChangedVarsLhs el)
        val referenceVars =
          List.concat ((extractReferenceVarsRhs e) :: (List.map extractReferenceVarsLhs el)) (* 事後状態の参照となるので注意 *)
      in
        ((Utils.deleteDouble Utils.eqto changedVars), (Utils.deleteDouble Utils.eqto referenceVars))
      end
    | extractVars (BS_Call (_, el1, el2)) =
      let
        val changedVars = List.concat (List.map extractChangedVarsLhs el1)
        val referenceVars = List.concat ((List.map extractReferenceVarsLhs el1) @ (List.map extractReferenceVarsRhs el2))
      in
        ((Utils.deleteDouble Utils.eqto changedVars), (Utils.deleteDouble Utils.eqto referenceVars))
      end
    | extractVars (BS_BecomesEqual (e1, e2)) = 
      let
        val changedVars = extractChangedVarsLhs e1
        val referenceVars = (extractReferenceVarsLhs e1) @ (extractReferenceVarsRhs e2)
      in
        ((Utils.deleteDouble Utils.eqto changedVars), (Utils.deleteDouble Utils.eqto referenceVars))
      end
    | extractVars (BS_BecomesEqualList (sl1, sl2)) = 
      let
        val changedVars = List.concat (List.map extractChangedVarsLhs sl1)
        val referenceVars = List.concat ((List.map extractReferenceVarsLhs sl1) @ (List.map extractReferenceVarsRhs sl2))
      in
        (changedVars, referenceVars)
      end
    | extractVars (BS_Simultaneous sl) = extractVarsInSubstitutionList sl

    | extractVars (BS_Sequencing sl) = extractVarsInSubstitutionList sl

    | extractVars (BS_LocalVariable (_, s)) = extractVars s

    | extractVars (BS_While (BP e1, s, BP e2, e3)) =
      let
        val (changedVarsInSubstitutions, referenceVarsInSubstitutions) = extractVars s
        val e1Vars = extractReferenceVarsRhs e1
        val e2Vars = extractReferenceVarsRhs e2
        val e3Vars = extractReferenceVarsRhs e3
      in
        (changedVarsInSubstitutions, Utils.deleteDouble Utils.eqto (e1Vars @ e2Vars @ e3Vars @ referenceVarsInSubstitutions))
      end
      
  (* 元 OperationDivision.extractVarsInSubstitutionList *)
  (* 代入文のリストから変更する識別子と参照する識別子を抽出する *)
      (* BSubstitution -> (BToken list) * (BToken list) *)
      (* [代入文] -> ([変更変数], [参照変数]) *)
  and extractVarsInSubstitutionList sl =  
      let
        val (changedVars, referenceVars) =
          List.foldr (fn ((cvs1, rvs1), (cvs2, rvs2)) => ((cvs1 @ cvs2), (rvs1 @ rvs2)))
          ([], []) (List.map extractVars sl)
      in
        ((Utils.deleteDouble Utils.eqto changedVars), (Utils.deleteDouble Utils.eqto referenceVars))
      end
end
