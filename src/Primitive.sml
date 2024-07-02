structure Primitive =
struct
  exception PrimitiveError of string
  fun applyLetEnv env (BE_Leaf (to, Var vn)) =
      (case
          (List.find (fn (v, e) => v = Var vn) env)
        of
          NONE              => (BE_Leaf (to, Var vn))
        | (SOME (Var _, e)) => e
        | _ => raise PrimitiveError "")
        
    | applyLetEnv env (BE_Leaf  (to, x))              = BE_Leaf  (to, x)
    | applyLetEnv env (BE_Node1 (to, opName, e))      = BE_Node1 (to, opName, applyLetEnv env e)
    | applyLetEnv env (BE_Node2 (to, opName, e1, e2)) = BE_Node2 (to, opName, applyLetEnv env e1, applyLetEnv env e2)
    | applyLetEnv env (BE_NodeN (to, opName, el))     = BE_NodeN (to, opName, List.map (applyLetEnv env) el)
    | applyLetEnv env (BE_Fnc   (to, e1, e2))         = BE_Fnc   (to, applyLetEnv env e1, applyLetEnv env e2)
    | applyLetEnv env (BE_Img   (to, e1, e2))         = BE_Img   (to, applyLetEnv env e1, applyLetEnv env e2)
    | applyLetEnv env (BE_Bool  (BP e))               = BE_Bool  (BP (applyLetEnv env e))
    | applyLetEnv env (BE_ExSet (to, el))             = BE_ExSet (to, List.map (applyLetEnv env) el)
    | applyLetEnv env (BE_InSet (to, vl, BP e))       =
      let
        val nenv = List.filter (fn (v, _) => not (List.exists (Utils.eqto v) vl)) env
      in
        BE_InSet (to, vl, BP (applyLetEnv nenv e))
      end
    | applyLetEnv env (BE_Seq (to, el)) = BE_Seq (to, List.map (applyLetEnv env) el)
    | applyLetEnv env (BE_ForAll (vl, BP e1, BP e2)) =
      let
        val nenv = List.filter (fn (v, _) => not (List.exists (Utils.eqto v) vl)) env
      in
        BE_ForAll (vl, BP (applyLetEnv nenv e1), BP (applyLetEnv nenv e2))
      end
    | applyLetEnv env (BE_Exists (vl, BP e)) =
      let
        val nenv = List.filter (fn (v, _) => not (List.exists (Utils.eqto v) vl)) env
      in
        BE_Exists (vl, BP (applyLetEnv nenv e))
      end
    | applyLetEnv env (BE_Lambda (to, vl, BP e1, e2)) =
      let
        val nenv = List.filter (fn (v, _) => not (List.exists (Utils.eqto v) vl)) env
      in
        BE_Lambda (to, vl, BP (applyLetEnv nenv e1), applyLetEnv nenv e2)
      end
    | applyLetEnv env (BE_Sigma (to, v1, BP e1, e2)) =
      let
        val nenv = List.filter (fn (v, _) => not (v = v1)) env
      in
        BE_Sigma (to, v1, BP (applyLetEnv nenv e1), applyLetEnv nenv e2)
      end
    | applyLetEnv env (BE_Pi (to, v1, BP e1, e2)) =
      let
        val nenv = List.filter (fn (v, _) => not (v = v1)) env
      in
        BE_Pi (to, v1, BP (applyLetEnv nenv e1), applyLetEnv nenv e2)
      end
    | applyLetEnv env (BE_Inter (to, vl, BP e1, e2)) =
      let
        val nenv = List.filter (fn (v, _) => not (List.exists (Utils.eqto v) vl)) env
      in
        BE_Inter (to, vl, BP (applyLetEnv nenv e1), applyLetEnv nenv e2)
      end
    | applyLetEnv env (BE_Union (to, vl, BP e1, e2)) =
      let
        val nenv = List.filter (fn (v, _) => not (List.exists (Utils.eqto v) vl)) env
      in
        BE_Union (to, vl, BP (applyLetEnv nenv e1), applyLetEnv nenv e2)
      end
    | applyLetEnv env (BE_Struct      (to, l))          = BE_Struct      (to, List.map (fn (str,  e) => (str,  applyLetEnv env e)) l)
    | applyLetEnv env (BE_Rec         (to, l))          = BE_Rec         (to, List.map (fn (stro, e) => (stro, applyLetEnv env e)) l)
    | applyLetEnv env (BE_RcAc        (to, e, str))     = BE_RcAc        (to, applyLetEnv env e, str)
    | applyLetEnv env (BE_Commutative (to, opName, el)) = BE_Commutative (to, opName,            List.map (applyLetEnv env) el)
    
  fun expandLetInSubstitutionTree env (BS_Block s)                     = BS_Block (expandLetInSubstitutionTree env s)
    | expandLetInSubstitutionTree env BS_Identity                      = BS_Identity
    | expandLetInSubstitutionTree env (BS_Precondition (BP e, s))      = BS_Precondition (BP (applyLetEnv env e), expandLetInSubstitutionTree env s)
    | expandLetInSubstitutionTree env (BS_Assertion (p, s))            = BS_Assertion (p, expandLetInSubstitutionTree env s)
    | expandLetInSubstitutionTree env (BS_Choice l)                    = BS_Choice (List.map (expandLetInSubstitutionTree env) l)
    | expandLetInSubstitutionTree env (BS_If l)                        = BS_If (List.map (fn (NONE,        s) => (NONE, expandLetInSubstitutionTree env s)
                                                                               | (SOME (BP e), s) => (SOME (BP (applyLetEnv env e)), expandLetInSubstitutionTree env s))
                                                                             l)
    | expandLetInSubstitutionTree env (BS_Select l)                    = BS_Select (List.map (fn (NONE,        s) => (NONE, expandLetInSubstitutionTree env s)
                                                                                   | (SOME (BP e), s) => (SOME (BP (applyLetEnv env e)), expandLetInSubstitutionTree env s)) l)
    | expandLetInSubstitutionTree env (BS_Case (e, l))                 = BS_Case (applyLetEnv env e, List.map (fn (el, s) => (el, expandLetInSubstitutionTree env s)) l)
    | expandLetInSubstitutionTree env (BS_Any (vl, BP e, s))           = BS_Any (vl, BP (applyLetEnv env e), expandLetInSubstitutionTree env s)
    | expandLetInSubstitutionTree env (BS_Let (eqs, s))                =
      let
        val nenv = eqs @ env
      in
        Utils.repeatApply (expandLetInSubstitutionTree nenv) s
      end
    | expandLetInSubstitutionTree env (BS_BecomesElt       (el, re))         = BS_BecomesElt (List.map (applyLetEnv env) el, applyLetEnv env re)
    | expandLetInSubstitutionTree env (BS_BecomesSuchThat  (el, BP e))       = BS_BecomesSuchThat (List.map (applyLetEnv env) el, BP (applyLetEnv env e))
    | expandLetInSubstitutionTree env (BS_Call             (name, el1, el2)) = BS_Call (name, List.map (applyLetEnv env) el1, List.map (applyLetEnv env) el2)
    | expandLetInSubstitutionTree env (BS_BecomesEqual     (e1, e2))         = BS_BecomesEqual (applyLetEnv env e1, applyLetEnv env e2)
    | expandLetInSubstitutionTree env (BS_BecomesEqualList (el1, el2))       = BS_BecomesEqualList (List.map (applyLetEnv env) el1, List.map (applyLetEnv env) el2)
    | expandLetInSubstitutionTree env (BS_Simultaneous sl)                   = BS_Simultaneous (List.map (expandLetInSubstitutionTree env) sl)
    | expandLetInSubstitutionTree env _                                      = raise PrimitiveError "unsupported substitution"
    
  (* 使われていない識別子名を生成するための番号 *)
  val unusedIdStrNumber = ref 0
  
  fun generateUnusedIdStr usedIdStrs =
      let
        val _ = unusedIdStrNumber := !unusedIdStrNumber + 1;
        val newIdStr = "genVar" ^ (Utils.intToFixedString 3 (!unusedIdStrNumber))
      in
        if
          Utils.isIn newIdStr usedIdStrs
        then
          generateUnusedIdStr usedIdStrs
        else
          newIdStr
      end

  fun extractUsedIdStrs (BE_Leaf (_, Var str)) = [str]
    | extractUsedIdStrs expr = List.concat (List.map extractUsedIdStrs (AST.subExprTrees expr))
  
  fun primitiveExpr (BE_ExSet (to, [e])) = BE_ExSet (to, [e])
    | primitiveExpr (BE_ExSet (to, el))  = BE_Commutative (to, Keyword "\\/", List.map (fn e => BE_ExSet (to, [e])) el)
    | primitiveExpr (BE_ForAll (lvs, BP e1, BP e2)) = BE_Node1 (SOME BT_Predicate, Keyword "not", BE_Exists (lvs, BP (BE_Commutative (SOME BT_Predicate, Keyword "&", [e1, BE_Node1 (SOME BT_Predicate, Keyword "not", e2)]))))
    | primitiveExpr (BE_Seq (to, [e])) = BE_Seq (to, [e])
    | primitiveExpr (BE_Seq (to, el)) =
      let
        val lastElement :: reversed = List.rev el
      in
        BE_Node2 (to, Keyword "^", (primitiveExpr (BE_Seq (to, List.rev reversed))), BE_Seq (to, [lastElement]))
      end
    | primitiveExpr e = e
  
  fun primitiveSubstitution (BS_Block s) = s
    | primitiveSubstitution (BS_BecomesEqual (BE_Fnc (_, f, e1), e2)) =
        BS_BecomesEqual (f, BE_Node2 (NONE, Keyword "<+", f, BE_ExSet (NONE, [(BE_Node2 (NONE, Keyword "|->", e1, e2))])))
    | primitiveSubstitution (BS_Case (e0, l)) =   (* CASEはSELECTを用いて定義されるが条件が排他的なのでIFでも代用可能だと思われる *)
      let
        fun primitiveSubstitutionAux ([], s) = (NONE, s)
          | primitiveSubstitutionAux (es, s) =
            let
              fun parseOR [e] = BE_Node2 (SOME BT_Predicate, Keyword "=", e0, e)
                | parseOR (e :: rest) = BE_Node2 (SOME BT_Predicate, Keyword "or", BE_Node2 (SOME BT_Predicate, Keyword "=", e0, e), (parseOR rest))
                | parseOR _ = raise PrimitiveError ""
            in
              (SOME (BP (parseOR es)), s)
            end
      in
        BS_If (List.map primitiveSubstitutionAux l)
      end
    | primitiveSubstitution (BS_BecomesElt (el, re)) = 
      let
        val usedIdsInExprs = (List.concat (List.map extractUsedIdStrs el)) @ (extractUsedIdStrs re)
        fun generateUnusedIdStrList _ 0 = []
          | generateUnusedIdStrList usedIdStrs n =
            let
              val newIdStr = generateUnusedIdStr usedIdStrs
            in
              newIdStr :: (generateUnusedIdStrList (newIdStr :: usedIdStrs) (n - 1))
            end
        val localVars = List.map (fn x => Var x) (generateUnusedIdStrList usedIdsInExprs (List.length el))
        val localExprs = List.map (fn v => BE_Leaf (NONE, v)) localVars
        fun makeCommaTree [] = raise PrimitiveError ""
          | makeCommaTree [e] = e
          | makeCommaTree (e1 :: e2 :: es) = makeCommaTree ((BE_Node2 (NONE, Keyword ",", e1, e2)) :: es)
        val localExprTree = makeCommaTree localExprs
      in
        BS_Any (localVars, BP (BE_Node2 (SOME BT_Predicate, Keyword ":", localExprTree, re)), BS_BecomesEqualList (el, localExprs))
      end
    | primitiveSubstitution (BS_BecomesEqualList (el1, el2)) = BS_Simultaneous (ListPair.map (fn (e1, e2) => BS_BecomesEqual (e1, e2)) (el1, el2))
    | primitiveSubstitution s = s
      
  fun primitiveSubstitutionTree s = AST.mapExprsInSubstitutionTree primitiveExpr (AST.mapSubstitutionTree primitiveSubstitution s)

  fun primitiveOperation (BOp (name, oparam, iparam, s)) = BOp (name, oparam, iparam, Utils.repeatApply primitiveSubstitutionTree (expandLetInSubstitutionTree [] s))

  fun primitiveClause (BC_OPERATIONS     l) = BC_OPERATIONS     (List.map primitiveOperation l)
    | primitiveClause (BC_INITIALISATION s) = BC_INITIALISATION (Utils.repeatApply primitiveSubstitutionTree (expandLetInSubstitutionTree [] s))
    | primitiveClause (BC_CONSTRAINTS (BP e)) = BC_CONSTRAINTS (BP (AST.mapExprTree primitiveExpr e))
    | primitiveClause (BC_PROPERTIES (BP e)) = BC_PROPERTIES (BP (AST.mapExprTree primitiveExpr e))
    | primitiveClause (BC_INVARIANT (BP e)) = BC_INVARIANT (BP (AST.mapExprTree primitiveExpr e))
    | primitiveClause x                     = x

  fun primitive (BMch (name,            params, clauses)) = BMch (name,            params, (List.map primitiveClause clauses))
    | primitive (BRef (name, modelName, params, clauses)) = BRef (name, modelName, params, (List.map primitiveClause clauses))
    | primitive _                                         = raise PrimitiveError "LET in IMPLEMENTATION"
end


