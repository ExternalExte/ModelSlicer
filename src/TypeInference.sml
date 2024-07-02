structure TypeInference =
struct
  exception BTypeError of string
  fun isTypeSetByName s =
      let
        val os = IdentifierDuplication.originalString s
        val (x :: xs) = String.explode os
      in
        Char.isUpper x andalso (List.all (fn y => Char.isUpper y orelse y = #"_") xs) 
      end

  (* デバッグ用 *)
  fun typeToString NONE = "NONE"
    | typeToString (SOME BT_Real) = "REAL"
    | typeToString (SOME BT_Integer) = "INTEGER"
    | typeToString (SOME BT_String) = "STRING"
    | typeToString (SOME BT_Float) = "FLOAT"
    | typeToString (SOME BT_Bool) = "BOOL"
    | typeToString (SOME (BT_Power x)) = "POW ("^(typeToString x)^")"
    | typeToString (SOME (BT_Pair (x, y))) = (typeToString x)^"*"^(typeToString y)
    | typeToString (SOME (BT_Struct _)) = "STRUCT"
    | typeToString (SOME (BT_Deferred s)) = s
    | typeToString (SOME (BT_Enum (s, sl))) = s^"={"^(Utils.concatWith "," sl)^"}"
    | typeToString (SOME BT_Predicate) = "PREDICATE"

  fun typeOf (BE_Leaf        (t, _))       = t 
    | typeOf (BE_Node1       (t, _, _))    = t
    | typeOf (BE_Commutative (t, _, _))    = t
    | typeOf (BE_Fnc         (t, _, _))    = t 
    | typeOf (BE_Img         (t, _, _))    = t
    | typeOf (BE_NodeN       (t, _, _))    = t
    | typeOf (BE_Bool        _)            = SOME BT_Predicate
    | typeOf (BE_Node2       (t, _, _, _)) = t 
    | typeOf (BE_ExSet       (t, _))       = t 
    | typeOf (BE_InSet       (t, _, _))    = t 
    | typeOf (BE_Seq         (t, _))       = t 
    | typeOf (BE_ForAll      _)            = SOME BT_Predicate
    | typeOf (BE_Exists      _)            = SOME BT_Predicate
    | typeOf (BE_Lambda      (t, _, _, _)) = t
    | typeOf (BE_Sigma       (t, _, _, _)) = t
    | typeOf (BE_Pi          (t, _, _, _)) = t
    | typeOf (BE_Inter       (t, _, _, _)) = t
    | typeOf (BE_Union       (t, _, _, _)) = t
    | typeOf (BE_Struct      (t, _))       = t
    | typeOf (BE_Rec         (t, _))       = t
    | typeOf (BE_RcAc        (t, _, _))    = t
  and
      (* 式に型をセットする *)
      setType t x = setTypeOpt (SOME t) x
  and
      (* 式に型 (オプション型) をセットする *)
      setTypeOpt t (BE_Leaf        (_, x))           = BE_Leaf        (t, x) 
    | setTypeOpt t (BE_Node1       (_, x1, x2))      = BE_Node1       (t, x1, x2)
    | setTypeOpt t (BE_Node2       (_, x1, x2, x3))  = BE_Node2       (t, x1, x2, x3)
    | setTypeOpt t (BE_NodeN       (_, x1, x2))      = BE_NodeN       (t, x1, x2)
    | setTypeOpt t (BE_Fnc         (_, x1, x2))      = BE_Fnc         (t, x1, x2)
    | setTypeOpt t (BE_Img         (_, x1, x2))      = BE_Img         (t, x1, x2)
    (* BE_Bool は型情報なし *)
    | setTypeOpt t (BE_ExSet       (_, x))           = BE_ExSet       (t, x) 
    | setTypeOpt t (BE_InSet       (_, x1, x2))      = BE_InSet       (t, x1, x2)
    | setTypeOpt t (BE_Seq         (_, x))           = BE_Seq         (t, x)
    (* BE_ForAll は型情報なし *)
    (* BE_Exists は型情報なし *)
    | setTypeOpt t (BE_Lambda      (_, x1, x2, x3))  = BE_Lambda      (t, x1, x2, x3)
    | setTypeOpt t (BE_Sigma       (_, x1, x2, x3))  = BE_Sigma       (t, x1, x2, x3)
    | setTypeOpt t (BE_Pi          (_, x1, x2, x3))  = BE_Pi          (t, x1, x2, x3)
    | setTypeOpt t (BE_Inter       (_, x1, x2, x3))  = BE_Inter       (t, x1, x2, x3)
    | setTypeOpt t (BE_Union       (_, x1, x2, x3))  = BE_Union       (t, x1, x2, x3)
    | setTypeOpt t (BE_Struct      (_, x))           = BE_Struct      (t, x)
    | setTypeOpt t (BE_Rec         (_, x))           = BE_Rec         (t, x)
    | setTypeOpt t (BE_RcAc        (_, x1, x2))      = BE_RcAc        (t, x1, x2)
    | setTypeOpt t (BE_Commutative (_, x1, x2))      = BE_Commutative (t, x1, x2)  
    | setTypeOpt t x = x
  and
      (* コンポーネント内の型情報を全てクリアする *)
      resetTypeInComponent c = AST.mapExprsInComponent (setTypeOpt NONE) c
  and
    (* 環境 (識別子とその型の組のリスト) を式に反映する *)
      setEnv env expr = 
      let
        fun setEnvAux (BE_Leaf (to, Var x)) =
            let
              val tinfoOpt = List.find (fn (Var y, to) => x = y | _ => raise BTypeError "invalid token") env
            in
              case tinfoOpt of
                NONE          => BE_Leaf (to, Var x)
              | SOME (_, to1) => BE_Leaf (typeUnification to to1, Var x)
            end
          | setEnvAux x = x
      in
        AST.mapExprTree setEnvAux expr
      end
  and
    (* 式内で新たに判明した型情報を環境に反映する *)
      getEnv [] expr = []
    | getEnv ((Var x, to) :: env) expr =
      let
        val next = getEnv env expr
        val es = AST.findExprs (fn (BE_Leaf (SOME t, Var z)) => x = z | _ => false) expr
      in
        if
          es = []
        then
          (Var x, to) :: next
        else
          (Var x, (List.foldl (Utils.uncurry typeUnification) to (List.map typeOf es))) :: next
      end
    | getEnv _ _ = raise BTypeError ""
  and
    typeConstraints parameters constraintsOpt clauses = 
      (case (parameters, constraintsOpt) of
          ([]   , NONE  ) => ([], clauses)
        | ([]   , SOME _) => raise BTypeError "0 machine parameter with constraints clause"
        | (param, NONE  ) => if List.all (fn (Var x) => isTypeSetByName x | _ => raise BTypeError "") parameters then
            let
              val env = List.map (fn (Var x) => (Var x, SOME (BT_Power (SOME (BT_Deferred x)))) | _ => raise BTypeError "") param
            in
              (env, clauses)
            end
          else
            raise BTypeError "scalar parameters without constraints"
        | (param, SOME (BC_CONSTRAINTS (BP e))) => 
          let  
            val env1 = List.map (fn (Var x) => if isTypeSetByName x then (Var x, SOME (BT_Power (SOME (BT_Deferred x)))) else (Var x, NONE) | _ => raise BTypeError "") param
            val ne = typeExprTree (setEnv env1 e)
            val env2 = getEnv env1 ne
            val ncls = (BC_CONSTRAINTS (BP ne)) :: (List.filter (fn (BC_CONSTRAINTS _) => false | _ => true) clauses)
          in
            (env2, ncls)
          end
        | _ => raise BTypeError ""
      )
  and
    typeProperties env NONE clauses = (env, clauses)
    | typeProperties [] (SOME _) _ = raise BTypeError "properties clause with no constants to be typed"
    | typeProperties env (SOME (BC_PROPERTIES (BP e))) clauses =
      let
        fun updateEnv (oldenv, oldexpr) =
            let
              val nexpr = typeExprTree (setEnv oldenv oldexpr)
              val nenv = getEnv oldenv nexpr
            in
              (nenv, nexpr)
            end
        val (env1, e1) = Utils.repeatApply updateEnv (env, e)
        val ncls = (BC_PROPERTIES (BP e1)) :: (List.filter (fn (BC_PROPERTIES _) => false | _ => true) clauses)
      in
        (env1, ncls)
      end
    | typeProperties _ _ _ = raise BTypeError ""
  and
    typeInvariant env NONE clauses = (env, clauses)
    | typeInvariant env (SOME (BC_INVARIANT (BP e))) clauses =
      let
        fun updateEnv (oldenv, oldexpr) =
            let
              val nexpr = typeExprTree (setEnv oldenv oldexpr)
              val nenv = getEnv oldenv nexpr
            in
              (nenv, nexpr)
            end
        val (env1, e1) = Utils.repeatApply updateEnv (env, e)
        val ncls = (BC_INVARIANT (BP e1)) :: (List.filter (fn (BC_INVARIANT _) => false | _ => true) clauses)
      in
        (env1, ncls)
      end
    | typeInvariant _ _ _ = raise BTypeError ""
  and
    typeInitialisation env NONE clauses = clauses
    | typeInitialisation env (SOME (BC_INITIALISATION s)) clauses = 
      let
        val ns = typeSubstitutionTree env s
      in
        (BC_INITIALISATION ns) :: (List.filter (fn (BC_INITIALISATION _) => false | _ => true) clauses)
      end
    | typeInitialisation _ _ _ = raise BTypeError ""
  and
    typeOperations env NONE clauses = clauses
    | typeOperations env (SOME (BC_OPERATIONS ops)) clauses = 
      (BC_OPERATIONS (List.map (typeOperation env) ops)) :: (List.filter (fn (BC_OPERATIONS _) => false | _ => true) clauses)
    | typeOperations _ _ _ = raise BTypeError ""
  and
    typeOperation env (BOp (name, outputs, inputs, s)) =
      let
        val inenv  = List.map (fn token => (token, NONE : BType option)) inputs
        val outenv = List.map (fn token => (token, NONE : BType option)) outputs
        val typedSubstitution = typeSubstitutionTree (outenv @ inenv @ env) s
      in
        BOp (name, outputs, inputs, typedSubstitution)
      end
  and
    typeAssertions env NONE clauses = clauses
    | typeAssertions env (SOME (BC_ASSERTIONS (BP e))) clauses =
      let
        val ne = typeExprTree (setEnv env e)
      in
        (BC_ASSERTIONS (BP ne)) :: (List.filter (fn (BC_ASSERTIONS _) => false | _ => true) clauses)
      end
    | typeAssertions _ _ _ = raise BTypeError ""
  and
      typeSees env NONE clauses = clauses
    | typeSees env (SOME (BC_SEES l)) clauses = (BC_SEES (typeMachinelist env l)) :: (List.filter (fn (BC_SEES _) => false | _ => true) clauses)
    | typeSees _ _ _ = raise BTypeError ""
  and
      typeIncludes env NONE clauses = clauses
    | typeIncludes env (SOME (BC_INCLUDES l)) clauses = (BC_INCLUDES (typeMachinelist env l)) :: (List.filter (fn (BC_INCLUDES _) => false | _ => true) clauses)
    | typeIncludes _ _ _ = raise BTypeError ""
  and
      typePromotes env NONE clauses = clauses
    | typePromotes env (SOME (BC_PROMOTES l)) clauses = (BC_PROMOTES (typeMachinelist env l)) :: (List.filter (fn (BC_PROMOTES _) => false | _ => true) clauses)
    | typePromotes _ _ _ = raise BTypeError ""
  and
      typeExtends env NONE clauses = clauses
    | typeExtends env (SOME (BC_EXTENDS l)) clauses = (BC_EXTENDS (typeMachinelist env l)) :: (List.filter (fn (BC_EXTENDS _) => false | _ => true) clauses)
    | typeExtends _ _ _ = raise BTypeError ""
  and
      typeUses env NONE clauses = clauses
    | typeUses env (SOME (BC_USES l)) clauses = (BC_USES (typeMachinelist env l)) :: (List.filter (fn (BC_USES _) => false | _ => true) clauses)
    | typeUses _ _ _ = raise BTypeError ""
  and
      typeImports env NONE clauses = clauses
    | typeImports env (SOME (BC_IMPORTS l)) clauses = (BC_IMPORTS (typeMachinelist env l)) :: (List.filter (fn (BC_IMPORTS _) => false | _ => true) clauses)
    | typeImports _ _ _ = raise BTypeError ""
  and
      typeMachinelist env [] = []
    | typeMachinelist env ((BMchInst (t, [])) :: ms) = (BMchInst (t, [])) :: (typeMachinelist env ms)
    | typeMachinelist env ((BMchInst (t, l)) :: ms) = (BMchInst (t, List.map (fn e => (Utils.repeatApply typeExpr) (setEnv env e)) l)) :: (typeMachinelist env ms)
  and
      typeValues env NONE clauses = clauses
    | typeValues env (SOME (BC_VALUES l)) clauses = (BC_VALUES (List.map (fn (v, e) => (v, Utils.repeatApply typeExpr (setEnv env e))) l)) :: (List.filter (fn (BC_VALUES _) => false | _ => true) clauses)
    | typeValues _ _ _ = raise BTypeError ""
  and
      typeComponent (BMch (machinename, parameters, clauses)) = 
      let
        val constraintsOpt    = List.find (fn (BC_CONSTRAINTS _)    => true | _ => false) clauses
        val setsOpt           = List.find (fn (BC_SETS _)           => true | _ => false) clauses
        val valuesOpt         = List.find (fn (BC_VALUES _)         => true | _ => false) clauses (**)
        val seesOpt           = List.find (fn (BC_SEES _)           => true | _ => false) clauses (**)
        val includesOpt       = List.find (fn (BC_INCLUDES _)       => true | _ => false) clauses
        val promotesOpt       = List.find (fn (BC_PROMOTES _)       => true | _ => false) clauses (**)
        val extendsOpt        = List.find (fn (BC_EXTENDS _)        => true | _ => false) clauses
        val usesOpt           = List.find (fn (BC_USES _)           => true | _ => false) clauses (**)
        val importsOpt        = List.find (fn (BC_IMPORTS _)        => true | _ => false) clauses (**)
        val aconstantsOpt     = List.find (fn (BC_ACONSTANTS _)     => true | _ => false) clauses
        val cconstantsOpt     = List.find (fn (BC_CCONSTANTS _)     => true | _ => false) clauses
        val propertiesOpt     = List.find (fn (BC_PROPERTIES _)     => true | _ => false) clauses
        val avariablesOpt     = List.find (fn (BC_AVARIABLES _)     => true | _ => false) clauses
        val cvariablesOpt     = List.find (fn (BC_CVARIABLES _)     => true | _ => false) clauses
        val invariantOpt      = List.find (fn (BC_INVARIANT _)      => true | _ => false) clauses
        val assertionsOpt     = List.find (fn (BC_ASSERTIONS _)     => true | _ => false) clauses
        val initialisationOpt = List.find (fn (BC_INITIALISATION _) => true | _ => false) clauses
        val operationsOpt     = List.find (fn (BC_OPERATIONS _)     => true | _ => false) clauses
        val (envConstraints, c1) = typeConstraints parameters constraintsOpt clauses
        val envSets = (
            case setsOpt of
              NONE              => []
            | SOME (BC_SETS ts) => List.map (fn (BT_Deferred s) => (Var s, SOME (BT_Power (SOME (BT_Deferred s)))) | (BT_Enum (s, es)) => (Var s, SOME (BT_Power (SOME (BT_Enum (s, es))))) | _ => raise BTypeError "") ts
            | _ => raise BTypeError ""
          )
        val envAconstants = (
            case aconstantsOpt of
              NONE                    => []
            | SOME (BC_ACONSTANTS vs) => List.map (fn (Var x) => (Var x, NONE : BType option) | _ => raise BTypeError "") vs
            | _ => raise BTypeError ""
          )
        val envCconstants = (
            case cconstantsOpt of
              NONE                    => []
            | SOME (BC_CCONSTANTS vs) => List.map (fn (Var x) => (Var x, NONE : BType option) | _ => raise BTypeError "") vs
            | _ => raise BTypeError ""
          ) 
        val (envProperties, c2) = typeProperties (envConstraints @ envSets @ envAconstants @ envCconstants) propertiesOpt c1
        val c3 = typeSees     envProperties seesOpt     c2
        val c4 = typeIncludes envProperties includesOpt c3
        val c5 = typePromotes envProperties promotesOpt c4
        val c6 = typeExtends  envProperties extendsOpt  c5
        val c7 = typeUses     envProperties usesOpt     c6
        val c8 = typeImports  envProperties importsOpt  c7
        val c9 = typeValues   envProperties valuesOpt   c8
        val envAvariables = (
            case avariablesOpt of
              NONE                    => []
            | SOME (BC_AVARIABLES vs) => List.map (fn (Var x) => (Var x, NONE : BType option) | _ => raise BTypeError "") vs
            | _ => raise BTypeError ""
          ) 
        val envCvariables = (
            case cvariablesOpt of
              NONE                    => []
            | SOME (BC_CVARIABLES vs) => List.map (fn Var x => (Var x, NONE : BType option) | _ => raise BTypeError "") vs
            | _ => raise BTypeError ""
          ) 
        val (envInvariant, c10) = typeInvariant (envConstraints @ envProperties @ envAvariables @ envCvariables) invariantOpt c9
        val c11 = typeAssertions envInvariant assertionsOpt c10
        val c12 = typeInitialisation envInvariant initialisationOpt c11
        val c13 = typeOperations envInvariant operationsOpt c12
      in
        BMch (machinename, parameters, c13)
      end
    | typeComponent _ = raise BTypeError "input is not an abstract machine"
  and
      typeSubstitutionTree env (BS_Block s) = (BS_Block (typeSubstitutionTree env s))
    | typeSubstitutionTree env (BS_Precondition (BP ps, s)) = 
      let
        fun updateEnv (oldenv, oldp) =
            let
              val np = typeExprTree (setEnv oldenv oldp)
              val nenv = getEnv oldenv np
            in
              (nenv, np)
            end
        val (env1, ps1) = Utils.repeatApply updateEnv (env, ps)
        val s1 = typeSubstitutionTree env1 s
      in
        BS_Precondition (BP ps1, s1)
      end
    | typeSubstitutionTree env (BS_Assertion (BP ps, s)) = 
      let
        fun updateEnv (oldenv, oldp) =
            let
              val np = typeExprTree (setEnv oldenv oldp)
              val nenv = getEnv oldenv np
            in
              (nenv, np)
            end
        val (env1, p1) = Utils.repeatApply updateEnv (env, ps)
        val s1 = typeSubstitutionTree env1 s
      in
        BS_Assertion (BP p1, s1)
      end
    | typeSubstitutionTree env (BS_Choice l) = BS_Choice (List.map (typeSubstitutionTree env) l)
    | typeSubstitutionTree env (BS_If l) = BS_If (List.map (fn (SOME p, s) => (SOME (typePredicateTree env p), typeSubstitutionTree env s)
                                                     | (NONE  , s) => (NONE, typeSubstitutionTree env s)) l)
    | typeSubstitutionTree env (BS_Select l) = BS_Select (List.map (fn (SOME p, s) => (SOME (typePredicateTree env p), typeSubstitutionTree env s)
                                                             | (NONE  , s) => (NONE, typeSubstitutionTree env s)) l)
    | typeSubstitutionTree env (BS_Case (ex, l)) = BS_Case (typeExprTree (setEnv env ex), List.map (fn (es, s) => (List.map (fn x => typeExprTree (setEnv env x)) es, typeSubstitutionTree env s)) l)
    | typeSubstitutionTree env (BS_Any (vs, BP ps, s)) = 
      let
        val env1 = List.map (fn x => (x, NONE)) vs
        fun updateEnv (oldenv, oldp) = 
            let
              val np = typeExprTree (setEnv oldenv oldp)
              val nenv = getEnv oldenv np
            in
              (nenv, np)
            end
        val (env2, p1) = Utils.repeatApply updateEnv (env1 @ env, ps)
        val s1 = typeSubstitutionTree env2 s
      in
        BS_Any (vs, BP p1, s1)
      end
    | typeSubstitutionTree env (BS_Let (l, s)) = 
      let
        fun updateEnv (oldenv, oldl) =
            let
              val nl = List.map (fn (i, e) => (i, typeExprTree (setEnv oldenv e))) l
              val lenv = List.map (fn (i, e) => (i, typeOf e)) l
              fun addEnv en [] = en
                | addEnv en ((v, t) :: rest) =
                  let
                    val eOpt = List.find (fn (vv, _) => (vv = v)) en
                  in
                    case eOpt of
                      NONE          => addEnv en rest
                    | SOME (vv, tt) => 
                      let
                        val nt = typeUnification t tt
                      in
                        if nt = t then
                          addEnv en rest
                        else
                          let
                            val nen = (v, nt) :: (List.filter (fn (vv, _) => vv <> v) en)
                          in
                            addEnv nen rest
                          end
                      end 
                  end
              val nenv = addEnv oldenv lenv
            in
              (nenv, nl)
            end
        val (env1, l1) = Utils.repeatApply updateEnv (env, l)
        val s1 = typeSubstitutionTree env1 s
      in
        BS_Let (l1, s1)
      end    
    
    | typeSubstitutionTree env (BS_BecomesElt (el, re)) =
      let
        fun makeLhsTree [] = raise BTypeError ""
          | makeLhsTree [e] = e
          | makeLhsTree (e1 :: e2 :: es) = makeLhsTree ((BE_Node2 (NONE, Keyword ",", e1, e2)) :: es)
          
        val lhsTree = makeLhsTree el
        
        fun subsTreeAux (xold, yold) =
            let
              val nx = typeExprTree (setEnv env xold)
              val ny = typeExprTree (setEnv env yold)
              val xto = typeOf nx
              val yto = typeOf ny
              val nxto = (
                  case yto of
                    SOME (BT_Power xto1) => ((typeUnification xto xto1) handle BTypeError _ => raise BTypeError "::")
                  | NONE                 => xto
                  | _                    => raise BTypeError ""
                )
              val nyto = SOME (BT_Power nxto)
            in
              (setTypeOpt nxto nx, setTypeOpt nyto ny)
            end

        val (newLhsTree, nre) = Utils.repeatApply subsTreeAux (lhsTree, re)

        fun listLhs (BE_Node2 (_, Keyword ",", e1, e2)) = (listLhs e1) @ [e2]
          | listLhs e = [e]
        
      in
        BS_BecomesElt (listLhs newLhsTree, nre)
      end
    | typeSubstitutionTree env (BS_BecomesSuchThat (es, p)) = BS_BecomesSuchThat (List.map (fn e => typeExprTree (setEnv env e)) es, typePredicateTree env p)
    | typeSubstitutionTree env (BS_BecomesEqual (x, y)) = 
      let
        fun subsTreeAux (xold, yold) =
            let
              val nx = typeExprTree (setEnv env xold)
              val ny = typeExprTree (setEnv env yold)
              val xto = typeOf nx
              val yto = typeOf ny
              val nt = ((typeUnification xto yto) handle BTypeError _ => raise BTypeError ":=")
            in
              (setTypeOpt nt nx, setTypeOpt nt ny)
            end
        val (x1, y1) = Utils.repeatApply subsTreeAux (x, y)
      in
        BS_BecomesEqual (x1, y1)
      end
    | typeSubstitutionTree env (BS_Simultaneous l) = BS_Simultaneous (List.map (typeSubstitutionTree env) l)
    | typeSubstitutionTree env (BS_LocalVariable (vs, s)) =
      let
        val localEnv = List.map (fn x => (x, NONE)) vs
      in
        BS_LocalVariable (vs, typeSubstitutionTree (env @ localEnv) s)
      end
    | typeSubstitutionTree env (BS_Sequencing l) = BS_Sequencing (List.map (typeSubstitutionTree env) l)
    | typeSubstitutionTree env (BS_While (p1, s, p2, e)) = BS_While (typePredicateTree env p1, typeSubstitutionTree env s, typePredicateTree env p2, typeExprTree (setEnv env e))
    | typeSubstitutionTree _ x = x

  and
    typePredicateTree env (BP e) = BP (typeExprTree (setEnv env e))
  and
    typeExprTree et = Utils.repeatApply (AST.mapExprTree typeExpr) et
  and
      typeUnification NONE                      NONE                      = NONE
    | typeUnification NONE                      (SOME x)                  = SOME x
    | typeUnification (SOME x)                  NONE                      = SOME x
    | typeUnification (SOME (BT_Power x))       (SOME (BT_Power y))       = SOME (BT_Power (typeUnification x y))
    | typeUnification (SOME (BT_Pair (x1, x2))) (SOME (BT_Pair (y1, y2))) = SOME (BT_Pair (typeUnification x1 y1, typeUnification x2 y2))
    | typeUnification (SOME (BT_Struct l1))     (SOME (BT_Struct l2))     = 
      let
        val l12 = ListPair.zip (l1, l2)
        val nl = List.map (fn ((t1, s1), (t2, s2)) => if s1 = s2 then (valOf (typeUnification (SOME t1) (SOME t2)), s1) else raise BTypeError "") l12
      in
        SOME (BT_Struct nl)
      end
    | typeUnification (SOME x)                  (SOME y)                  = if x = y then SOME x else raise BTypeError ((typeToString (SOME x)) ^ " and " ^ (typeToString (SOME y)))
  and
    typeExpr (ex as BE_RcAc (NONE, rcd, x)) = (* a -> a'b *)
      let
        val rct = typeOf rcd
      in
        (case rct of
            NONE                  => ex
          | SOME (BT_Struct flst) => 
            let
              val t = #1 (valOf (List.find (fn (_, y) => y = x) flst))
            in
              BE_RcAc (SOME t, rcd, x)
            end
          | _ => raise BTypeError ""
        )
      end
    | typeExpr (BE_Node1 (yto, (Keyword "~"), x)) = (* a~ *)
      let
        val (na, nb) =
          (case (typeOf x, yto) of
              (SOME (BT_Power (SOME (BT_Pair (a1, b1)))), SOME (BT_Power (SOME (BT_Pair (b2, a2))))) => ((typeUnification a1 a2, typeUnification b1 b2) handle BTypeError _ => raise BTypeError "~")
            | (SOME (BT_Power (SOME (BT_Pair (a1, b1)))), _                                        ) => (a1, b1)
            | (_                                        , SOME (BT_Power (SOME (BT_Pair (b2, a2))))) => (a2, b2)
            | _                                                                                      => (NONE, NONE))
        val (nxt, nyt) = (BT_Power (SOME (BT_Pair (na, nb))), BT_Power (SOME (BT_Pair (nb, na))))
      in
        BE_Node1 (SOME nyt, (Keyword "~"), setType nxt x)
      end

    | typeExpr (BE_Node1 (xto, Keyword "-", y)) = (* -a *)
      let
        val t = ((typeUnification xto (typeOf y)) handle BTypeError _ => raise BTypeError "unary -")
      in
        BE_Node1 (t, Keyword "-", setTypeOpt t y)
      end
    
    | typeExpr (BE_Node2 (_, Keyword "**", x, y)) = (* a**b *)
      BE_Node2 (SOME BT_Integer, Keyword "**", setType BT_Integer x, setType BT_Integer y)
  
    | typeExpr (BE_Node2 (_, Keyword "/", x, y)) = (* a/b *)
      BE_Node2 (SOME BT_Integer, Keyword "/", setType BT_Integer x, setType BT_Integer y)
    | typeExpr (BE_Node2 (_, Keyword "mod", x, y)) = (* a mod b *)
      BE_Node2 (SOME BT_Integer, Keyword "mod", setType BT_Integer x, setType BT_Integer y)
    
    | typeExpr (ex as BE_Node2 (zto, Keyword "*", x, y)) = (* a * b *) (* 集合・スカラー両方に対応 *)
      let
        val xto = typeOf x
        val yto = typeOf y
        val (nxto, nyto, nzto) = 
          ((
            case (xto, yto, zto) of 
              (NONE              , NONE              , NONE                                       ) => (NONE, NONE, NONE)
            | (SOME (BT_Power xt), SOME (BT_Power yt), SOME (BT_Power (SOME (BT_Pair (zt1, zt2))))) =>
              let
                val t1 = typeUnification xt zt1
                val t2 = typeUnification yt zt2
              in
                (SOME (BT_Power t1), SOME (BT_Power t2), SOME (BT_Power (SOME (BT_Pair (t1, t2)))))
              end
            | (_, SOME (BT_Power yt), SOME (BT_Power (SOME (BT_Pair (zt1, zt2))))) =>
              let
                val t1 = zt1
                val t2 = typeUnification yt zt2
              in
                (SOME (BT_Power t1), SOME (BT_Power t2), SOME (BT_Power (SOME (BT_Pair (t1, t2)))))
              end
            | (SOME (BT_Power xt), _, SOME (BT_Power (SOME (BT_Pair (zt1, zt2))))) =>
              let
                val t1 = typeUnification xt zt1
                val t2 = zt2
              in
                (SOME (BT_Power t1), SOME (BT_Power t2), SOME (BT_Power (SOME (BT_Pair (t1, t2)))))
              end
            | (SOME (BT_Power xt), SOME (BT_Power yt), _) =>
              let
                val t1 = xt
                val t2 = yt
              in
                (SOME (BT_Power t1), SOME (BT_Power t2), SOME (BT_Power (SOME (BT_Pair (t1, t2)))))
              end
            | (SOME (BT_Power xt), _, _) =>
              let
                val t1 = xt
                val t2 = NONE
              in
                (SOME (BT_Power t1), SOME (BT_Power t2), SOME (BT_Power (SOME (BT_Pair (t1, t2)))))
              end
            | (_, SOME (BT_Power yt), _) =>
              let
                val t1 = NONE
                val t2 = yt
              in
                (SOME (BT_Power t1), SOME (BT_Power t2), SOME (BT_Power (SOME (BT_Pair (t1, t2)))))
              end
            | (_, _, SOME (BT_Power (SOME (BT_Pair (zt1, zt2))))) =>
              let
                val t1 = zt1
                val t2 = zt2
              in
                (SOME (BT_Power t1), SOME (BT_Power t2), SOME (BT_Power (SOME (BT_Pair (t1, t2)))))
              end
            | (_, _, SOME (BT_Power _)) =>
              let
                val t1 = NONE
                val t2 = NONE
              in
                (SOME (BT_Power t1), SOME (BT_Power t2), SOME (BT_Power (SOME (BT_Pair (t1, t2)))))
              end
            | (SOME xt, _,       _)       => (SOME xt, SOME xt, SOME xt)
            | (_,       SOME yt, _)       => (SOME yt, SOME yt, SOME yt)
            | (_,       _,       SOME zt) => (SOME zt, SOME zt, SOME zt)
          ) handle BTypeError _ => raise BTypeError "*")
      in
        BE_Node2 (nzto, Keyword "*", setTypeOpt nxto x, setTypeOpt nyto y)
      end
    
    | typeExpr (BE_Node2 (_, Keyword "..", x, y)) = 
      (BE_Node2 (SOME (BT_Power (SOME BT_Integer)), Keyword "..", setType BT_Integer x, setType BT_Integer y))
    | typeExpr (ex as BE_Node2 (_, Keyword "/:", x, y)) =
      let
        val xto = typeOf x
        val yto = typeOf y
        val nxto =
          (case (xto, yto) of
              (NONE   , NONE                ) => NONE
            | (xto2   , SOME (BT_Power yto2)) => ((typeUnification xto2 yto2) handle BTypeError _ => raise BTypeError "/:")
            | (SOME xt, NONE                ) => SOME xt
            | _ => raise BTypeError "")
      in
        BE_Node2 (SOME BT_Predicate, Keyword "/:", setTypeOpt nxto x, setTypeOpt (SOME (BT_Power nxto)) y)
      end
    | typeExpr (ex as BE_Node2 (_, Keyword ":", x, y)) =
      let
        val xto = typeOf x
        val yto = typeOf y
        val nxto =
          (case (xto, yto) of
              (NONE   , NONE                ) => NONE
            | (xto2   , SOME (BT_Power yto2)) => typeUnification xto2 yto2
            | (SOME xt, NONE                ) => SOME xt
            | _                               => raise BTypeError "")
      in
        BE_Node2 (SOME BT_Predicate, Keyword ":", setTypeOpt nxto x, setTypeOpt (SOME (BT_Power nxto)) y)
      end
    
    | typeExpr (BE_Node2 (_,  Keyword "or",  x, y)) = 
        BE_Node2 (SOME BT_Predicate, Keyword "or",  setType BT_Predicate x, setType BT_Predicate y)
    | typeExpr (BE_Node2 (_,  Keyword "&",   x, y)) = 
        BE_Node2 (SOME BT_Predicate, Keyword "&",   setType BT_Predicate x, setType BT_Predicate y)
    | typeExpr (BE_Node2 (_,  Keyword "=>",  x, y)) = 
        BE_Node2 (SOME BT_Predicate, Keyword "=>",  setType BT_Predicate x, setType BT_Predicate y)
    | typeExpr (BE_Node2 (_,  Keyword "<=>", x, y)) = 
        BE_Node2 (SOME BT_Predicate, Keyword "<=>", setType BT_Predicate x, setType BT_Predicate y)
    
    | typeExpr (BE_Node2 (to, Keyword "+",   x, y)) = ((kwXxx (x, y, to, "+"))   handle BTypeError _ => raise BTypeError "+")
    | typeExpr (BE_Node2 (to, Keyword "-",   x, y)) = ((kwXxx (x, y, to, "-"))   handle BTypeError _ => raise BTypeError "-")
    | typeExpr (BE_Node2 (to, Keyword "<+",  x, y)) = ((kwXxx (x, y, to, "<+"))  handle BTypeError _ => raise BTypeError "<+")
    | typeExpr (BE_Node2 (to, Keyword "/\\", x, y)) = ((kwXxx (x, y, to, "/\\")) handle BTypeError _ => raise BTypeError "/\\")
    | typeExpr (BE_Node2 (to, Keyword "\\/", x, y)) = ((kwXxx (x, y, to, "\\/")) handle BTypeError _ => raise BTypeError "\\/")
    | typeExpr (BE_Node2 (to, Keyword "^",   x, y)) = ((kwXxx (x, y, to, "^"))   handle BTypeError _ => raise BTypeError "^")

    | typeExpr (BE_Node2 (zto, Keyword ","  , x, y)) =
      (case typeExpr (BE_Node2 (zto, Keyword "|->", x, y)) of
        BE_Node2 (nzto, _, nx, ny) => BE_Node2 (nzto, Keyword ",", nx, ny)
      | _ => raise BTypeError "")
        
    | typeExpr (BE_Node2 (zto, Keyword "|->", x, y)) =
      let
        val xto = typeOf x
        val yto = typeOf y
        val (nxto, nyto) = 
          ((case zto of
              SOME (BT_Pair (zto1, zto2)) => 
                (typeUnification xto zto1, typeUnification yto zto2)
            | NONE => (xto, yto)
            | _ => raise BTypeError "") handle BTypeError _ => raise BTypeError "|->")
      in
        BE_Node2 (SOME (BT_Pair (nxto, nyto)), Keyword "|->", setTypeOpt nxto x, setTypeOpt nyto y)
      end

    | typeExpr (BE_Node2 (_, Keyword "/=",   x, y)) = ((kwXxp (x, y, "/="))   handle BTypeError _ => raise BTypeError "/=")
    | typeExpr (BE_Node2 (_, Keyword ">=",   x, y)) = ((kwXxp (x, y, ">="))   handle BTypeError _ => raise BTypeError ">=")
    | typeExpr (BE_Node2 (_, Keyword "<=",   x, y)) = ((kwXxp (x, y, "<="))   handle BTypeError _ => raise BTypeError "<=")
    | typeExpr (BE_Node2 (_, Keyword ">",    x, y)) = ((kwXxp (x, y, ">"))    handle BTypeError _ => raise BTypeError ">")
    | typeExpr (BE_Node2 (_, Keyword "<",    x, y)) = ((kwXxp (x, y, "<"))    handle BTypeError _ => raise BTypeError "<")
    | typeExpr (BE_Node2 (_, Keyword "<:",   x, y)) = ((kwXxp (x, y, "<:"))   handle BTypeError _ => raise BTypeError "<:")
    | typeExpr (BE_Node2 (_, Keyword "/<<:", x, y)) = ((kwXxp (x, y, "/<<:")) handle BTypeError _ => raise BTypeError "/<<:")
    | typeExpr (BE_Node2 (_, Keyword "/<:",  x, y)) = ((kwXxp (x, y, "/<:"))  handle BTypeError _ => raise BTypeError "/<:")
    | typeExpr (BE_Node2 (_, Keyword "<<:",  x, y)) = ((kwXxp (x, y, "<<:"))  handle BTypeError _ => raise BTypeError "<<:")
    | typeExpr (BE_Node2 (_, Keyword "=",    x, y)) = ((kwXxp (x, y, "="))    handle BTypeError _ => raise BTypeError "=")

    | typeExpr (BE_Node2 (zto, Keyword ">->>", x, y)) = ((typeRelationsets (zto, x, y, ">->>")) handle BTypeError _ => raise BTypeError ">->>")
    | typeExpr (BE_Node2 (zto, Keyword "-->",  x, y)) = ((typeRelationsets (zto, x, y, "-->"))  handle BTypeError _ => raise BTypeError "-->")
    | typeExpr (BE_Node2 (zto, Keyword "+->",  x, y)) = ((typeRelationsets (zto, x, y, "+->"))  handle BTypeError _ => raise BTypeError "+->")
    | typeExpr (BE_Node2 (zto, Keyword "-->>", x, y)) = ((typeRelationsets (zto, x, y, "-->>")) handle BTypeError _ => raise BTypeError "-->>")
    | typeExpr (BE_Node2 (zto, Keyword "+->>", x, y)) = ((typeRelationsets (zto, x, y, "+->>")) handle BTypeError _ => raise BTypeError "+->>")
    | typeExpr (BE_Node2 (zto, Keyword ">->",  x, y)) = ((typeRelationsets (zto, x, y, ">->"))  handle BTypeError _ => raise BTypeError ">->")
    | typeExpr (BE_Node2 (zto, Keyword ">+>",  x, y)) = ((typeRelationsets (zto, x, y, ">+>"))  handle BTypeError _ => raise BTypeError ">+>")
    | typeExpr (BE_Node2 (zto, Keyword "<->",  x, y)) = ((typeRelationsets (zto, x, y, "<->"))  handle BTypeError _ => raise BTypeError "<->")

    | typeExpr (BE_Node2 (zto, Keyword "|>>",  x, y)) = ((typeRanOperations (zto, x, y, "|>>")) handle BTypeError _ => raise BTypeError "|>>")
    | typeExpr (BE_Node2 (zto, Keyword "|>",   x, y)) = ((typeRanOperations (zto, x, y, "|>"))  handle BTypeError _ => raise BTypeError "|>")
    
    | typeExpr (BE_Node2 (zto, Keyword "<<|",  x, y)) = ((typeDomOperations (zto, x, y, "<<|")) handle BTypeError _ => raise BTypeError "<<|")
    | typeExpr (BE_Node2 (zto, Keyword "<|",   x, y)) = ((typeDomOperations (zto, x, y, "<|"))  handle BTypeError _ => raise BTypeError "<|")
    | typeExpr (BE_Node2 (zto, Keyword "\\|/", x, y)) = ((typeRseq (zto, x, y, "\\|/")) handle BTypeError _ => raise BTypeError "\\|/")
    | typeExpr (BE_Node2 (zto, Keyword "/|\\", x, y)) = ((typeRseq (zto, x, y, "/|\\")) handle BTypeError _ => raise BTypeError "/|\\")
    | typeExpr (BE_Node2 (zto, Keyword "<-",   x, y)) = 
      let
        val xzto = ((typeUnification (typeOf x) zto) handle BTypeError _ => raise BTypeError "<-")
        val yto = typeOf y
        val eto = (
            case xzto of 
              SOME (BT_Power (SOME (BT_Pair (_, eto1)))) => ((typeUnification eto1 yto) handle BTypeError _ => raise BTypeError "<-")
            | _ => yto
          )
        val nxto = SOME (BT_Power (SOME (BT_Pair (SOME BT_Integer, eto))))
        val nyto = eto
        val nzto = nxto 
      in
        BE_Node2 (nzto, Keyword "<-", setTypeOpt nxto x, setTypeOpt nyto y)
      end
    | typeExpr (BE_Node2 (zto, Keyword "->", x, y)) =
      let
        val yzto = ((typeUnification (typeOf y) zto) handle BTypeError _ => raise BTypeError "->")
        val xto = typeOf x
        val eto = (
            case yzto of 
              SOME (BT_Power (SOME (BT_Pair (_, eto1)))) => ((typeUnification eto1 xto) handle BTypeError _ => raise BTypeError "->")
            | _ => xto
          )
        val nxto = eto
        val nyto = SOME (BT_Power (SOME (BT_Pair (SOME BT_Integer, eto))))
        val nzto = nyto 
      in
        BE_Node2 (nzto, Keyword "->", setTypeOpt nxto x, setTypeOpt nyto y)
      end
    | typeExpr (BE_Node2 (zto, Keyword ";", x, y)) = 
      let
        val xto = typeOf x
        val yto = typeOf y
        val (nato, nbto, ncto) = 
          ((
            case (xto, yto, zto) of
              (SOME (BT_Power (SOME (BT_Pair (ato1, bto1)))), SOME (BT_Power (SOME (BT_Pair (bto2, cto1)))), SOME (BT_Power (SOME (BT_Pair (ato2, cto2))))) => (typeUnification ato1 ato2, typeUnification bto1 bto2, typeUnification cto1 cto2)
            | (SOME (BT_Power (SOME (BT_Pair (ato1, bto1)))), SOME (BT_Power (SOME (BT_Pair (bto2, cto1)))), _                                            ) => (ato1                     , typeUnification bto1 bto2, cto1                     )
            | (SOME (BT_Power (SOME (BT_Pair (ato1, bto1)))), _                                            , SOME (BT_Power (SOME (BT_Pair (ato2, cto2))))) => (typeUnification ato1 ato2, bto1                     , cto2                     )
            | (_                                            , SOME (BT_Power (SOME (BT_Pair (bto2, cto1)))), SOME (BT_Power (SOME (BT_Pair (ato2, cto2))))) => (ato2                     , bto2                     , typeUnification cto1 cto2)
            | (SOME (BT_Power (SOME (BT_Pair (ato1, bto1)))), _                                            , _                                            ) => (ato1                     , bto1                     , NONE                     )
            | (_                                            , SOME (BT_Power (SOME (BT_Pair (bto2, cto1)))), _                                            ) => (NONE                     , bto2                     , cto1                     )
            | (_                                            , _                                            , SOME (BT_Power (SOME (BT_Pair (ato2, cto2))))) => (ato2                     , NONE                     , cto2                     )
            | _                                                                                                                                             => (NONE                     , NONE                     , NONE                     )
          ) handle BTypeError _ => raise BTypeError ";")
        val nxto = SOME (BT_Power (SOME (BT_Pair (nato, nbto))))
        val nyto = SOME (BT_Power (SOME (BT_Pair (nbto, ncto))))
        val nzto = SOME (BT_Power (SOME (BT_Pair (nato, ncto))))
      in
        BE_Node2 (nzto, Keyword ";", setTypeOpt nxto x, setTypeOpt nyto y)
      end
    | typeExpr (BE_Node2 (zto, Keyword "><", x, y)) =
      let
        val xto = typeOf x
        val yto = typeOf y
        val (nato, nbto, ncto) = ((
            case (xto, yto, zto) of
              (SOME (BT_Power (SOME (BT_Pair (ato1, bto1)))), 
                SOME (BT_Power (SOME (BT_Pair (bto2, cto2)))), 
                SOME (BT_Power (SOME (BT_Pair (ato3, SOME (BT_Pair (bto3, cto3)))))))
              => 
                (typeUnification ato1 ato3, typeUnification bto1 (typeUnification bto2 bto3), typeUnification cto2 cto3)
            | (SOME (BT_Power (SOME (BT_Pair (ato1, bto1)))), 
              SOME (BT_Power (SOME (BT_Pair (bto2, cto2)))), 
              SOME (BT_Power (SOME (BT_Pair (ato3, _)))))
            => 
              (typeUnification ato1 ato3, typeUnification bto1 bto2, cto2)
            |(SOME (BT_Power (SOME (BT_Pair (ato1, bto1)))), 
              SOME (BT_Power (SOME (BT_Pair (bto2, cto2)))), 
              _)
            => 
              (ato1, typeUnification bto1 bto2, cto2)
            |(SOME (BT_Power (SOME (BT_Pair (ato1, bto1)))), 
              _, 
              SOME (BT_Power (SOME (BT_Pair (ato3, SOME (BT_Pair (bto3, cto3)))))))
            => 
              (typeUnification ato1 ato3, typeUnification bto1 bto3, cto3)
            |(SOME (BT_Power (SOME (BT_Pair (ato1, bto1)))), 
              _, 
              SOME (BT_Power (SOME (BT_Pair (ato3, _)))))
            => 
              (typeUnification ato1 ato3, bto1, NONE)
            |(_, 
              SOME (BT_Power (SOME (BT_Pair (bto2, cto2)))), 
              SOME (BT_Power (SOME (BT_Pair (ato3, SOME (BT_Pair (bto3, cto3)))))))
            => 
              (ato3, typeUnification bto2 bto3, typeUnification cto2 cto3)
            |(SOME (BT_Power (SOME (BT_Pair (ato1, bto1)))), _, _)
            => 
              (ato1, bto1, NONE)
            |(_, SOME (BT_Power (SOME (BT_Pair (bto2, cto2)))), _)
            => 
              (NONE, bto2, cto2)
            |(_, _, SOME (BT_Power (SOME (BT_Pair (ato3, SOME (BT_Pair (bto3, cto3)))))))
            => 
              (ato3, bto3, cto3)
            | _ => (NONE, NONE, NONE)
          ) handle BTypeError _ => raise BTypeError "><")
        val nxto = SOME (BT_Power (SOME (BT_Pair (nato, nbto))))
        val nyto = SOME (BT_Power (SOME (BT_Pair (nbto, ncto))))
        val nzto = SOME (BT_Power (SOME (BT_Pair (nato, SOME (BT_Pair (nbto, ncto))))))
      in
        BE_Node2 (nzto, Keyword "><", setTypeOpt nxto x, setTypeOpt nyto y)
      end
     
    | typeExpr (BE_Fnc (yto, f, x)) =
      let
        val fto = typeOf f
        val xto = typeOf x
        val (nxto, nyto) = ((
            case fto of 
              SOME (BT_Power (SOME (BT_Pair (ato, bto)))) => 
                (typeUnification ato xto, typeUnification bto yto)
            | _ => (xto, yto)
          ) handle BTypeError _ => raise BTypeError "ff(xx)")
        val nfto = SOME (BT_Power (SOME (BT_Pair (nxto, nyto))))
      in
        BE_Fnc (nyto, setTypeOpt nfto f, setTypeOpt nxto x)
      end
    | typeExpr (BE_Img (yto, f, x)) =
      let
        val fto = typeOf f
        val xto = typeOf x
        val (nato, nbto) = ((
            case (fto, xto, yto) of 
              (SOME (BT_Power (SOME (BT_Pair (ato1, bto1)))), SOME (BT_Power ato2), SOME (BT_Power bto2)) => (typeUnification ato1 ato2, typeUnification bto1 bto2)
            | (SOME (BT_Power (SOME (BT_Pair (ato1, bto1)))), SOME (BT_Power ato2), NONE                ) => (typeUnification ato1 ato2, bto1                     )
            | (SOME (BT_Power (SOME (BT_Pair (ato1, bto1)))), NONE                , SOME (BT_Power bto2)) => (ato1                     , typeUnification bto1 bto2)
            | (_                                            , SOME (BT_Power ato2), SOME (BT_Power bto2)) => (ato2                     , bto2                     )
            | (SOME (BT_Power (SOME (BT_Pair (ato1, bto1)))), NONE                , NONE                ) => (ato1                     , bto1                     )
            | (_                                            , SOME (BT_Power ato2), NONE                ) => (ato2                     , NONE                     )
            | (_                                            , NONE                , SOME (BT_Power bto2)) => (NONE                     , bto2                     )
            | _                                                                                           => (NONE                     , NONE                     )
          ) handle BTypeError _ => raise BTypeError "f[x]")
        val nxto = SOME (BT_Power nato)
        val nyto = SOME (BT_Power nbto)
        val nfto = SOME (BT_Power (SOME (BT_Pair (nato, nbto))))
      in
        BE_Img (nyto, setTypeOpt nfto f, setTypeOpt nxto x)
      end
            
    | typeExpr (BE_Node1 (_, Keyword "bool", y)) =
      BE_Node1 (SOME BT_Bool, Keyword "bool", setTypeOpt (SOME BT_Predicate) y)
    | typeExpr (BE_Node1 (_, Keyword "not", x)) = 
      BE_Node1 (SOME BT_Predicate, Keyword "not", setType BT_Predicate x)
    | typeExpr (BE_Node1 (_, Keyword "pred", x)) = 
      BE_Node1 (SOME BT_Integer, Keyword "pred", setType BT_Integer x)
    | typeExpr (BE_Node1 (_, Keyword "succ", x)) = 
      BE_Node1 (SOME BT_Integer, Keyword "succ", setType BT_Integer x)
    | typeExpr (BE_Node1 (_, Keyword "floor", x)) = 
      BE_Node1 (SOME BT_Integer, Keyword "floor", setType BT_Real x)
    | typeExpr (BE_Node1 (_, Keyword "ceiling", x)) = 
      BE_Node1 (SOME BT_Integer, Keyword "ceiling", setType BT_Real x)
    | typeExpr (BE_Node1 (_, Keyword "real", x)) = 
      BE_Node1 (SOME BT_Real, Keyword "real", setType BT_Integer x)
    | typeExpr (BE_Node1 (_, Keyword "card", x)) = 
      BE_Node1 (SOME BT_Integer, Keyword "card", setTypeOpt ((typeUnification (typeOf x) (SOME (BT_Power NONE))) handle BTypeError _ => raise BTypeError "card") x)
    | typeExpr (BE_Node1 (_, Keyword "size", x)) = 
      BE_Node1 (SOME BT_Integer, Keyword "size", setTypeOpt ((typeUnification (typeOf x) (SOME (BT_Power (SOME (BT_Pair (SOME BT_Integer, NONE)))))) handle BTypeError _ => raise BTypeError "size") x)
    | typeExpr (BE_Node1 (_, Keyword "sizet", x)) = 
      BE_Node1 (SOME BT_Integer, Keyword "sizet", setTypeOpt ((typeUnification (typeOf x) (SOME (BT_Power (SOME (BT_Pair (SOME (BT_Power (SOME (BT_Pair (SOME BT_Integer, SOME BT_Integer)))), NONE)))))) handle BTypeError _ => raise BTypeError "sizet") x)
    | typeExpr (BE_Node1 (yto, Keyword "max", x))  = ((typeMinmax (yto, "max", x)) handle BTypeError _ => raise BTypeError "max")
    | typeExpr (BE_Node1 (yto, Keyword "min", x))  = ((typeMinmax (yto, "min", x)) handle BTypeError _ => raise BTypeError "min")
    | typeExpr (BE_Node1 (yto, Keyword "FIN", x))  = ((typePow (yto, "FIN" , x)) handle BTypeError _ => raise BTypeError "FIN")
    | typeExpr (BE_Node1 (yto, Keyword "FIN1", x)) = ((typePow (yto, "FIN1", x)) handle BTypeError _ => raise BTypeError "FIN1")
    | typeExpr (BE_Node1 (yto, Keyword "POW", x))  = ((typePow (yto, "POW" , x)) handle BTypeError _ => raise BTypeError "POW")
    | typeExpr (BE_Node1 (yto, Keyword "POW1", x)) = ((typePow (yto, "POW1", x)) handle BTypeError _ => raise BTypeError "POW1")
    | typeExpr (BE_Node1 (yto, Keyword "id", x)) =
      let
        val xto = typeOf x
        val nato = ((
            case (xto, yto) of
              (SOME (BT_Power ato1), SOME (BT_Power (SOME (BT_Pair (ato2, ato3))))) => typeUnification ato1 (typeUnification ato2 ato3)
            | (NONE                , SOME (BT_Power (SOME (BT_Pair (ato2, ato3))))) => typeUnification ato2 ato3
            | (SOME (BT_Power ato1), _                                            ) => ato1
            | (NONE                , _                                            ) => NONE
            | _ => raise BTypeError ""
          ) handle BTypeError _ => raise BTypeError "id")
        val nxto = SOME (BT_Power nato)
        val nyto = SOME (BT_Power (SOME (BT_Pair (nato, nato))))
      in
        BE_Node1 (nyto, Keyword "id", setTypeOpt nxto x)
      end
    | typeExpr (BE_Node1 (yto, Keyword "first", x)) = ((typeFlseq (yto, "first", x)) handle BTypeError _ => raise BTypeError "first")
    | typeExpr (BE_Node1 (yto, Keyword "last" , x)) = ((typeFlseq (yto, "last" , x)) handle BTypeError _ => raise BTypeError "last")
    | typeExpr (BE_Node1 (yto, Keyword "union", x)) = ((typeUiset (yto, "union", x)) handle BTypeError _ => raise BTypeError "union")
    | typeExpr (BE_Node1 (yto, Keyword "inter", x)) = ((typeUiset (yto, "inter", x)) handle BTypeError _ => raise BTypeError "inter")
    | typeExpr (BE_Node1 (dto, Keyword "dom", f)) = 
      let
        val fto = typeOf f
        val (nato, nbto) = (
            case (dto, fto) of
              (SOME (BT_Power ato1), SOME (BT_Power (SOME (BT_Pair (ato2, bto2))))) => (((typeUnification ato1 ato2) handle BTypeError _ => raise BTypeError "dom"), bto2)
            | (SOME (BT_Power ato1), _                                            ) => (ato1                                                                       , NONE)
            | (NONE                , SOME (BT_Power (SOME (BT_Pair (ato2, bto2))))) => (ato2                                                                       , bto2)
            | (NONE                , _                                            ) => (NONE                                                                       , NONE)
            | _ => raise BTypeError ""
          )
        val ndto = SOME (BT_Power nato)
        val nfto = SOME (BT_Power (SOME (BT_Pair (nato, nbto))))
      in
        BE_Node1 (ndto, Keyword "dom", setTypeOpt nfto f)
      end
    | typeExpr (BE_Node1 (rto, Keyword "ran", f)) = 
      let
        val fto = typeOf f
        val (nato, nbto) = (
            case (rto, fto) of
              (SOME (BT_Power bto1), SOME (BT_Power (SOME (BT_Pair (ato2, bto2))))) => (ato2, ((typeUnification bto1 bto2) handle BTypeError _ => raise BTypeError "ran"))
            | (SOME (BT_Power bto1), _                                            ) => (NONE, bto1)
            | (NONE                , SOME (BT_Power (SOME (BT_Pair (ato2, bto2))))) => (ato2, bto2)
            | (NONE                , _                                            ) => (NONE, NONE)
            | _ => raise BTypeError ""
          )
        val nrto = SOME (BT_Power nbto)
        val nfto = SOME (BT_Power (SOME (BT_Pair (nato, nbto))))
      in
        BE_Node1 (nrto, Keyword "ran", setTypeOpt nfto f)
      end
    | typeExpr (BE_Node1 (fto, Keyword "closure",  g)) = ((typeClosure (fto, "closure",  g)) handle BTypeError _ => raise BTypeError "closure")
    | typeExpr (BE_Node1 (fto, Keyword "closure1", g)) = ((typeClosure (fto, "closure1", g)) handle BTypeError _ => raise BTypeError "closure1")
    
    | typeExpr (BE_Node1 (yto, Keyword "seq",      x)) = ((typeSeqset (yto, "seq",   x)) handle BTypeError _ => raise BTypeError "seq")
    | typeExpr (BE_Node1 (yto, Keyword "seq1",     x)) = ((typeSeqset (yto, "seq1",  x)) handle BTypeError _ => raise BTypeError "seq1")
    | typeExpr (BE_Node1 (yto, Keyword "iseq",     x)) = ((typeSeqset (yto, "iseq",  x)) handle BTypeError _ => raise BTypeError "iseq")
    | typeExpr (BE_Node1 (yto, Keyword "iseq1",    x)) = ((typeSeqset (yto, "iseq1", x)) handle BTypeError _ => raise BTypeError "iseq1")
    | typeExpr (BE_Node1 (yto, Keyword "perm",     x)) = ((typeSeqset (yto, "perm",  x)) handle BTypeError _ => raise BTypeError "perm")
    
    | typeExpr (BE_Node1 (yto, Keyword "rev",      x)) = ((typeSeqConvert (yto, "rev",   x)) handle BTypeError _ => raise BTypeError "rev")
    | typeExpr (BE_Node1 (yto, Keyword "front",    x)) = ((typeSeqConvert (yto, "front", x)) handle BTypeError _ => raise BTypeError "front")
    | typeExpr (BE_Node1 (yto, Keyword "tail",     x)) = ((typeSeqConvert (yto, "tail",  x)) handle BTypeError _ => raise BTypeError "tail")

    | typeExpr (BE_Node1 (yto, Keyword "btree",    x)) = ((typeTrees (yto, "btree", x)) handle BTypeError _ => raise BTypeError "btree")
    | typeExpr (BE_Node1 (yto, Keyword "tree",     x)) = ((typeTrees (yto, "tree",  x)) handle BTypeError _ => raise BTypeError "tree")

    | typeExpr (BE_Node1 (yto, Keyword "fnc",      x)) = 
      let
        val xto = typeOf x
        val (nato, nbto) = ((
            case (xto, yto) of
              (SOME (BT_Power (SOME (BT_Pair (ato1, bto1)))), SOME (BT_Power (SOME (BT_Pair (ato2, SOME (BT_Power bto2)))))) => (typeUnification ato1 ato2, typeUnification bto1 bto2)
            | (SOME (BT_Power (SOME (BT_Pair (ato1, bto1)))), SOME (BT_Power (SOME (BT_Pair (ato2, NONE                ))))) => (typeUnification ato1 ato2, bto1)
            | (SOME (BT_Power (SOME (BT_Pair (ato1, bto1)))), _                                                            ) => (ato1                     , bto1)
            | (_                                            , SOME (BT_Power (SOME (BT_Pair (ato2, SOME (BT_Power bto2)))))) => (ato2                     , bto2)
            | (_                                            , SOME (BT_Power (SOME (BT_Pair (ato2, NONE                ))))) => (ato2                     , NONE)
            | _                                                                                                              => (NONE                     , NONE) 
          ) handle BTypeError _ => raise BTypeError "fnc")
        val nxto = SOME (BT_Power (SOME (BT_Pair (nato, nbto))))
        val nyto = SOME (BT_Power (SOME (BT_Pair (nato, SOME (BT_Power nbto)))))
      in
        BE_Node1 (nyto, Keyword "fnc", setTypeOpt nxto x)
      end
    | typeExpr (BE_Node1 (yto, Keyword "rel", x)) = 
      let
        val xto = typeOf x
        val (nato, nbto) = ((
            case (yto, xto) of
              (SOME (BT_Power (SOME (BT_Pair (ato1, bto1)))), SOME (BT_Power (SOME (BT_Pair (ato2, SOME (BT_Power bto2)))))) => (typeUnification ato1 ato2, typeUnification bto1 bto2)
            | (SOME (BT_Power (SOME (BT_Pair (ato1, bto1)))), SOME (BT_Power (SOME (BT_Pair (ato2, NONE                ))))) => (typeUnification ato1 ato2, bto1)
            | (SOME (BT_Power (SOME (BT_Pair (ato1, bto1)))), _                                                            ) => (ato1                     , bto1)
            | (_                                            , SOME (BT_Power (SOME (BT_Pair (ato2, SOME (BT_Power bto2)))))) => (ato2                     , bto2)
            | (_                                            , SOME (BT_Power (SOME (BT_Pair (ato2, NONE                ))))) => (ato2                     , NONE)
            | _                                                                                                              => (NONE                     , NONE) 
          ) handle BTypeError _ => raise BTypeError "rel")
        val nyto = SOME (BT_Power (SOME (BT_Pair (nato, nbto))))
        val nxto = SOME (BT_Power (SOME (BT_Pair (nato, SOME (BT_Power nbto)))))
      in
        BE_Node1 (nyto, Keyword "rel", setTypeOpt nxto x)
      end
    | typeExpr (BE_Node1 (yto, Keyword "conc", x)) = 
      let
        val xto = typeOf x
        val neto = (
            case (xto, yto) of
              (SOME (BT_Power (SOME (BT_Pair (_, SOME (BT_Power (SOME (BT_Pair (_, eto1)))))))), SOME (BT_Power (SOME (BT_Pair (_, eto2))))) => ((typeUnification eto1 eto2) handle BTypeError _ => raise BTypeError "conc")
            | (SOME (BT_Power (SOME (BT_Pair (_, SOME (BT_Power (SOME (BT_Pair (_, eto1)))))))), _                                         ) => eto1
            | (_                                                                               , SOME (BT_Power (SOME (BT_Pair (_, eto2))))) => eto2
            | _                                                                                                                              => NONE 
          )
        val nxto = SOME (BT_Power (SOME (BT_Pair (SOME BT_Integer, SOME (BT_Power (SOME (BT_Pair (SOME BT_Integer, neto))))))))
        val nyto = SOME (BT_Power (SOME (BT_Pair (SOME BT_Integer, neto))))
      in
        BE_Node1 (nyto, Keyword "conc", setTypeOpt nxto x)
      end
    | typeExpr (BE_Node1 (yto, Keyword "infix",   x)) = ((typeTree2seq (yto, "infix",   x)) handle BTypeError _ => raise BTypeError "infix")
    | typeExpr (BE_Node1 (yto, Keyword "prefix",  x)) = ((typeTree2seq (yto, "prefix",  x)) handle BTypeError _ => raise BTypeError "prefix")
    | typeExpr (BE_Node1 (yto, Keyword "postfix", x)) = ((typeTree2seq (yto, "postfix", x)) handle BTypeError _ => raise BTypeError "postfix")

    | typeExpr (BE_Node1 (yto, Keyword "left",   x)) = ((typeTree2tree (yto, "left",   x)) handle BTypeError _ => raise BTypeError "left")
    | typeExpr (BE_Node1 (yto, Keyword "right",  x)) = ((typeTree2tree (yto, "right",  x)) handle BTypeError _ => raise BTypeError "right")
    | typeExpr (BE_Node1 (yto, Keyword "mirror", x)) = ((typeTree2tree (yto, "mirror", x)) handle BTypeError _ => raise BTypeError "mirror")

    | typeExpr (BE_Node1 (yto, Keyword "top", x)) =    
      let
        val xto = typeOf x
        val nyto = (
            case (xto, yto) of
              (SOME (BT_Power (SOME (BT_Pair (_, yto1)))), yto2) =>
                ((typeUnification yto1 yto2) handle BTypeError _ => raise BTypeError "top")
            | (_, yto2) => yto2
          )
        val nxto = SOME (BT_Power (SOME (BT_Pair (SOME (BT_Power (SOME (BT_Pair (SOME BT_Integer, SOME BT_Integer)))), nyto))))
      in
        BE_Node1 (nyto, Keyword "top", setTypeOpt nxto x)
      end
    | typeExpr (BE_Node1 (yto, Keyword "sons", x)) =
      let
        val xto = typeOf x
        val neto = (
            case (xto, yto) of
              (SOME (BT_Power (SOME (BT_Pair (_, eto1)))), SOME (BT_Power (SOME (BT_Pair (_, SOME (BT_Power (SOME (BT_Pair (_, eto2))))))))) => ((typeUnification eto1 eto2) handle BTypeError _ => raise BTypeError "sons")
            | (SOME (BT_Power (SOME (BT_Pair (_, eto1)))), _                                                                               ) => eto1
            | (_                                         , SOME (BT_Power (SOME (BT_Pair (_, SOME (BT_Power (SOME (BT_Pair (_, eto2))))))))) => eto2
            | _                                                                                                                              => NONE
          )
        val nxto = SOME (BT_Power (SOME (BT_Pair (SOME (BT_Power (SOME (BT_Pair (SOME BT_Integer, SOME BT_Integer)))), neto))))
        val nyto = SOME (BT_Power (SOME (BT_Pair (SOME BT_Integer, nxto))))
      in
        BE_Node1 (nyto, Keyword "sons", setTypeOpt nxto x)
      end
    | typeExpr (BE_Struct (SOME (BT_Power NONE), lst)) = typeExpr (BE_Struct (NONE, lst))
    | typeExpr (BE_Struct (NONE, lst)) = (* 要素から struct(e) への型付けのみ、逆はなし *)
      let
        fun typestructAux [] = []
          | typestructAux ((n, e) :: rest) =
            let
              val to = typeOf e
              fun elt (SOME (BT_Power x)) = x
                | elt NONE = NONE
                | elt _ = raise BTypeError ""
            in
              (elt to, n) :: (typestructAux rest)
            end
        val tonlst = typestructAux lst
      in
        if List.exists (fn (NONE, _) => true | _ => false) tonlst then
          BE_Struct (SOME (BT_Power NONE), lst)
        else
          BE_Struct (SOME (BT_Power (SOME (BT_Struct (List.map (fn (to, e) => (valOf to, e)) tonlst)))), lst)
      end
    | typeExpr (BE_Node2 (_, Keyword "arity", x, y)) =
      let
        val nxto = SOME (BT_Power (SOME (BT_Pair (SOME (BT_Power (SOME (BT_Pair (SOME BT_Integer, SOME BT_Integer)))), NONE))))
        val nyto = SOME (BT_Power (SOME (BT_Pair (SOME BT_Integer, SOME BT_Integer))))
        val nzto = SOME BT_Integer
      in
        BE_Node2 (nzto, Keyword "arity", setTypeOpt nxto x, setTypeOpt nyto y)
      end
    | typeExpr (BE_Node2 (zto, Keyword "const", x, y)) =
      let
        val xto = typeOf x
        val yto = typeOf y
        val nxto = ((
            case (yto, zto) of
              (SOME (BT_Power (SOME (BT_Pair (_, SOME (BT_Power (SOME (BT_Pair (_, xto1)))))))), SOME (BT_Power (SOME (BT_Pair (_, xto2))))) => typeUnification (typeUnification xto1 xto2) xto
            | (SOME (BT_Power (SOME (BT_Pair (_, SOME (BT_Power (SOME (BT_Pair (_, xto1)))))))), _                                         ) => typeUnification xto xto1
            | (_                                                                               , SOME (BT_Power (SOME (BT_Pair (_, xto2))))) => typeUnification xto xto2
            | _                                                                                                                              => xto
          ) handle BTypeError _ => raise BTypeError "const")
        val nyto = SOME (BT_Power (SOME (BT_Pair (SOME BT_Integer, SOME (BT_Power (SOME (BT_Pair (SOME (BT_Power (SOME (BT_Pair (SOME BT_Integer, SOME BT_Integer)))), nxto))))))))
        val nzto = SOME (BT_Power (SOME (BT_Pair (SOME (BT_Power (SOME (BT_Pair (SOME BT_Integer, SOME BT_Integer)))), xto))))
      in
        BE_Node2 (nzto, Keyword "const", setTypeOpt xto x, setTypeOpt yto y)
      end
    | typeExpr (BE_Node2 (zto, Keyword "father", x, y)) = 
      let
        val nxto = SOME (BT_Power (SOME (BT_Pair (SOME (BT_Power (SOME (BT_Pair (SOME BT_Integer, SOME BT_Integer)))), NONE))))
        val nyto = SOME (BT_Power (SOME (BT_Pair (SOME BT_Integer, SOME BT_Integer))))
        val nzto = SOME (BT_Power (SOME (BT_Pair (SOME BT_Integer, SOME BT_Integer)))) 
      in
        BE_Node2 (nzto, Keyword "father", setTypeOpt nyto y, setTypeOpt nxto x)
      end
    | typeExpr (BE_Node2 (zto, Keyword "iterate", x, y)) = 
      let
        val xto = typeOf x
        val nato = ((
            case (xto, zto) of
              (SOME (BT_Power (SOME (BT_Pair (ato1, ato2)))), SOME (BT_Power (SOME (BT_Pair (ato3, ato4))))) => List.foldl (Utils.uncurry typeUnification) NONE [ato1, ato2, ato3, ato4]
            | (_                                            , SOME (BT_Power (SOME (BT_Pair (ato3, ato4))))) => typeUnification ato3 ato4
            | (SOME (BT_Power (SOME (BT_Pair (ato1, ato2)))), _                                            ) => typeUnification ato1 ato2
            | _                                                                                              => NONE
          ) handle BTypeError _ => raise BTypeError "iterate")
        val nxto = SOME (BT_Power (SOME (BT_Pair (nato, nato))))
        val nyto = SOME BT_Integer
        val nzto = SOME (BT_Power (SOME (BT_Pair (nato, nato))))
      in
        BE_Node2 (nzto, Keyword "iterate", setTypeOpt nxto x, setTypeOpt nyto y)
      end
    | typeExpr (BE_Node2 (zto, Keyword "prj1", x, y)) = 
      let
        val xto = typeOf x
        val yto = typeOf y
        val (nato, nbto) = ((
            case (xto, yto, zto) of
              (SOME (BT_Power ato1), SOME (BT_Power bto1), SOME (BT_Power (SOME (BT_Pair (SOME (BT_Pair (ato2, bto2)), ato3))))) => (typeUnification ato1 (typeUnification ato2 ato3), typeUnification bto1 bto2)
            | (SOME (BT_Power ato1), SOME (BT_Power bto1), _                                                                   ) => (ato1                                            , bto1                     )
            | (SOME (BT_Power ato1), NONE                , SOME (BT_Power (SOME (BT_Pair (SOME (BT_Pair (ato2, bto2)), ato3))))) => (typeUnification ato1 (typeUnification ato2 ato3), bto2                     )
            | (NONE                , SOME (BT_Power bto1), SOME (BT_Power (SOME (BT_Pair (SOME (BT_Pair (ato2, bto2)), ato3))))) => (typeUnification ato2 ato3                       , typeUnification bto1 bto2)
            | (SOME (BT_Power ato1), NONE                , _                                                                   ) => (ato1                                            , NONE                     )
            | (NONE                , NONE                , SOME (BT_Power (SOME (BT_Pair (SOME (BT_Pair (ato2, bto2)), ato3))))) => (typeUnification ato2 ato3                       , bto2                     )
            | (NONE                , SOME (BT_Power bto1), _                                                                   ) => (NONE                                            , bto1                     )
            | (NONE                , NONE                , _                                                                   ) => (NONE                                            , NONE                     )
            | _ => raise BTypeError ""
          ) handle BTypeError _ => raise BTypeError "prj1")
        val nxto = SOME (BT_Power nato)
        val nyto = SOME (BT_Power nbto)
        val nzto = SOME (BT_Power (SOME (BT_Pair (SOME (BT_Pair (nato, nbto)), nato))))
      in
        BE_Node2 (nzto, Keyword "prj1", setTypeOpt nxto x, setTypeOpt nyto y)
      end
    | typeExpr (BE_Node2 (zto, Keyword "prj2", x, y)) = 
      let
        val xto = typeOf x
        val yto = typeOf y
        val (nato, nbto) = ((
            case (xto, yto, zto) of
              (SOME (BT_Power ato1), SOME (BT_Power bto1), SOME (BT_Power (SOME (BT_Pair (SOME (BT_Pair (ato2, bto2)), bto3))))) => (typeUnification ato1 ato2, typeUnification bto1 (typeUnification bto2 bto3))
            | (SOME (BT_Power ato1), SOME (BT_Power bto1), _                                                                   ) => (ato1                     , bto1                                            )
            | (SOME (BT_Power ato1), NONE                , SOME (BT_Power (SOME (BT_Pair (SOME (BT_Pair (ato2, bto2)), bto3))))) => (typeUnification ato1 ato2, typeUnification bto2 bto3                       )
            | (NONE                , SOME (BT_Power bto1), SOME (BT_Power (SOME (BT_Pair (SOME (BT_Pair (ato2, bto2)), bto3))))) => (ato2                     , typeUnification bto1 (typeUnification bto2 bto3))
            | (SOME (BT_Power ato1), NONE                , _                                                                   ) => (ato1                     , NONE                                            )
            | (NONE                , NONE                , SOME (BT_Power (SOME (BT_Pair (SOME (BT_Pair (ato2, bto2)), bto3))))) => (ato2                     , typeUnification bto2 bto3                       )
            | (NONE                , SOME (BT_Power bto1), _                                                                   ) => (NONE                     , bto1                                            )
            | (NONE                , NONE                , _                                                                   ) => (NONE                     , NONE                                            )
            | _                                                                                                                  => raise BTypeError ""
          ) handle BTypeError _ => raise BTypeError "prj2")
        val nxto = SOME (BT_Power nato)
        val nyto = SOME (BT_Power nbto)
        val nzto = SOME (BT_Power (SOME (BT_Pair (SOME (BT_Pair (nato, nbto)), nbto))))
      in
        BE_Node2 (nzto, Keyword "prj2", setTypeOpt nxto x, setTypeOpt nyto y)
      end
    | typeExpr (BE_Node2 (zto, Keyword "rank", x, y)) = 
      let
        val xto = typeOf x
        val xto1 = SOME (BT_Power (SOME (BT_Pair (SOME (BT_Power (SOME (BT_Pair (SOME BT_Integer, SOME BT_Integer)))), NONE))))
        val nxto = ((typeUnification xto xto1) handle BTypeError _ => raise BTypeError "rank")
        val nyto = SOME (BT_Power (SOME (BT_Pair (SOME BT_Integer, SOME BT_Integer))))
        val nzto = SOME BT_Integer
      in
        BE_Node2 (nzto, Keyword "rank", setTypeOpt nxto x, setTypeOpt nyto y)
      end
    | typeExpr (BE_Node2 (zto, Keyword "subtree", x, y)) = 
      let
        val xto = typeOf x
        val nato = (
            case (xto, zto) of
              (SOME (BT_Power (SOME (BT_Pair (_, ato1)))), SOME (BT_Power (SOME (BT_Pair (_, ato2))))) => ((typeUnification ato1 ato2) handle BTypeError _ => raise BTypeError "subtree")
            | (SOME (BT_Power (SOME (BT_Pair (_, ato1)))), _                                         ) => ato1
            | (_                                         , SOME (BT_Power (SOME (BT_Pair (_, ato2))))) => ato2
            | _                                                                                        => NONE
          )
        val nxto = SOME (BT_Power (SOME (BT_Pair (SOME (BT_Power (SOME (BT_Pair (SOME BT_Integer, SOME BT_Integer)))), nato))))
        val nyto = SOME (BT_Power (SOME (BT_Pair (SOME BT_Integer, SOME BT_Integer))))
        val nzto = SOME (BT_Power (SOME (BT_Pair (SOME (BT_Power (SOME (BT_Pair (SOME BT_Integer, SOME BT_Integer)))), nato))))
      in
        BE_Node2 (nzto, Keyword "subtree", setTypeOpt nxto x, setTypeOpt nyto y)
      end
    | typeExpr (BE_NodeN (yto, Keyword "bin", [x])) = 
      let
        val xto = typeOf x
        val nxto = (
            case yto of
              (SOME (BT_Power (SOME (BT_Pair (_, xto1))))) => ((typeUnification xto xto1) handle BTypeError _ => raise BTypeError "bin")
            | _                                            => NONE
          )
        val nyto = SOME (BT_Power (SOME (BT_Pair (SOME (BT_Power (SOME (BT_Pair (SOME BT_Integer, SOME BT_Integer)))), nxto))))
      in
        BE_NodeN (nyto, Keyword "bin", [setTypeOpt nxto x])
      end
    
 
    | typeExpr (BE_NodeN (yto, Keyword "bin", [l, x, r])) =
      let
        val xto = typeOf x
        val lto = typeOf l
        val rto = typeOf r
        val nxto = ((
            case (lto, rto, yto) of
              ((SOME (BT_Power (SOME (BT_Pair (_, xto1))))), (SOME (BT_Power (SOME (BT_Pair (_, xto2))))), (SOME (BT_Power (SOME (BT_Pair (_, xto3)))))) => List.foldl (Utils.uncurry typeUnification) xto [xto1, xto2, xto3]
            | ((SOME (BT_Power (SOME (BT_Pair (_, xto1))))), (SOME (BT_Power (SOME (BT_Pair (_, xto2))))), _                                           ) => List.foldl (Utils.uncurry typeUnification) xto [xto1, xto2]
            | ((SOME (BT_Power (SOME (BT_Pair (_, xto1))))), _                                           , (SOME (BT_Power (SOME (BT_Pair (_, xto3)))))) => List.foldl (Utils.uncurry typeUnification) xto [xto1, xto3]
            | (_                                           , (SOME (BT_Power (SOME (BT_Pair (_, xto2))))), (SOME (BT_Power (SOME (BT_Pair (_, xto3)))))) => List.foldl (Utils.uncurry typeUnification) xto [xto2, xto3]
            | ((SOME (BT_Power (SOME (BT_Pair (_, xto1))))), _                                           , _                                           ) => typeUnification xto xto1
            | (_                                           , (SOME (BT_Power (SOME (BT_Pair (_, xto2))))), _                                           ) => typeUnification xto xto2
            | (_                                           , _                                           , (SOME (BT_Power (SOME (BT_Pair (_, xto3)))))) => typeUnification xto xto3
            | _                                                                                                                                          => raise BTypeError ""
          ) handle BTypeError _ => raise BTypeError "bin")
        val nyto = (SOME (BT_Power (SOME (BT_Pair (SOME (BT_Power (SOME (BT_Pair (SOME BT_Integer, SOME BT_Integer)))), nxto)))))
        val nlto = (SOME (BT_Power (SOME (BT_Pair (SOME (BT_Power (SOME (BT_Pair (SOME BT_Integer, SOME BT_Integer)))), nxto)))))
        val nrto = (SOME (BT_Power (SOME (BT_Pair (SOME (BT_Power (SOME (BT_Pair (SOME BT_Integer, SOME BT_Integer)))), nxto)))))
      in
        BE_NodeN (nyto, Keyword "bin", [setTypeOpt nlto l, setTypeOpt nxto x, setTypeOpt nrto r])
      end
    | typeExpr (BE_NodeN (_, Keyword "bin", _)) = raise BTypeError ""
    | typeExpr (BE_NodeN (sto, Keyword "son", [x, y, z])) = 
      let
        val xto = typeOf x
        val nxto = ((typeUnification xto (SOME (BT_Power (SOME (BT_Pair (SOME (BT_Power (SOME (BT_Pair (SOME BT_Integer, SOME BT_Integer)))), NONE)))))) handle BTypeError _ => raise BTypeError "son")
        val nyto = SOME (BT_Power (SOME (BT_Pair (SOME BT_Integer, SOME BT_Integer))))
        val nzto = SOME BT_Integer
        val nsto = SOME (BT_Power (SOME (BT_Pair (SOME BT_Integer, SOME BT_Integer))))
      in
        BE_NodeN (nsto, Keyword "son", [setTypeOpt nxto x, setTypeOpt nyto y, setTypeOpt nzto z])
      end
    | typeExpr (BE_NodeN (_, Keyword "son", _)) = raise BTypeError ""

    (* ラベル付きの要素の型からレコード全体の型への推論 *)
    | typeExpr (x as (BE_Rec (NONE, (l as ((SOME _, _) :: rest))))) = 
      let
        val lo = List.map (fn (SOME s, e) => (typeOf e, s) | _ => raise BTypeError "") l
      in
        if List.exists (fn (NONE, _) => true | _ => false) lo then
          x          
        else
          let
            val nl = List.map (fn (SOME t, s) => (t, s) | _ => raise BTypeError "") lo
          in
            BE_Rec (SOME (BT_Struct nl), l)
          end
      end
    (* レコード全体の型と要素の型の相互への推論 *)
    | typeExpr (x as (BE_Rec (SOME (BT_Struct l1), l2))) = 
      let
        val tl1 = List.map (fn (t, s) => (SOME t, s)) l1
        val tl2 = List.map (fn (_, e) => (typeOf e, e)) l2
        val tl12 = ListPair.zip (tl1, tl2)
        val nl2 = List.map (fn ((to1, s), (to2, e)) => let val to = ((typeUnification to1 to2) handle BTypeError _ => raise BTypeError "rec") in (SOME s, setTypeOpt to e) end) tl12
        val nl1 = List.map (fn (SOME s, e) => (case typeOf e of NONE => raise BTypeError "" | SOME t => (t, s)) | _ => raise BTypeError "") nl2
      in
        BE_Rec (SOME (BT_Struct nl1), nl2)
      end
    
    (* BE_Rec of BType option * (string option * BExpr) list *)
    (* BT_Struct of (BType * string) list *)
    | typeExpr (x as (BE_Rec _)) = x
    | typeExpr (BE_ExSet (sto, es)) =
      let
        val eto = ((List.foldl (Utils.uncurry typeUnification) NONE (List.map typeOf es)) handle BTypeError _ => raise BTypeError "{...}")
        val neto = (case sto of
              SOME (BT_Power eto1) => ((typeUnification eto eto1) handle BTypeError _ => raise BTypeError "{...}")
            | NONE => eto
            | _ => raise BTypeError ""
          )
        val nsto = SOME (BT_Power neto)
      in
        BE_ExSet (nsto, List.map (setTypeOpt neto) es)
      end
    | typeExpr (BE_Commutative (to, Keyword tk, es)) =
      let
        val tentativeType = if tk = "/\\" orelse tk = "\\/" then (SOME (BT_Power NONE)) else NONE
        val eto = ((List.foldl (Utils.uncurry typeUnification) tentativeType (List.map typeOf es)) handle BTypeError _ => raise BTypeError tk)
        val nto = ((typeUnification eto to) handle BTypeError _ => raise BTypeError tk)
      in
        BE_Commutative (nto, Keyword tk, List.map (setTypeOpt nto) es)
      end
      
    | typeExpr (BE_InSet (sto, vlst, BP ps)) =
      let
        val oenv = List.map (fn v => (v, NONE)) vlst
        val nenv = getEnv oenv ps
        val tlst = List.map (fn (_, to) => to) nenv
        fun typeTree x [] = x
          | typeTree x (y :: ys) = typeTree (SOME (BT_Pair (x, y))) ys
        val nto = ((typeUnification sto (SOME (BT_Power (typeTree (hd tlst) (tl tlst))))) handle BTypeError _ => raise BTypeError "{ | }")
      in
        BE_InSet (nto, vlst, BP (typeExprTree (setEnv nenv ps)))
      end
    | typeExpr (BE_ForAll (vlst, BP p1, BP p2)) =
      let
        val oenv = List.map (fn v => (v, NONE)) vlst
        val nenv = getEnv oenv p1
      in
        BE_ForAll (vlst, BP (typeExprTree (setEnv nenv p1)), BP (typeExprTree (setEnv nenv p2)))
      end
    | typeExpr (BE_Exists (vlst, BP p)) =
      let
        val oenv = List.map (fn v => (v, NONE)) vlst
        val nenv = getEnv oenv p
      in
        BE_Exists (vlst, BP (typeExprTree (setEnv nenv p)))
      end
    | typeExpr (BE_Seq (sto, es)) =
      let
        val eto = ((List.foldl (Utils.uncurry typeUnification) NONE (List.map typeOf es)) handle BTypeError _ => raise BTypeError "[...]")
        val neto = (case sto of
              SOME (BT_Power (SOME (BT_Pair (_, eto1)))) => ((typeUnification eto eto1) handle BTypeError _ => raise BTypeError "[...]")
            | SOME (BT_Power NONE                      ) => eto
            | NONE => eto
            | _ => raise BTypeError ""
          )
        val nsto = SOME (BT_Power (SOME (BT_Pair (SOME BT_Integer, neto))))
      in
        BE_Seq (nsto, List.map (setTypeOpt neto) es)
      end
    | typeExpr (BE_Lambda (lto, vlst, BP ps, e)) =
      let
        val oenv = List.map (fn v => (v, NONE)) vlst
        val nenv = getEnv oenv ps
        val tlst = List.map (fn (_, to) => to) nenv
        fun typeTree x [] = x
          | typeTree x (y :: ys) = typeTree (SOME (BT_Pair (x, y))) ys
        val domto = typeTree (hd tlst) (tl tlst)
        val ne = typeExprTree (setEnv nenv e)
        val ranto = typeOf ne
        val (ndomto, nranto) =
          case lto of
            SOME (BT_Power (SOME (BT_Pair (dto, rto)))) => ((typeUnification dto domto, typeUnification rto ranto) handle BTypeError _ => raise BTypeError "%")
          | _                                           => (domto                     , ranto                    )
        val nlto = SOME (BT_Power (SOME (BT_Pair (ndomto, nranto))))
      in
        BE_Lambda (nlto, vlst, BP ps, setTypeOpt nranto ne)
      end
    | typeExpr (BE_Sigma (to, x, BP ps, e)) = 
      let
        val eto = typeOf e
        val nenv = getEnv [(x, NONE)] ps
        val ne  = typeExprTree (setEnv nenv e)
        val nps = typeExprTree (setEnv nenv ps)
        val nto = (typeUnification to eto handle BTypeError _ => raise BTypeError "SIGMA")
      in
        BE_Sigma (nto, x, BP nps, setTypeOpt nto ne)
      end
    | typeExpr (BE_Pi (to, x, BP ps, e)) = 
      let
        val eto = typeOf e
        val nenv = getEnv [(x, NONE)] ps
        val ne  = typeExprTree (setEnv nenv e)
        val nps = typeExprTree (setEnv nenv ps)
        val nto = (typeUnification to eto handle BTypeError _ => raise BTypeError "SIGMA")
      in
        BE_Pi (nto, x, BP nps, setTypeOpt nto ne)
      end

    | typeExpr (BE_Inter (to, vlst, BP ps, e)) = ((typeQuantified "INTER" to vlst ps e) handle BTypeError _ => raise BTypeError "Inter")
    | typeExpr (BE_Union (to, vlst, BP ps, e)) = ((typeQuantified "UNION" to vlst ps e) handle BTypeError _ => raise BTypeError "Union")
    
    | typeExpr x = x (* 型推論できないものはスルー *)
  and
    typeQuantified kind to vlst ps e =
      let
        val oenv = List.map (fn v => (v, NONE)) vlst
        val nenv = getEnv oenv ps
        val ne = typeExprTree (setEnv nenv e)
        val nto = typeUnification to (typeOf ne)
      in
        case kind of
          "INTER" => BE_Inter (nto, vlst, BP ps, setTypeOpt nto ne)
        | "UNION" => BE_Union (nto, vlst, BP ps, setTypeOpt nto ne)
        | _ => raise BTypeError ""
      end
  and
    typeTree2tree (yto, s, x) =
      let
        val xto = typeOf x
        val neto = (
            case (xto, yto) of
              (SOME (BT_Power (SOME (BT_Pair (_, eto1)))), SOME (BT_Power (SOME (BT_Pair (_, eto2))))) => typeUnification eto1 eto2
            | (SOME (BT_Power (SOME (BT_Pair (_, eto1)))), _                                         ) => eto1
            | (_                                         , SOME (BT_Power (SOME (BT_Pair (_, eto2))))) => eto2
            | _ => NONE
          )
        val nxto = SOME (BT_Power (SOME (BT_Pair (SOME (BT_Power (SOME (BT_Pair (SOME BT_Integer, SOME BT_Integer)))), neto))))
        val nyto = SOME (BT_Power (SOME (BT_Pair (SOME (BT_Power (SOME (BT_Pair (SOME BT_Integer, SOME BT_Integer)))), neto))))
      in
        BE_Node1 (nyto, Keyword s, setTypeOpt nxto x)
      end

  and
    typeTree2seq (yto, s, x) =
      let
        val xto = typeOf x
        val neto = (
            case (xto, yto) of
              (SOME (BT_Power (SOME (BT_Pair (_, eto1)))), SOME (BT_Power (SOME (BT_Pair (_, eto2))))) => typeUnification eto1 eto2
            | (SOME (BT_Power (SOME (BT_Pair (_, eto1)))), _                                         ) => eto1
            | (_                                         , SOME (BT_Power (SOME (BT_Pair (_, eto2))))) => eto2
            | _                                                                                        => NONE
          )
        val nxto = SOME (BT_Power (SOME (BT_Pair (SOME (BT_Power (SOME (BT_Pair (SOME BT_Integer, SOME BT_Integer)))), neto))))
        val nyto = SOME (BT_Power (SOME (BT_Pair (SOME BT_Integer, neto))))
      in
        BE_Node1 (nyto, Keyword s, setTypeOpt nxto x)
      end
  and
    typeTrees (yto, s, x) =
      let
        val xto = typeOf x
        val neto = (
            case (xto, yto) of
              (SOME (BT_Power eto1), SOME (BT_Power (SOME (BT_Power (SOME (BT_Pair (_, eto2))))))) => typeUnification eto1 eto2
            | (NONE                , SOME (BT_Power (SOME (BT_Power (SOME (BT_Pair (_, eto2))))))) => eto2
            | (SOME (BT_Power eto1), _                                                           ) => eto1
            | (NONE                , _                                                           ) => NONE
            | _ => raise BTypeError ""
          )
        val nxto = SOME (BT_Power neto)
        val nyto = SOME (BT_Power (SOME (BT_Power (SOME (BT_Pair (SOME (BT_Power (SOME (BT_Pair (SOME BT_Integer, SOME BT_Integer)))), neto))))))
      in
        BE_Node1 (nyto, Keyword s, setTypeOpt nxto x)
      end
  and
    typeSeqConvert (yto, s, x) =
      let 
        val xto = typeOf x
        val neto = (
            case (xto, yto) of
              (SOME (BT_Power (SOME (BT_Pair (_, eto1)))), SOME (BT_Power (SOME (BT_Pair (_, eto2))))) => typeUnification eto1 eto2
            | (SOME (BT_Power (SOME (BT_Pair (_, eto1)))), _                                         ) => eto1
            | (_                                         , SOME (BT_Power (SOME (BT_Pair (_, eto2))))) => eto2
            | _                                                                                        => NONE
          )
        val nxto = SOME (BT_Power (SOME (BT_Pair (SOME BT_Integer, neto))))
        val nyto = nxto
      in
        BE_Node1 (nyto, Keyword s, setTypeOpt nxto x)
      end
  and
    typeSeqset (yto, s, x) =
      let
        val xto = typeOf x
        val neto = (
            case (xto, yto) of
             (SOME (BT_Power eto1), SOME (BT_Power (SOME (BT_Power (SOME (BT_Pair (_, eto2))))))) => typeUnification eto1 eto2
            |(NONE                , SOME (BT_Power (SOME (BT_Power (SOME (BT_Pair (_, eto2))))))) => eto2
            |(SOME (BT_Power eto1), _                                                           ) => eto1
            |(NONE                , _                                                           ) => NONE
            | _                                                                                   => raise BTypeError ""
          )
        val nxto = SOME (BT_Power neto)
        val nyto = SOME (BT_Power (SOME (BT_Power (SOME (BT_Pair (SOME BT_Integer, neto))))))
      in
        BE_Node1 (nyto, Keyword s, setTypeOpt nxto x)
      end
  and
    typeClosure (fto, s, g) = 
      let
        val gto = typeOf g
        val nxto = (
            case (fto, gto) of
              (SOME (BT_Power (SOME (BT_Pair (xto1, xto2)))), SOME (BT_Power (SOME (BT_Pair (xto3, xto4))))) => typeUnification xto1 (typeUnification xto2 (typeUnification xto3 xto4))
            | (SOME (BT_Power (SOME (BT_Pair (xto1, xto2)))), _                                            ) => typeUnification xto1 xto2
            | (_                                            , SOME (BT_Power (SOME (BT_Pair (xto3, xto4))))) => typeUnification xto3 xto4
            | _                                                                                              => NONE
          )
        val nfto = SOME (BT_Power (SOME (BT_Pair (nxto, nxto))))
        val ngto = nfto
      in
        BE_Node1 (nfto, Keyword s, setTypeOpt ngto g)
      end
  and
    typeUiset (yto, s, x) =
      let
        val xto = typeOf x
        val neto = (
            case (xto, yto) of
              (SOME (BT_Power (SOME (BT_Power eto1))), (SOME (BT_Power eto2))) => typeUnification eto1 eto2
            | (_                                     , (SOME (BT_Power eto2))) => eto2
            | (SOME (BT_Power (SOME (BT_Power eto1))), _                     ) =>  eto1
            | (_                                     , NONE                  ) => NONE
            | _                                                                => raise BTypeError ""
          )
        val nxto = SOME (BT_Power (SOME (BT_Power neto)))
        val nyto = SOME (BT_Power neto)
      in
        BE_Node1 (nyto, Keyword s, setTypeOpt nxto x)
      end
  and
    typeFlseq (yto, s, x) = 
      let
        val xto = typeOf x
        val nyto = (
            case xto of
              (SOME (BT_Power (SOME (BT_Pair (_, eto))))) => typeUnification yto eto
            | _                                           => yto
          )
        val nxto = SOME (BT_Power (SOME (BT_Pair (SOME BT_Integer, nyto))))
      in
        BE_Node1 (nyto, Keyword s, setTypeOpt nxto x)
      end
  and
    typePow (yto, s, x) =
      let
        val xto = typeOf x
        val nato = (
            case (xto, yto) of
              (SOME (BT_Power ato1), SOME (BT_Power (SOME (BT_Power ato2)))) => typeUnification ato1 ato2
            | (SOME (BT_Power ato1), _                                     ) => ato1
            | (NONE                , SOME (BT_Power (SOME (BT_Power ato2)))) => ato2
            | (NONE                , _                                     ) => NONE
            | _                                                              => raise BTypeError ""
          )
        val nxto = SOME (BT_Power nato)
        val nyto = SOME (BT_Power nxto)
      in
        BE_Node1 (nyto, Keyword s, setTypeOpt nxto x)
      end
  and
    typeMinmax (yto, s, x) = 
      let
        val xto = typeOf x
        val nyto = (
            case xto of
              SOME (BT_Power bto) => typeUnification bto yto
            | NONE                => yto
            | _                   => raise BTypeError ""
          )
        val nxto = SOME (BT_Power nyto)
      in
        BE_Node1 (nyto, Keyword s, setTypeOpt nxto x)
      end
  and
    typeRseq (zto, x, y, s) =
      let
        val nxto = (
            case typeUnification (typeOf x) zto of
              (SOME (BT_Power (SOME (BT_Pair (_, eto))))) => (SOME (BT_Power (SOME (BT_Pair (SOME BT_Integer, eto)))))
            | _                                           => (SOME (BT_Power (SOME (BT_Pair (SOME BT_Integer, NONE)))))
          )
      in
        BE_Node2 (nxto, Keyword s, setTypeOpt nxto x, setType BT_Integer y)
      end
  and
    typeRanOperations (zto, x, y, s) =
      let
        val xto = typeOf x
        val yto = typeOf y
        val (nato, nbto) = 
          (case (xto, yto, zto) of
              (SOME (BT_Power (SOME (BT_Pair (ato1, bto1)))), SOME (BT_Power bto2), SOME (BT_Power (SOME (BT_Pair (ato3, bto3))))) =>
              ((typeUnification ato1 ato3, typeUnification bto1 (typeUnification bto2 bto3)))

            | (_,                                             SOME (BT_Power bto2), SOME (BT_Power (SOME (BT_Pair (ato3, bto3))))) => 
              ((ato3, typeUnification bto2 bto3))

            | (SOME (BT_Power (SOME (BT_Pair (ato1, bto1)))), NONE                , SOME (BT_Power (SOME (BT_Pair (ato3, bto3))))) =>
              ((typeUnification ato1 ato3, typeUnification bto1 bto3))

            | (SOME (BT_Power (SOME (BT_Pair (ato1, bto1)))), SOME (BT_Power bto2), _                                            ) =>
              ((ato1, typeUnification bto1 bto2))

            | (SOME (BT_Power (SOME (BT_Pair (ato1, bto1)))), NONE                , _                                            ) =>
              ((ato1, bto1))

            | (_,                                             SOME (BT_Power bto2), _                                            ) =>
              ((NONE, bto2))

            | (_,                                             NONE                , SOME (BT_Power (SOME (BT_Pair (ato3, bto3))))) =>
              ((ato3, bto3))

            | (_,                                             NONE                , _                                            ) =>
              ((NONE, NONE))

            | _ => raise BTypeError ""
          )
        val nxto = SOME (BT_Power (SOME (BT_Pair (nato, nbto))))
        val nyto = SOME (BT_Power nbto)
        val nzto = nxto
      in
        BE_Node2 (nzto, Keyword s, setTypeOpt nxto x, setTypeOpt nyto y)
      end
  and
    typeDomOperations (zto, x, y, s) =
      let
        val xto = typeOf x
        val yto = typeOf y
        val (nato, nbto) = 
          (case (xto, yto, zto) of
              (SOME (BT_Power ato1), SOME (BT_Power (SOME (BT_Pair (ato2, bto2)))), SOME (BT_Power (SOME (BT_Pair (ato3, bto3))))) => (typeUnification ato1 (typeUnification ato2 ato3), typeUnification bto2 bto3)
            | (SOME (BT_Power ato1), _                                            , SOME (BT_Power (SOME (BT_Pair (ato3, bto3))))) => (typeUnification ato1 ato3                       , bto3                     )
            | (NONE                , SOME (BT_Power (SOME (BT_Pair (ato2, bto2)))), SOME (BT_Power (SOME (BT_Pair (ato3, bto3))))) => (typeUnification ato2 ato3                       , typeUnification bto2 bto3)
            | (SOME (BT_Power ato1), SOME (BT_Power (SOME (BT_Pair (ato2, bto2)))), _                                            ) => (typeUnification ato1 ato2                       , bto2                     )
            | (NONE                , SOME (BT_Power (SOME (BT_Pair (ato2, bto2)))), _                                            ) => (ato2                                            , bto2                     )
            | (SOME (BT_Power ato1), _                                            , _                                            ) => (ato1                                            , NONE                     )
            | (NONE                , _                                            , SOME (BT_Power (SOME (BT_Pair (ato3, bto3))))) => (ato3                                            , bto3                     )
            | (NONE                , NONE                                         , _                                            ) => (NONE                                            , NONE                     )
            | _                                                                                                                    => raise BTypeError ""
          )
        val nxto = SOME (BT_Power nato)
        val nyto = SOME (BT_Power (SOME (BT_Pair (nato, nbto))))
        val nzto = nyto
      in
        BE_Node2 (nzto, Keyword s, setTypeOpt nxto x, setTypeOpt nyto y)
      end
  and
    typeRelationsets (zto, x, y, s) = 
      let
        val xto = typeOf x
        val yto = typeOf y
        val (nato, nbto) = 
          (case (xto, yto, zto) of
              (SOME (BT_Power ato1), SOME (BT_Power bto1), SOME (BT_Power (SOME (BT_Power (SOME (BT_Pair (ato2, bto2))))))) => (typeUnification ato1 ato2, typeUnification bto1 bto2)
            | (NONE                , SOME (BT_Power bto1), SOME (BT_Power (SOME (BT_Power (SOME (BT_Pair (ato2, bto2))))))) => (ato2                     , typeUnification bto1 bto2)
            | (SOME (BT_Power ato1), NONE                , SOME (BT_Power (SOME (BT_Power (SOME (BT_Pair (ato2, bto2))))))) => (typeUnification ato1 ato2, bto2                     )
            | (NONE                , NONE                , SOME (BT_Power (SOME (BT_Power (SOME (BT_Pair (ato2, bto2))))))) => (ato2                     , bto2                     )
            | (SOME (BT_Power ato1), SOME (BT_Power bto1), _                                                              ) => (ato1                     , bto1                     )
            | (SOME (BT_Power ato1), NONE                , _                                                              ) => (ato1                     , NONE                     )
            | (NONE                , SOME (BT_Power bto1), _                                                              ) => (NONE                     , bto1                     )
            | (NONE                , NONE                , _                                                              ) => (NONE                     , NONE                     )
            | _                                                                                                             => raise BTypeError ""
          )
        val nxto = SOME (BT_Power nato)
        val nyto = SOME (BT_Power nbto)
        val nzto = SOME (BT_Power (SOME (BT_Power (SOME (BT_Pair (nato, nbto))))))
      in
        BE_Node2 (nzto, Keyword s, setTypeOpt nxto x, setTypeOpt nyto y)
      end
  and
    kwXxx (x, y, zto, s) = (* x * x -> x *)
      let
        fun sameType3 (a, b, cto) = (* x * x -> x *)
            let
              val ato = typeOf a
              val bto = typeOf b
              val to = typeUnification cto (typeUnification ato bto)
            in
              (setTypeOpt to a, setTypeOpt to b, to)
            end

        val (nx, ny, nzto) = sameType3 (x, y, zto)
      in
        BE_Node2 (nzto, Keyword s, nx, ny)
      end
  and
    kwXxp (x, y, s) = (* x * x -> p *)
      let
        fun sameType2 (a, b) = (* x * x -> p *)
            let
              val ato = typeOf a
              val bto = typeOf b
              val resto = typeUnification ato bto
            in
              (setTypeOpt resto a, setTypeOpt resto b)
            end 
        val (nx, ny) = sameType2 (x, y)
      in
        BE_Node2 (SOME BT_Predicate, Keyword s, nx, ny)
      end
  and
  (* 型情報明示のための関数群 *)
  (* 型情報が欠落していると失敗するため、必ず型推論を行った直後に呼び出すこと *)
  (* モジュール未対応 *)
    presentTypeInfoInComponent (BMch (machineName, machineParams, clauses)) =
      let
        val scalarMachineParams = List.filter (fn (Var x) => isTypeSetByName x | _ => raise BTypeError "invalid form of machine parameter") machineParams
        val cconstants = case (List.find (fn (BC_CCONSTANTS _) => true | _ => false) clauses) of NONE => [] | (SOME (BC_CCONSTANTS l)) => l | _ => raise BTypeError ""
        val aconstants = case (List.find (fn (BC_ACONSTANTS _) => true | _ => false) clauses) of NONE => [] | (SOME (BC_ACONSTANTS l)) => l | _ => raise BTypeError ""
        val constants = cconstants @ aconstants
        val cvariables = case (List.find (fn (BC_CVARIABLES _) => true | _ => false) clauses) of NONE => [] | (SOME (BC_CVARIABLES l)) => l | _ => raise BTypeError ""
        val avariables = case (List.find (fn (BC_AVARIABLES _) => true | _ => false) clauses) of NONE => [] | (SOME (BC_AVARIABLES l)) => l | _ => raise BTypeError ""
        val variables = cvariables @ avariables
        val newClauses = List.map (presentTypeInfoInClause scalarMachineParams constants variables) clauses
      in
        AST.mapExprsInComponent presentTypeInfoInExpr (BMch (machineName, machineParams, newClauses))
      end
    (* リファインメントや実装が入力された場合 *)
    | presentTypeInfoInComponent _ = raise BTypeError "this system is only for B machines."
  and
    presentTypeInfoInClause [] _ _ (BC_CONSTRAINTS p) = BC_CONSTRAINTS p
    | presentTypeInfoInClause machineParams _ _ (BC_CONSTRAINTS (BP e)) =
      let
        val emptyEnv = List.map (fn (Var x) => (Var x, if isTypeSetByName x then (SOME (BT_Power (SOME (BT_Deferred x)))) else NONE) | _ => raise BTypeError "invalid machine parameter") machineParams
        val env = getEnv emptyEnv e
      in
        if
          List.all (fn (_, to) => isFixedType to) env
        then
          BC_CONSTRAINTS (BP (BE_Node2 (SOME BT_Predicate, Keyword "&", envToExpr env, e)))
        else
          raise BTypeError "type inference is not completed."
      end
    | presentTypeInfoInClause _ [] _ (BC_PROPERTIES p) = BC_PROPERTIES p
    | presentTypeInfoInClause _ constants _ (BC_PROPERTIES (BP e)) =
      let
        val emptyEnv = List.map (fn v => (v, NONE)) constants
        val env = getEnv emptyEnv e
      in
        if
          List.all (fn (_, to) => isFixedType to) env
        then
          BC_PROPERTIES (BP (BE_Node2 (SOME BT_Predicate, Keyword "&", envToExpr env, e)))
        else
          raise BTypeError "type inference is not completed."
      end
    | presentTypeInfoInClause _ _ [] (BC_INVARIANT p) = BC_INVARIANT p
    | presentTypeInfoInClause _ _ variables (BC_INVARIANT (BP e)) =
      let
        val emptyEnv = List.map (fn v => (v, NONE)) variables
        val env = getEnv emptyEnv e
      in
        if
          List.all (fn (_, to) => isFixedType to) env
        then
          BC_INVARIANT (BP (BE_Node2 (SOME BT_Predicate, Keyword "&", envToExpr env, e)))
        else
          raise BTypeError "type inference is not completed."
      end
    | presentTypeInfoInClause _ _ _ (BC_OPERATIONS oprs) = 
      let
        (* PREにおける入力パラメータの型付け *)
        fun presentTypeInfoInPrecondition (BOp (oprName, outputParams, [], s)) = BOp (oprName, outputParams, [], s)
          | presentTypeInfoInPrecondition (BOp (oprName, outputParams, inputParams, BS_Precondition (BP e, s))) = 
            let
              val emptyEnv = List.map (fn v => (v, NONE)) inputParams
              val env = getEnv emptyEnv e
            in
              if
                List.all (fn (_, to) => isFixedType to) env
              then
                BOp (oprName, outputParams, inputParams, BS_Precondition (BP (BE_Node2 (SOME BT_Predicate, Keyword "&", e, envToExpr env)), s))
              else
                raise BTypeError "type inference is not completed."
            end
          | presentTypeInfoInPrecondition bop = bop
      in
        BC_OPERATIONS (List.map presentTypeInfoInPrecondition oprs)
      end
    | presentTypeInfoInClause _ _ _ c = c
  and
    (* 全称量化やラムダ式等の局所変数の型情報の明示 *)
    presentTypeInfoInExpr (BE_InSet (to, tks, BP e)) =
      let
        val emptyEnv = List.map (fn v => (v, NONE)) tks
        val env = getEnv emptyEnv e
      in
        if
          List.all (fn (_, to) => isFixedType to) env
         then
           BE_InSet (to, tks, BP (BE_Node2 (SOME BT_Predicate, Keyword "&", envToExpr env, e)))
         else
           raise BTypeError "type inference is not completed."
      end
    | presentTypeInfoInExpr (BE_ForAll (tks, BP e1, BP e2)) =
      let
        val emptyEnv = List.map (fn v => (v, NONE)) tks
        val env = getEnv emptyEnv e1
      in
        if
          List.all (fn (_, to) => isFixedType to) env
        then
          BE_ForAll (tks, BP (envToExpr env), BP (BE_Node2 (SOME BT_Predicate, Keyword "=>", e1, e2)))
        else
          raise BTypeError "type inference is not completed."
      end
    | presentTypeInfoInExpr (BE_Exists (tks, BP e)) =
      let
        val emptyEnv = List.map (fn v => (v, NONE)) tks
        val env = getEnv emptyEnv e
      in
        if
          List.all (fn (_, to) => isFixedType to) env
        then
          BE_Exists (tks, BP (BE_Node2 (SOME BT_Predicate, Keyword "&", envToExpr env, e)))
        else
          raise BTypeError "type inference is not completed."
      end
    | presentTypeInfoInExpr (BE_Lambda (to, tks, BP e1, e2)) =
      let
        val emptyEnv = List.map (fn v => (v, NONE)) tks
        val env = getEnv emptyEnv e1
      in
        if
          List.all (fn (_, to) => isFixedType to) env
        then
          BE_Lambda (to, tks, BP (BE_Node2 (SOME BT_Predicate, Keyword "&", envToExpr env, e1)), e2)
        else
          raise BTypeError "type inference is not completed."
      end
    | presentTypeInfoInExpr (BE_Sigma (to, tk, BP e1, e2)) =
      let
        val env = getEnv [(tk, NONE)] e1
      in
        if
          env <> [(tk, NONE)]
        then
          BE_Sigma (to, tk, BP (BE_Node2 (SOME BT_Predicate, Keyword "&", envToExpr env, e1)), e2)
        else
          raise BTypeError "type inference is not completed."
      end
    | presentTypeInfoInExpr (BE_Pi (to, tk, BP e1, e2)) =
      let
        val env = getEnv [(tk, NONE)] e1
      in
        if
          env <> [(tk, NONE)]
        then
          BE_Pi (to, tk, BP (BE_Node2 (SOME BT_Predicate, Keyword "&", envToExpr env, e1)), e2)
        else
          raise BTypeError "type inference is not completed."
      end
    | presentTypeInfoInExpr (BE_Inter (to, tks, BP e1, e2)) =
      let
        val emptyEnv = List.map (fn v => (v, NONE)) tks
        val env = getEnv emptyEnv e1
      in
        if
          List.all (fn (_, to) => isFixedType to) env
        then
          BE_Inter (to, tks, BP (BE_Node2 (SOME BT_Predicate, Keyword "&", envToExpr env, e1)), e2)
        else
          raise BTypeError "type inference is not completed."
      end
    | presentTypeInfoInExpr (BE_Union (to, tks, BP e1, e2)) =
      let
        val emptyEnv = List.map (fn v => (v, NONE)) tks
        val env = getEnv emptyEnv e1
      in
        if
          List.all (fn (_, to) => isFixedType to) env
        then
          BE_Union (to, tks, BP (BE_Node2 (SOME BT_Predicate, Keyword "&", envToExpr env, e1)), e2)
        else
          raise BTypeError "type inference is not completed."
      end
    | presentTypeInfoInExpr e = e
  and
      isFixedType NONE = false
    | isFixedType (SOME (BT_Power to)) = isFixedType to
    | isFixedType (SOME (BT_Pair (to1, to2))) = (isFixedType to1) andalso (isFixedType to2)
    | isFixedType _ = true
  and
    envToExpr [] = raise BTypeError "empty environment"
    | envToExpr [(v, SOME ty)] = BE_Node2 (SOME BT_Predicate, Keyword ":", BE_Leaf (SOME ty, v), typeToExpr (SOME ty))
    | envToExpr ((v, SOME ty) :: restEnv) = BE_Node2 (SOME BT_Predicate, Keyword "&", envToExpr [(v, SOME ty)], envToExpr restEnv)
    | envToExpr _ = raise BTypeError "type inference is not completed."
  and
    typeToExpr NONE = raise BTypeError "type inference is not completed."
    | typeToExpr (SOME BT_Real) =
        BE_Leaf (SOME (BT_Power (SOME BT_Real)), Keyword "REAL")
    | typeToExpr (SOME BT_Integer) =
        BE_Leaf (SOME (BT_Power (SOME BT_Integer)), Keyword "INTEGER")
    | typeToExpr (SOME BT_String) =
        BE_Leaf (SOME (BT_Power (SOME BT_String)), Keyword "STRING")
    | typeToExpr (SOME BT_Float) =
        BE_Leaf (SOME (BT_Power (SOME BT_Float)), Keyword "FLOAT")
    | typeToExpr (SOME BT_Bool) =
        BE_Leaf (SOME (BT_Power (SOME BT_Bool)), Keyword "BOOL")
    | typeToExpr (SOME (BT_Power to)) =
        BE_Node1 (SOME (BT_Power (SOME (BT_Power to))), Keyword "POW", typeToExpr to)
    | typeToExpr (SOME (BT_Pair (to1, to2))) =
        BE_Node2 (SOME (BT_Power (SOME (BT_Pair (to1, to2)))), Keyword "*", typeToExpr to1, typeToExpr to2)
    | typeToExpr (SOME (BT_Struct l)) =
        BE_Struct (SOME (BT_Power (SOME (BT_Struct l))), List.map (fn (ty, str) => (str, typeToExpr (SOME ty))) l)
    | typeToExpr (SOME (BT_Deferred str)) =
        BE_Leaf (SOME (BT_Power (SOME (BT_Deferred str))), Var str)
    | typeToExpr (SOME (BT_Enum (str, l))) =
        BE_Leaf (SOME (BT_Power (SOME (BT_Enum (str, l)))), Var str)
    | typeToExpr (SOME BT_Predicate) = raise BTypeError "invalid predicate type"

end
