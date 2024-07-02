(* DEFINITIONSは既に展開済みであるとする *)
structure IdentifierDuplication =
struct
  val digit = 3 (* 識別子のナンバリング桁数 *)
  exception IdentifierDuplicationError of string

  fun originalString s = String.extract (s, 0, SOME ((String.size s) - digit - 1)) (* α-変換前の文字列を求める *)

  fun branchBack (originalTable : (BToken * int * int) list) (branchTable : (BToken * int * int) list) =
        List.map (fn (v1, _, numberCount) => case (List.find (fn (v2, _, _) => v1 = v2) originalTable) of
                                               NONE                    => (v1, 0,          numberCount)
                                             | SOME (_, numberHere, _) => (v1, numberHere, numberCount))
                 branchTable

  fun mergeTable originalTable localVars = 
      let
        val newLocalVars = List.map (fn (Var str) => (case (List.find (fn (x, _, _) => x = Var str) originalTable) of
                                                       NONE            => Var (str ^ "_" ^ (Utils.intToFixedString digit 1))
                                                     | SOME (_, _, nc) => Var (str ^ "_" ^ (Utils.intToFixedString digit (nc + 1))))
                                      | _         => raise IdentifierDuplicationError "invalid local variable declaration") localVars (* 局所変数のリネーム *)
        val newVars = List.filter (fn v => not (List.exists (fn (x, _, _) => x = v) originalTable)) localVars (* 初出変数名のみ *)
        val newTable = List.map (fn (v, nh, nc) => if (Utils.isIn v localVars) then (v, nc + 1, nc + 1) else (v, nh, nc)) originalTable
      in
        (((List.map (fn nv => (nv, 1, 1)) newVars) @ newTable), newLocalVars)
      end

  fun renameIdsInExpr table (BE_Leaf (to, Var str)) =
      let
        val (_, number, _) = ((valOf (List.find (fn (x, _, _) => x = Var str) table)) handle Option => raise IdentifierDuplicationError ("undefined identifier \"" ^ str ^ "\""))
      in
        if
          number = 0
        then
          raise IdentifierDuplicationError ("undefined identifier \"" ^ str ^ "\"")
        else
          (table, BE_Leaf (to, Var (str ^ "_" ^ (Utils.intToFixedString digit number))))
      end
    | renameIdsInExpr table (BE_Leaf x) = (table, BE_Leaf x)
    | renameIdsInExpr table (BE_Node1 (to, opName, e)) = 
      let
        val (subExprTable, newSubExpr) = renameIdsInExpr table e
        val newTable = branchBack table subExprTable
      in
        (newTable, BE_Node1 (to, opName, newSubExpr))
      end
    | renameIdsInExpr table (BE_Node2 (to, opName, e1, e2)) =
      let
        val (subExprTable1, newSubExpr1) = renameIdsInExpr table e1
        val (subExprTable2, newSubExpr2) = renameIdsInExpr (branchBack table subExprTable1) e2
        val newTable = branchBack table subExprTable2
      in
        (newTable, BE_Node2 (to, opName, newSubExpr1, newSubExpr2))
      end
    | renameIdsInExpr table (BE_NodeN (to, opName, el)) =
      let
        val (subExprTable1, newSubExpr1) = ((renameIdsInExpr table (hd el)) handle Empty => raise IdentifierDuplicationError "the number of a builtin function arguments is wrong")
        val (btb, nsel) = 
          List.foldl (fn (e, (tb, nes)) => 
              let 
                val (ntb, ne) = renameIdsInExpr (branchBack table tb) e
              in
                (ntb, (nes @ [ne])) 
              end) 
          (subExprTable1, [newSubExpr1]) (tl el)
        val newTable = branchBack table btb
      in
        (newTable, BE_NodeN (to, opName, nsel))
      end
    | renameIdsInExpr table (BE_Fnc (to, e1, e2)) =
      let
        val (subExprTable1, newSubExpr1) = renameIdsInExpr table e1
        val (subExprTable2, newSubExpr2) = renameIdsInExpr (branchBack table subExprTable1) e2
        val newTable = branchBack table subExprTable2
      in
        (newTable, BE_Fnc (to, newSubExpr1, newSubExpr2))
      end
    | renameIdsInExpr table (BE_Img (to, e1, e2)) =
      let
        val (subExprTable1, newSubExpr1) = renameIdsInExpr table e1
        val (subExprTable2, newSubExpr2) = renameIdsInExpr (branchBack table subExprTable1) e2
        val newTable = branchBack table subExprTable2
      in
        (newTable, BE_Img (to, newSubExpr1, newSubExpr2))
      end
    | renameIdsInExpr table (BE_Bool (BP e)) =
      let
        val (subExprTable, newSubExpr) = renameIdsInExpr table e
        val newTable = branchBack table subExprTable
      in
        (newTable, BE_Bool (BP newSubExpr))
      end
    | renameIdsInExpr table (BE_ExSet (to, [])) = (table, BE_ExSet (to, []))
    | renameIdsInExpr table (BE_ExSet (to, el)) =
      let
        val (subExprTable1, newSubExpr1) = renameIdsInExpr table (hd el)
        val (btb, nsel) = 
          List.foldl (fn (e, (tb, nes)) => 
              let 
                val (ntb, ne) = renameIdsInExpr (branchBack table tb) e
              in
                (ntb, (nes @ [ne])) 
              end) 
          (subExprTable1, [newSubExpr1]) (tl el)
        val newTable = branchBack table btb
      in
        (newTable, BE_ExSet (to, nsel))
      end
    | renameIdsInExpr table (BE_InSet (to, vl, BP e)) =
      let
        val (localTable, nvl) = mergeTable table vl
        val (subExprTable, newSubExpr) = renameIdsInExpr localTable e
        val newTable = branchBack table subExprTable
      in
        (newTable, BE_InSet (to, nvl, BP newSubExpr))
      end
    | renameIdsInExpr table (BE_Seq (to, [])) = (table, BE_Seq (to, []))
    | renameIdsInExpr table (BE_Seq (to, el)) =
      let
        val (subExprTable1, newSubExpr1) = renameIdsInExpr table (hd el)
        val (btb, nsel) = 
          List.foldl (fn (e, (tb, nes)) => 
              let 
                val (ntb, ne) = renameIdsInExpr (branchBack table tb) e
              in
                (ntb, (nes @ [ne])) 
              end) 
          (subExprTable1, [newSubExpr1]) (tl el)
        val newTable = branchBack table btb
      in
        (newTable, BE_Seq (to, nsel))
      end
    | renameIdsInExpr table (BE_ForAll (vl, BP e1, BP e2)) =
      let
        val (localTable, nvl) = mergeTable table vl
        val (subExprTable1, newSubExpr1) = renameIdsInExpr localTable e1
        val (subExprTable2, newSubExpr2) = renameIdsInExpr (branchBack localTable subExprTable1) e2
        val newTable = branchBack table subExprTable2
      in
        (newTable, BE_ForAll (nvl, BP newSubExpr1, BP newSubExpr2))
      end
    | renameIdsInExpr table (BE_Exists (vl, BP e)) =
      let
        val (localTable, nvl) = mergeTable table vl
        val (subExprTable, newSubExpr) = renameIdsInExpr localTable e
        val newTable = branchBack table subExprTable
      in
        (newTable, BE_Exists (nvl, BP newSubExpr))
      end
    | renameIdsInExpr table (BE_Lambda (to, vl, BP e1, e2)) =
      let
        val (localTable, nvl) = mergeTable table vl
        val (subExprTable1, newSubExpr1) = renameIdsInExpr localTable e1
        val (subExprTable2, newSubExpr2) = renameIdsInExpr (branchBack localTable subExprTable1) e2
        val newTable = branchBack table subExprTable2
      in
        (newTable, BE_Lambda (to, nvl, BP newSubExpr1, newSubExpr2))
      end
    | renameIdsInExpr table (BE_Sigma (to, v, BP e1, e2)) =
      let
        val (localTable, [nv]) = mergeTable table [v]
        val (subExprTable1, newSubExpr1) = renameIdsInExpr localTable e1
        val (subExprTable2, newSubExpr2) = renameIdsInExpr (branchBack localTable subExprTable1) e2
        val newTable = branchBack table subExprTable2
      in
        (newTable, BE_Sigma (to, nv, BP newSubExpr1, newSubExpr2))
      end
    | renameIdsInExpr table (BE_Pi (to, v, BP e1, e2)) =
      let
        val (localTable, [nv]) = mergeTable table [v]
        val (subExprTable1, newSubExpr1) = renameIdsInExpr localTable e1
        val (subExprTable2, newSubExpr2) = renameIdsInExpr (branchBack localTable subExprTable1) e2
        val newTable = branchBack table subExprTable2
      in
        (newTable, BE_Pi (to, nv, BP newSubExpr1, newSubExpr2))
      end
    | renameIdsInExpr table (BE_Inter (to, vl, BP e1, e2)) =
      let
        val (localTable, nvl) = mergeTable table vl
        val (subExprTable1, newSubExpr1) = renameIdsInExpr localTable e1
        val (subExprTable2, newSubExpr2) = renameIdsInExpr (branchBack localTable subExprTable1) e2
        val newTable = branchBack table subExprTable2
      in
        (newTable, BE_Inter (to, nvl, BP newSubExpr1, newSubExpr2))
      end
    | renameIdsInExpr table (BE_Union (to, vl, BP e1, e2)) =
      let
        val (localTable, nvl) = mergeTable table vl
        val (subExprTable1, newSubExpr1) = renameIdsInExpr localTable e1
        val (subExprTable2, newSubExpr2) = renameIdsInExpr (branchBack localTable subExprTable1) e2
        val newTable = branchBack table subExprTable2
      in
        (newTable, BE_Union (to, nvl, BP newSubExpr1, newSubExpr2))
      end
    | renameIdsInExpr table (BE_Struct (to, [])) = raise IdentifierDuplicationError "empty struct"
    | renameIdsInExpr table (BE_Struct (to, l)) =
      let
        val (subExprTable1, newSubExpr1) =  renameIdsInExpr table (#2 (hd l))
        val (btb, nl) = 
          List.foldl (fn ((s, e), (tb, nes)) => 
              let 
                val (ntb, ne) = renameIdsInExpr (branchBack table tb) e
              in
                (ntb, (nes @ [(s, ne)])) 
              end) 
          (subExprTable1, [(#1 (hd l), newSubExpr1)]) l
        val newTable = branchBack table btb
      in
        (newTable, BE_Struct (to, nl))
      end
    | renameIdsInExpr table (BE_Rec (to, [])) = raise IdentifierDuplicationError "empty record"
    | renameIdsInExpr table (BE_Rec (to, l)) =
      let
        val (subExprTable1, newSubExpr1) =  renameIdsInExpr table (#2 (hd l))
        val (btb, nl) = 
          List.foldl (fn ((s, e), (tb, nes)) => 
              let 
                val (ntb, ne) = renameIdsInExpr (branchBack table tb) e
              in
                (ntb, (nes @ [(s, ne)])) 
              end) 
          (subExprTable1, [(#1 (hd l), newSubExpr1)]) l
        val newTable = branchBack table btb
      in
        (newTable, BE_Rec (to, nl))
      end
    | renameIdsInExpr table (BE_RcAc (to, e, str)) =
      let
        val (subExprTable, newSubExpr) = renameIdsInExpr table e
        val newTable = branchBack table subExprTable
      in
        (newTable, BE_RcAc (to, newSubExpr, str))
      end    
    | renameIdsInExpr table (BE_Commutative (to, opName, el)) =
      let
        val (subExprTable1, newSubExpr1) = ((renameIdsInExpr table (hd el)) handle Empty => raise IdentifierDuplicationError "the number of commutative operands is invalid")
        val (btb, nsel) = 
          List.foldl (fn (e, (tb, nes)) => 
              let 
                val (ntb, ne) = renameIdsInExpr (branchBack table tb) e
              in
                (ntb, (nes @ [ne])) 
              end) 
          (subExprTable1, [newSubExpr1]) (tl el)
        val newTable = branchBack table btb
      in
        (newTable, BE_Commutative (to, opName, nsel))
      end

  fun renameIdsInSubstitutions table (BS_Block s) =
      let
        val (stb, newSubs) = renameIdsInSubstitutions table s
        val newTable = branchBack table stb
      in
        (newTable, BS_Block newSubs)
      end
    | renameIdsInSubstitutions table BS_Identity = (table, BS_Identity)
    | renameIdsInSubstitutions table (BS_Precondition (BP e, s)) =
      let
        val (etb, newExpr) = renameIdsInExpr table e
        val (stb, newSubs) = renameIdsInSubstitutions (branchBack table etb) s
        val newTable = branchBack table stb
      in
        (newTable, BS_Precondition (BP newExpr, newSubs))
      end
    | renameIdsInSubstitutions table (BS_Assertion x) =
        (case (renameIdsInSubstitutions table (BS_Precondition x)) of
          (newTable, BS_Precondition y) => (newTable, BS_Assertion y)
        | _                             => raise IdentifierDuplicationError "")
    | renameIdsInSubstitutions _ (BS_Choice []) = raise IdentifierDuplicationError "empty CHOICE substitution"
    | renameIdsInSubstitutions table (BS_Choice sl) =
      let
        val (stb1, newSubs1) = renameIdsInSubstitutions table (hd sl)
        val (btb, nsl) =
          List.foldl (fn (s, (tb, nss)) =>
              let
                val (ntb, ns) = renameIdsInSubstitutions (branchBack table tb) s
              in
                (ntb, (nss @ [ns]))
              end)
          (stb1, [newSubs1]) (tl sl)
        val newTable = branchBack table btb
      in
        (newTable, BS_Choice nsl)
      end
    | renameIdsInSubstitutions table (BS_If []) = raise IdentifierDuplicationError "empty IF substitution"
    | renameIdsInSubstitutions table (BS_If ((NONE, _)::_)) = raise IdentifierDuplicationError "empty IF condition"
    | renameIdsInSubstitutions table (BS_If ((SOME (BP e1), s1)::xs)) =
      let
        val (etb1, newExpr1) = renameIdsInExpr table e1
        val (stb1, newSubs1) = renameIdsInSubstitutions (branchBack table etb1) s1
        val (btb, nbl) =
          List.foldl (fn ((SOME (BP e), s), (tb, nbs)) => let
                                                           val (etb, ne) = renameIdsInExpr (branchBack table tb) e
                                                           val (stb, ns) = renameIdsInSubstitutions (branchBack table etb) s
                                                         in
                                                           (stb, (nbs @ [(SOME (BP ne), ns)]))
                                                         end
                       | ((NONE, s), (tb, nbs)) => let
                                                     val (ntb, ns) = renameIdsInSubstitutions (branchBack table tb) s
                                                   in
                                                     (ntb, (nbs @ [(NONE, ns)]))
                                                   end)
                     (stb1, [(SOME (BP newExpr1), newSubs1)]) xs
        val newTable = branchBack table btb
      in
        (newTable, BS_If nbl)
      end
    | renameIdsInSubstitutions _ (BS_Select []) = raise IdentifierDuplicationError "empty SELECT substitution"
    | renameIdsInSubstitutions table (BS_Select ((NONE, _)::_)) = raise IdentifierDuplicationError "empty SELECT condition"
    | renameIdsInSubstitutions table (BS_Select l) =
        (case (renameIdsInSubstitutions table (BS_If l)) of
          (newTable, BS_If nbl) => (newTable, BS_Select nbl)
        | _                     => raise IdentifierDuplicationError "")
    | renameIdsInSubstitutions _ (BS_Case (_, [])) = raise IdentifierDuplicationError "empty CASE substitution"    
    | renameIdsInSubstitutions table (BS_Case (initExpr, (el1, s1)::xs)) =
      let
        val (initEtb, newInitExpr) = renameIdsInExpr table initExpr
        fun renameIdsInExprList tb [] = (branchBack table tb, [])
          | renameIdsInExprList tb (e1 :: es) =
            let
              val (e1tb, ne1) = renameIdsInExpr tb e1
              val (estb, nel) = List.foldl (fn (e, (tb, nes)) => let
                                                                   val (etb, ne) = renameIdsInExpr (branchBack table tb) e
                                                                 in
                                                                   (etb, nes @ [ne])
                                                                 end)
                                           (e1tb, [ne1]) es
              val newExprListTable = branchBack table estb
            in
              (newExprListTable, nel)
            end
        val (eltb1, newEl1) = renameIdsInExprList (branchBack table initEtb) el1
        val (stb1, newS1) = renameIdsInSubstitutions (branchBack table eltb1) s1
        val (btb, nbl) = List.foldl (fn ((el, s), (tb, nbs)) => let
                                                                  val (eltb, nel) = renameIdsInExprList (branchBack table tb) el
                                                                  val (stb, ns) = renameIdsInSubstitutions (branchBack table eltb) s
                                                                in
                                                                  (stb, nbs @ [(nel, ns)])
                                                                end)
                                    (stb1, [(newEl1, newS1)]) xs
        val newTable = branchBack table btb
      in
        (newTable, BS_Case (newInitExpr, nbl))
      end
    | renameIdsInSubstitutions table (BS_Any (vl, BP e, s)) =
      let
        val (localTable, nvl) = mergeTable table vl
        val (etb, ne) = renameIdsInExpr localTable e
        val (stb, ns) = renameIdsInSubstitutions (branchBack localTable etb) s
        val newTable = branchBack table stb
      in
        (newTable, BS_Any (nvl, BP ne, ns))
      end
    | renameIdsInSubstitutions _ (BS_Let ([], _)) = raise IdentifierDuplicationError "empty local variables declaration in LET substitution"
    | renameIdsInSubstitutions table (BS_Let (dl, s)) =
      let
        val (vl, el) = ListPair.unzip dl
        val (localTable, nvl) = mergeTable table vl
        val e1 = hd el
        val (tb1, ne1) = renameIdsInExpr localTable e1
        val (eltb, nel) = List.foldl (fn (e, (tb, nes)) => let
                                                             val (etb, ne) = renameIdsInExpr (branchBack localTable tb) e
                                                           in
                                                             (etb, nes @ [ne])
                                                           end)
                                     (branchBack localTable tb1, [ne1]) (tl el)
        val (stb, ns) = renameIdsInSubstitutions (branchBack localTable eltb) s
        val newTable = branchBack table stb
        val ndl = ListPair.zip (nvl, nel)
      in
        (newTable, BS_Let (ndl, ns))
      end
    | renameIdsInSubstitutions _     (BS_BecomesElt ([], _)) = raise IdentifierDuplicationError "empty left hand side of BECOMES ELEMENT substitution"
    | renameIdsInSubstitutions table (BS_BecomesElt ((e1 :: es), re)) =
      let
        val (e1tb, ne1) = renameIdsInExpr table e1
        val (eltb, nel) = List.foldl (fn (e, (tb, nes)) => let
                                                             val (etb, ne) = renameIdsInExpr (branchBack table tb) e
                                                           in
                                                             (etb, nes @ [ne])
                                                           end)
                                     (e1tb, [ne1]) es
        val (retb, nre) = renameIdsInExpr (branchBack table eltb) re
        val newTable = branchBack table retb
      in
        (newTable, BS_BecomesElt (nel, nre))
      end
    | renameIdsInSubstitutions table (BS_BecomesSuchThat ([], _)) = raise IdentifierDuplicationError "empty left hand side of BECOMES SUCH THAT substitution"
    | renameIdsInSubstitutions table (BS_BecomesSuchThat ((e1 :: es), BP pe)) =
      let
        val (e1tb, ne1) = renameIdsInExpr table e1
        val (eltb, nel) = List.foldl (fn (e, (tb, nes)) => let
                                                             val (etb, ne) = renameIdsInExpr (branchBack table tb) e
                                                           in
                                                             (etb, nes @ [ne])
                                                           end)
                                     (e1tb, [ne1]) es
        val (petb, npe) = renameIdsInExpr (branchBack table eltb) pe
        val newTable = branchBack table petb
      in
        (newTable, BS_BecomesSuchThat (nel, BP npe))
      end

    | renameIdsInSubstitutions table (BS_Call (opName, el1, el2)) =
      (case (renameIdsInSubstitutions table (BS_BecomesEqualList (el1, el2))) of
            (newTable, BS_BecomesEqualList (nel1, nel2)) => (newTable, BS_Call (opName, nel1, nel2))
            | _ => raise IdentifierDuplicationError "")
    | renameIdsInSubstitutions table (BS_BecomesEqual (e1, e2)) =
      let
        val (e1tb, ne1) = renameIdsInExpr table e1
        val (e2tb, ne2) = renameIdsInExpr (branchBack table e1tb) e2
        val newTable = branchBack table e2tb
      in
        (newTable, BS_BecomesEqual (ne1, ne2))
      end
    | renameIdsInSubstitutions table (BS_BecomesEqualList (el1, el2)) =
      let
        fun renameIdsInExprList tb [] = (tb, [])
          | renameIdsInExprList tb (e1 :: es) =
            let
              val (e1tb, ne1) = renameIdsInExpr tb e1
              val (estb, nel) = List.foldl (fn (e, (tb, nes)) => let
                                                                   val (etb, ne) = renameIdsInExpr (branchBack table tb) e
                                                                 in
                                                                   (etb, nes @ [ne])
                                                                 end)
                                           (e1tb, [ne1]) es
              val newExprListTable = branchBack table estb
            in
              (newExprListTable, nel)
            end
        val (el1tb, nel1) = renameIdsInExprList table el1
        val (el2tb, nel2) = renameIdsInExprList (branchBack table el1tb) el2
        val newTable = branchBack table el2tb
      in
        (newTable, BS_BecomesEqualList (nel1, nel2))
      end
    | renameIdsInSubstitutions table (BS_Simultaneous l) =
      (case (renameIdsInSubstitutions table (BS_Choice l)) of
            (newTable, BS_Choice nl) => (newTable, BS_Simultaneous nl)
            | _ => raise IdentifierDuplicationError "")
    | renameIdsInSubstitutions _ _ = raise IdentifierDuplicationError "resolving of duplication of identifiers is only for models"
            
  fun renameIdsInOp table (BOp (opName, oparams, iparams, s)) =
      let
        val (otb, noparams) = mergeTable table oparams
        val (itb, niparams) = mergeTable otb iparams
        val (stb, ns) = renameIdsInSubstitutions itb s
        val newTable = branchBack table stb
      in
        (newTable, BOp (opName, noparams, niparams, ns))
      end

  fun renameIdsInInitialisation table (BC_INITIALISATION s) =
      let
        val (stb, ns) = renameIdsInSubstitutions table s
        val newTable = branchBack table stb
      in
        (newTable, (BC_INITIALISATION ns))
      end
    | renameIdsInInitialisation _ _ = raise IdentifierDuplicationError ""
      
  fun renameIdsInOperations _ (BC_OPERATIONS []) = raise IdentifierDuplicationError ""
    | renameIdsInOperations table (BC_OPERATIONS (op1 :: ops)) =
      let
        val (op1tb, nop1) = renameIdsInOp table op1
        val (opltb, nopl) = List.foldl (fn (opr, (tb, nops)) => let
                                                                  val (oprtb, nopr) = renameIdsInOp (branchBack table tb) opr
                                                                in
                                                                  (oprtb, nops @ [nopr])
                                                                end) (op1tb, [nop1]) ops
        val newTable = branchBack table opltb
      in
        (newTable, (BC_OPERATIONS nopl))
      end
    | renameIdsInOperations _ _ = raise IdentifierDuplicationError ""
      
  fun renameIdsInConditions table (BC_CONSTRAINTS (BP e)) =
      let
        val (tb, ne) = renameIdsInExpr table e
      in
        (branchBack table tb, (BC_CONSTRAINTS (BP ne)))
      end
    | renameIdsInConditions table (BC_PROPERTIES (BP e)) =
      let
        val (tb, ne) = renameIdsInExpr table e
      in
        (branchBack table tb, (BC_PROPERTIES (BP ne)))
      end
    | renameIdsInConditions table (BC_INVARIANT (BP e)) =
      let
        val (tb, ne) = renameIdsInExpr table e
      in
        (branchBack table tb, (BC_INVARIANT (BP ne)))
      end
    | renameIdsInConditions table (BC_ASSERTIONS (BP e)) =
      let
        val (tb, ne) = renameIdsInExpr table e
      in
        (branchBack table tb, (BC_ASSERTIONS (BP ne)))
      end
    | renameIdsInConditions _ _ = raise IdentifierDuplicationError ""
  
  fun resolve (BMch (name, params, clauses)) =
      let
        val sets = case (List.find (fn (BC_SETS _) => true | _ => false) clauses) of
                     NONE => []
                   | SOME (BC_SETS tl) => tl
                   | _ => raise IdentifierDuplicationError ""
        val typeSets = List.concat (List.map (fn (BT_Deferred str) => [(Var str)] | (BT_Enum (str, _)) => [(Var str)] | _ => []) sets) 
        val enumElements = List.concat (List.map (fn (BT_Enum (_, el)) => List.map (fn str => Var str) el | _ => []) sets)
        val aconstants = case (List.find (fn (BC_ACONSTANTS _) => true | _ => false) clauses) of
                           NONE => []
                         | SOME (BC_ACONSTANTS vl) => vl
                         | _ => raise IdentifierDuplicationError ""
        val cconstants = case (List.find (fn (BC_CCONSTANTS _) => true | _ => false) clauses) of
                           NONE => []
                         | SOME (BC_CCONSTANTS vl) => vl
                         | _ => raise IdentifierDuplicationError ""
        val avariables = case (List.find (fn (BC_AVARIABLES _) => true | _ => false) clauses) of
                           NONE => []
                         | SOME (BC_AVARIABLES vl) => vl
                         | _ => raise IdentifierDuplicationError ""
        val cvariables = case (List.find (fn (BC_CVARIABLES _) => true | _ => false) clauses) of
                           NONE => []
                         | SOME (BC_CVARIABLES vl) => vl
                         | _ => raise IdentifierDuplicationError ""
        val toplevelIdentifiers = params @ typeSets @ enumElements @ aconstants @ cconstants @ avariables @ cvariables 
        (* トップレベルの識別子：マシンパラメータ、定数、変数、型集合、列挙集合の要素 *)
        fun updateTopLevel (BC_SETS tl) = 
            let
              fun updateTopLevelInternal (BT_Deferred str) = BT_Deferred (str ^ "_" ^ (Utils.intToFixedString digit 1))
                | updateTopLevelInternal (BT_Enum (str, el)) =
                    BT_Enum (str ^ "_" ^ (Utils.intToFixedString digit 1), List.map (fn x => x ^ "_" ^ (Utils.intToFixedString digit 1)) el)
                | updateTopLevelInternal _ = raise IdentifierDuplicationError "invalid SETS declaration"
            in
              (BC_SETS (List.map updateTopLevelInternal tl))
            end
          | updateTopLevel (BC_ACONSTANTS vl) =
            (BC_ACONSTANTS (List.map (fn (Var x) => Var (x ^ "_" ^ (Utils.intToFixedString digit 1))
                                          | _ => raise IdentifierDuplicationError "invalid Variable") vl))
          | updateTopLevel (BC_CCONSTANTS vl) =
            (BC_CCONSTANTS (List.map (fn (Var x) => Var (x ^ "_" ^ (Utils.intToFixedString digit 1))
                                          | _ => raise IdentifierDuplicationError "invalid Variable") vl))
          | updateTopLevel (BC_AVARIABLES vl) =
            (BC_AVARIABLES (List.map (fn (Var x) => Var (x ^ "_" ^ (Utils.intToFixedString digit 1))
                                          | _ => raise IdentifierDuplicationError "invalid Variable") vl))
          | updateTopLevel (BC_CVARIABLES vl) =
            (BC_AVARIABLES (List.map (fn (Var x) => Var (x ^ "_" ^ (Utils.intToFixedString digit 1))
                                          | _ => raise IdentifierDuplicationError "invalid Variable") vl))
          | updateTopLevel x = x
        val updatedTopLevel = List.map updateTopLevel clauses
        val initialNumberingTable = List.map (fn v => (v, 1, 1)) toplevelIdentifiers
        val (conditionClauses, clausesExceptConditions) = List.partition (fn (BC_CONSTRAINTS _) => true
                                                                           | (BC_PROPERTIES _)  => true
                                                                           | (BC_INVARIANT _)   => true
                                                                           | (BC_ASSERTIONS _)  => true
                                                                           | _ => false)
                                                                         updatedTopLevel
        val (topLevelTable, rewrittenConditions) =
          if
            conditionClauses = []
          then
            (initialNumberingTable, [])
          else
            let
              val (ntb1, nc1) = renameIdsInConditions initialNumberingTable (hd conditionClauses)
              val (ncstb, ncs) = List.foldl (fn (c, (tb, cs)) => let
                                                                   val (ntb, nc) = renameIdsInConditions (branchBack initialNumberingTable tb) c
                                                                 in
                                                                   (ntb, cs @ [nc])
                                                                 end) (ntb1, [nc1]) (tl conditionClauses)
            in
              (branchBack initialNumberingTable ncstb, ncs)
            end
        val rewrittenTopLevel = rewrittenConditions @ clausesExceptConditions
        val clausesExceptInitAndOp = List.filter (fn (BC_OPERATIONS _) => false | (BC_INITIALISATION _) => false | _ => true) rewrittenTopLevel
        val initialisationOpt = List.find (fn (BC_INITIALISATION _) => true | _ => false) rewrittenTopLevel        
        val operationsOpt     = List.find (fn (BC_OPERATIONS _)     => true | _ => false) rewrittenTopLevel
        val newClauses = (case (initialisationOpt, operationsOpt) of
                            (NONE, NONE) => rewrittenTopLevel
                          | (SOME x, NONE) => (#2 (renameIdsInInitialisation topLevelTable x)) :: clausesExceptInitAndOp
                          | (NONE, SOME x) => (#2 (renameIdsInOperations topLevelTable x)) :: clausesExceptInitAndOp
                          | (SOME x, SOME y) => let
                                                    val (itb, nini) = renameIdsInInitialisation topLevelTable x
                                                    val (_, nops) = renameIdsInOperations (branchBack topLevelTable itb) y
                                                  in
                                                    nini :: nops :: clausesExceptInitAndOp
                                                  end
                          )
      in
        BMch (name, (List.map (fn (Var x) => Var (x ^ "_" ^ (Utils.intToFixedString digit 1)) | _ => raise IdentifierDuplicationError "invalid Variable") params), newClauses)
      end

    | resolve _ = raise IdentifierDuplicationError "this program can process only Machines"
end
