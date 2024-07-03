structure Merge =
struct
  exception MergeError of string


  fun mergeExpr from to = from (* TODO *)

  fun mergeSubstitution from to = from (* TODO *)

  (* 制約条件系・Assertion *)
  fun mergeClause (BC_CONSTRAINTS (BP from)) (BC_CONSTRAINTS (BP to)) = SOME (BC_CONSTRAINTS (BP (mergeExpr from to)))
    | mergeClause (BC_PROPERTIES (BP from)) (BC_PROPERTIES (BP to)) = SOME (BC_PROPERTIES (BP (mergeExpr from to)))
    | mergeClause (BC_INVARIANT (BP from)) (BC_INVARIANT (BP to)) = SOME ( BC_INVARIANT (BP (mergeExpr from to)))
    | mergeClause (BC_ASSERTIONS (BP from)) (BC_ASSERTIONS (BP to)) = SOME ( BC_ASSERTIONS (BP (mergeExpr from to)))
    | mergeClause (BC_VALUES from) (BC_VALUES to) = SOME( BC_VALUES (from)) (* TODO *)
  (* モジュール系 *)
    | mergeClause (BC_SEES from) (BC_SEES to) = SOME( BC_SEES (from)) (* TODO *)
    | mergeClause (BC_INCLUDES from) (BC_INCLUDES to) = SOME( BC_INCLUDES (from)) (* TODO *)
    | mergeClause (BC_PROMOTES from) (BC_PROMOTES to) = SOME( BC_PROMOTES (from)) (* TODO *)
    | mergeClause (BC_EXTENDS from) (BC_EXTENDS to) = SOME( BC_EXTENDS (from)) (* TODO *)
    | mergeClause (BC_USES from) (BC_USES to) = SOME( BC_USES (from)) (* TODO *)
    | mergeClause (BC_IMPORTS from) (BC_IMPORTS to) = SOME( BC_IMPORTS (from)) (* TODO *)
  (* 変数導入系 *)
    | mergeClause (BC_CCONSTANTS from) (BC_CCONSTANTS to) = SOME( BC_CCONSTANTS (from @ to)) (* FIXME list *)
    | mergeClause (BC_ACONSTANTS from) (BC_ACONSTANTS to) = SOME( BC_ACONSTANTS (from @ to)) (* FIXME list *)
    | mergeClause (BC_CVARIABLES from) (BC_CVARIABLES to) = SOME( BC_CVARIABLES (from @ to)) (* FIXME list *)
    | mergeClause (BC_AVARIABLES from) (BC_AVARIABLES to) = SOME( BC_AVARIABLES (from @ to)) (* FIXME list *)
  (* その他 *)
    | mergeClause (BC_SETS from) (BC_SETS to) = SOME( BC_SETS (from @ to)) (* FIXME list *)
    | mergeClause (BC_INITIALISATION from) (BC_INITIALISATION to) = SOME( BC_INITIALISATION (mergeSubstitution from to))
    | mergeClause (BC_OPERATIONS from) (BC_OPERATIONS to) = SOME( BC_OPERATIONS (from @ to)) (* FIXME list *)
    | mergeClause (BC_DEFINITIONS from) (BC_DEFINITIONS to) = SOME( BC_DEFINITIONS (from @ to)) (* FIXME list *)
    | mergeClause _ _ = NONE

  fun mergeClauseList froms tos = List.map (Option.valOf) (List.filter (Option.isSome) (List.concat( List.map (fn x => List.map (mergeClause x) froms) tos)))


  fun mergeComponent (BMch (name1, tokens1, clauses1)) (BMch (name2, tokens2, clauses2)) = BMch (name1, tokens1, mergeClauseList clauses1 clauses2)

end
