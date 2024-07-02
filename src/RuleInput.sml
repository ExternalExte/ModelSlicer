structure RuleInput =
struct
  exception RuleInputError of string
  fun isCommentline s =
    if
      String.size s <= 1
    then
      false
    else
      let
        val c0 = String.sub (s, 0)
      in
        if
          Char.isSpace c0
        then
          isCommentline (String.extract (s, 1, NONE))
        else
          if
            String.isPrefix "//" s
          then
            true
          else
            false
      end
      
  fun strToRules str =
    let
      val ruleLines = Utils.tokensS "\n" str
      val commentlineRemoved = List.filter (fn x => not (isCommentline x)) ruleLines
      val rulestrAndTypestr = List.map (fn x => case (Utils.tokensS "@TYPES@" x) of [r] => (r, "") | (r :: t :: []) => (r, t) | _ => raise RuleInputError "number of @TYPES@ is wrong") commentlineRemoved
      val untypedRules = List.map (fn (x, t) => case (Utils.tokensS "@->@" x, Lexer.tokenize t) of
                                                  (e1 :: e2 :: [], []) => (#1 (Parser.pExpr (Lexer.tokenize e1)), #1 (Parser.pExpr (Lexer.tokenize e2)), NONE)
                                                | (e1 :: e2 :: [], tt) => (#1 (Parser.pExpr (Lexer.tokenize e1)), #1 (Parser.pExpr (Lexer.tokenize e2)), SOME (#1 (Parser.pExpr tt)))
                                                | _ => raise RuleInputError "number of @->@ is wrong")
                                                  rulestrAndTypestr
      val vartypeSet = List.map (fn (e1, e2, NONE) => (e1, e2)
                                         | (e1, e2, SOME p) => let
                                                                  val vlst = AST.findExprs (fn BE_Leaf (to, Var y) => true | _ => false) e1
                                                                  val oenv = List.map (fn BE_Leaf (to, Var x) => (Var x, to) | _ => raise RuleInputError "") vlst
                                                                  val nenv = TypeInference.getEnv oenv (TypeInference.typeExprTree p)
                                                                in
                                                                  (TypeInference.setEnv nenv e1, e2)
                                                                end
                                       ) untypedRules
      val typedRules = List.map (fn (e1, e2) => (TypeInference.typeExprTree e1, TypeInference.typeExprTree e2)) vartypeSet
      val commutativeConvertedRules = List.map (fn (e1, e2) => (Utils.repeatApply (AST.mapExprTree Commutative.makeCommutative)    e1, Utils.repeatApply (AST.mapExprTree Commutative.makeCommutative)    e2)) typedRules
      val commutativeFlattenedRules = List.map (fn (e1, e2) => (Utils.repeatApply (AST.mapExprTree Commutative.flattenCommutative) e1, Utils.repeatApply (AST.mapExprTree Commutative.flattenCommutative) e2)) commutativeConvertedRules
      (* ↑ここまでは全て通常の変数として解釈 *)
      (* ↓ここでリテラル変数・型集合変数・制限付き変数を判定 *)
      fun interpretSuffix (BE_Leaf (tOpt, Var x)) =
          if
            String.isSuffix "_lit" x
          then
            BE_Leaf (tOpt, VarLit x)
          else if
            String.isSuffix "_type" x
          then
            BE_Leaf (tOpt, VarTypeSet x)
          else if
            String.isSuffix "_" x
          then
            BE_Leaf (tOpt, VarSingle x)
          else
            BE_Leaf (tOpt, Var x)
        | interpretSuffix e = e
      
      val litRules = List.map (fn (e1, e2) => (AST.mapExprTree interpretSuffix e1, AST.mapExprTree interpretSuffix e2)) commutativeFlattenedRules
    in
      litRules
    end
end
(* 書き換え前 @->@ 書き換え後 @TYPES@ 型制約 *)

(* ルールどうしの区切り：改行 *)
