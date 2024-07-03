(* ML処理系の設定 *)
    (* 変数の内容を画面に出力する際に省略せず出力するデータ構造の深さ（デバッグのため十分大きな値に） *)
Control.Print.printDepth := 1000;
    (* 変数の内容を画面に出力する際に省略せず出力するリストの長さ（デバッグのため十分大きな値に） *)
Control.Print.printLength := 1000;
    (* 変数の内容を画面に出力する際に省略せず出力する文字列の長さ（デバッグのため十分大きな値に） *)
Control.Print.stringDepth := 3000;
    (* poly equal warn という警告を表示するか（off） *)
Control.polyEqWarn := false;

use "Utils.sml";
use "BReal.sml";
use "AST.sml";
use "Keywords.sml";
use "Priority.sml";
use "BuiltinFnc.sml";
use "Lexer.sml";
use "Parser.sml";
use "Primitive.sml";             (* 旧 BetaReduction.sml *)
use "IdentifierDuplication.sml"; (* 旧 AlphaConversion.sml *)
use "Stringify.sml";             (* 旧 PrintComponent.sml *)
use "TypeInference.sml";
use "Commutative.sml";
use "Match.sml";
use "RuleInput.sml";
use "Simplify.sml";
use "ImplicitCondition.sml";
use "OperationDivision.sml";
use "ExtractConditions.sml";
use "Sort.sml";
use "Rename.sml";


(* コマンドライン引数から, [入力ディレクトリ名, 出力ディレクトリ名, 書き換え規則ファイル名, 暗黙の条件の導出規則ファイル名] を受け取る *)
val [inputDirName, outputDirName, rewritingRuleFileName, implicitConditionRuleFileName] = CommandLine.arguments ();


(* ファイルから規則を抽出 *)
val rewritingRules          = RuleInput.strToRules (Utils.fileToString rewritingRuleFileName)
val implicitConditionRules  = RuleInput.strToRules (Utils.fileToString implicitConditionRuleFileName)


(* 1つのモデルファイルに対する細分化を行う関数 *)
(* string -> string -> string -> unit *)
fun modelslice inputFileName inputDir outputDir =
    let
      val _ = print (inputFileName ^ " : loading file\n")
      val fileNameLength = String.size inputFileName
      val indent = Utils.repeatString " " fileNameLength

      (* 入力モデルファイルの文字列 *)
      val inputString = Utils.fileToString (inputDir ^ "/" ^ inputFileName)

      val _ = print (inputFileName ^ " : constructing syntax tree\n")

      val beforeTime = Time.toMilliseconds (Time.now ())

      (* 字句解析 *)
      val modelTokens = Lexer.tokenize inputString


      (* 構文解析 *)
      val modelSyntaxTree = Parser.parse modelTokens


      (* 代入文のプリミティブ化・規則で表現できないプリミティブ化 *)
      val primitiveModel = Primitive.primitive modelSyntaxTree


      (* 局所変数の重複解消 *)
      val iddup = IdentifierDuplication.resolve primitiveModel


      (* 型推論 *)
      val typed = Utils.repeatApply TypeInference.typeComponent iddup


      (* 型情報の追記 *)
      val typePresented = TypeInference.presentTypeInfoInComponent typed


      (* 可換結合演算の被演算子の多重集合化 *)
      val ac = Utils.repeatApplyEqf (AST.mapExprsInComponent Commutative.flattenCommutative) AST.eqComponents (AST.mapExprsInComponent Commutative.makeCommutative typePresented)

      (* 暗黙の条件の導出 *)
      val _ = print (inputFileName ^ " : rewriting expressions and deriving implicit conditions by rules\n")
      fun applyDerivingImplicitConditions flag model =
          let
            fun printExecutionMessage phase = print (indent ^ " - " ^ phase ^ "\n")
            val simplifyFunctionsList =
                  [
                    AST.mapExprsInComponent Commutative.flattenCommutative,
                    AST.mapExprsInComponent Simplify.simplifyExprTree,
                    AST.mapExprsInComponent Simplify.deleteLiteralCondition,
                    Utils.repeatApply TypeInference.typeComponent,
                    AST.mapExprsInComponent Match.rewriteVarTypeSet
                  ]
            val rewriteFunctionsList =
                  [
                    (fn m =>
                      (printExecutionMessage "rewriting expressions by rules";
                       Utils.repeatApplyEqf (AST.mapExprsInComponent (Match.rewriteExpr rewritingRules)) AST.eqComponents m)),
                    (fn m =>
                      (printExecutionMessage "simplifying expressions and complement type information";
                       Utils.repeatApplyEqf (fn x => Utils.pam x simplifyFunctionsList) AST.eqComponents m))
                  ]
            val implicitConditionFunctionsList =
                  [
                    (fn m =>
                      (printExecutionMessage "simplifying expressions and complement type information";
                       Utils.repeatApplyEqf (fn x => Utils.pam x simplifyFunctionsList) AST.eqComponents m)),
                    Utils.repeatApplyEqf (fn x => Utils.pam x rewriteFunctionsList) AST.eqComponents,
                    (fn m =>
                      (printExecutionMessage "deriving implicit conditions by rules";
                       ImplicitCondition.deriveImplicitConditions flag implicitConditionRules m)),
                    (fn m =>
                      (printExecutionMessage "simplifying expressions and complement type information";
                    Utils.repeatApplyEqf (fn x => Utils.pam x simplifyFunctionsList) AST.eqComponents m)),
                    Utils.repeatApplyEqf (fn x => Utils.pam x rewriteFunctionsList) AST.eqComponents
                  ]
            val implicitConditionsDerivedByRules = Utils.repeatApplyEqf (fn x => Utils.pam x implicitConditionFunctionsList) AST.eqComponents model
            val _ = printExecutionMessage "deriving implicit conditions by equivalences"
          in
            Utils.repeatApplyEqf (fn x => Utils.pam x rewriteFunctionsList) AST.eqComponents (ImplicitCondition.rewriteEqualExprs flag implicitConditionsDerivedByRules)
          end

      val implicitConditionDerived = TypeInference.typeComponent (applyDerivingImplicitConditions false ac)

      (* 操作分割 *)
          (* (string * BComponent * (string list)) list *)
          (* [(細分化モデルのファイル名, 操作分割後の操作を一つしか持たないモデル, [自身より結合順が先になる細分化モデルのファイル名])] *)
      val _ = print (inputFileName ^ " : dividing operations\n")
      val oneOprModels = OperationDivision.divide implicitConditionDerived

      (* 制約条件等抽出 => 「関連要素抽出」に変更予定 *)
          (* (string * BComponent * (string list)) list *)
          (* [(細分化モデルのファイル名, 関連要素抽出後 (関連しない要素の削除後) のモデル, [自身より結合順が先になる細分化モデルのファイル名])] *)
      val _ = print (inputFileName ^ " : extracting relative elements\n")
      val extractedModels = List.map (fn (name, model, changedVars, deps) => (name, ExtractConditions.extract [] model [] changedVars, deps)) oneOprModels

      (* 代入文内の条件式も対象にした暗黙の条件の導出 *)
      val _ = print (inputFileName ^ " : rewriting expressions and deriving implicit conditions by rules (2)\n")
      val implicitConditionDerived2List = List.map (fn (n, m, d) => (n, applyDerivingImplicitConditions true m, d)) extractedModels

      (* 構文要素整列 *)
      val _ = print (inputFileName ^ " : sorting\n")
      val sortedModels = List.map (fn (name, model, deps) => (name, Sort.sort model, deps)) implicitConditionDerived2List

      (* 識別子置換 *)
          (* (string * (BComponent * ((string * string * BExpr) list))) list *)
          (* [(細分化モデルファイル名, 識別子置換後の細分化モデル, [自身より結合順が先になる細分化モデルのファイル名])] *)
      val _ = print (inputFileName ^ " : renaming\n")
      val renamedModels = List.map (fn (name, model, deps) => (name, Rename.rename model, deps)) sortedModels

      (* 細分化モデルの出力準備 *)
          (* (string * string) list *)
          (* [(細分化モデルの内容の文字列, 細分化モデルのファイル名)] *)
      val _ = print (inputFileName ^ " : outputting files\n")
      val outputs = List.map (fn (fileName, (m, h), d) => ((Stringify.componentToString m) ^ (Stringify.historyToString h) ^ (Stringify.modelDependenciesToString d), outputDir ^ "/" ^ fileName ^ ".mch")) renamedModels
      val afterTime = Time.toMilliseconds (Time.now ())

      val nofResult = List.length renamedModels
      val allTimeInMilliseconds = Int.fromLarge (afterTime - beforeTime)
      val allTimeInSeconds = (Real.fromInt allTimeInMilliseconds) / 1000.0

    in
      (* 細分化モデルの出力 *)
      List.app Utils.outputFile outputs ;
      print (
              inputFileName            ^ " : Model slicing is finished.\n" ^
              indent ^ "   " ^ (Int.toString nofResult) ^ " sliced model" ^ (if nofResult <= 1 then " is" else "s are") ^ " generated.\n" ^
              indent ^ "   It takes " ^ (Real.toString allTimeInSeconds) ^ "s except model file I/O.\n")
    end

(* 複数のモデルに対する細分化を行う関数 *)
(* string -> string -> unit *)
fun modelsliceAll ipDir opDir =
    let
      val ipDirStream = OS.FileSys.openDir ipDir
      fun modelsliceAllAux stream =
        (case OS.FileSys.readDir ipDirStream of
           NONE => ()
         | SOME inputFile => ((modelslice inputFile ipDir opDir); modelsliceAllAux stream))
    in
      modelsliceAllAux ipDirStream
    end

(* 実行 *)
val _ = modelsliceAll inputDirName outputDirName

(* 実行終了後対話環境を終了 *)
(* デバッグ用に変数の値を対話環境で表示させたい場合はこの行を消す (出力される前に終了してしまうため) *)
val _ = OS.Process.exit OS.Process.success
