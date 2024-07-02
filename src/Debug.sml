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
use "Show.sml";

val inputFileName = "PointSystemWithIf2.mch"
val inputDir = "../inputs"
val _ = print (inputFileName ^ " : loading file\n")
val fileNameLength = String.size inputFileName

(* 入力モデルファイルの文字列 *)
val inputString = Utils.fileToString (inputDir ^ "/" ^ inputFileName)

val _ = print (inputFileName ^ " : constructing syntax tree\n")

(* 字句解析 *)
val modelTokens = Lexer.tokenize inputString

(* 構文解析 *)
val modelSyntaxTree = Parser.parse modelTokens


fun pickLibraryNames (BMch (name, params, clauses)) =
  List.map (fn (BMchInst (token, exprs)) => token)
  (List.concat
    (List.map
      (fn (clause: BClause) =>
          case clause of
            BC_SEES ls => ls
            | BC_INCLUDES ls => ls
            | BC_PROMOTES ls => ls
            | BC_EXTENDS ls => ls
            | BC_USES ls => ls
            | BC_IMPORTS ls => ls
            | _ => []
      )
      clauses
    )
  )

val _ = print (Show.showTokenList (pickLibraryNames modelSyntaxTree))


val _ = OS.Process.exit OS.Process.success
