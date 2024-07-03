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
use "Merge.sml";


val st1 = Parser.parse (Lexer.tokenize (Utils.fileToString ("../inputs/LibrarySystem.mch")))

val st2 = Parser.parse (Lexer.tokenize (Utils.fileToString ("../inputs/PointSystem.mch")))

(* val _ = print (Show.showComponent st1) *)

(* val _ = print (Show.showComponent st2) *)

val merged = Merge.mergeComponent st1 st2

val _ = print (Show.showComponent merged)

val _ = OS.Process.exit OS.Process.success
