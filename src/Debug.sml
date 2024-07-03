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
use "Primitive.sml";             (* 旧 BetaReduction.sml *)
use "IdentifierDuplication.sml"; (* 旧 AlphaConversion.sml *)
use "Stringify.sml";             (* 旧 PrintComponent.sml *)
use "TypeInference.sml";


val modelSyntaxTree = Parser.parse (Lexer.tokenize (Utils.fileToString ("../inputs/Student.mch")))

(* val st2 = Parser.parse (Lexer.tokenize (Utils.fileToString ("../inputs/PointSystem.mch"))) *)

val primitiveModel = Primitive.primitive modelSyntaxTree


(* 局所変数の重複解消 *)
val iddup = IdentifierDuplication.resolve primitiveModel


(* 型推論 *)
val typed = Utils.repeatApply TypeInference.typeComponent iddup


(* 型情報の追記 *)
val typePresented = TypeInference.presentTypeInfoInComponent typed

val _ = print (Show.showComponent typePresented)

(* val _ = print (Show.showComponent st1) *)

(* val _ = print (Show.showComponent st2) *)

(* val merged = Merge.mergeComponent st1 st2 *)

(* val _ = print (Show.showComponent merged) *)

val _ = OS.Process.exit OS.Process.success
