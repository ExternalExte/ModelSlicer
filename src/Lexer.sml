signature LEXER =
sig
  exception LexerError of string
  val tokenize : string -> BToken list
end

structure Lexer :> LEXER =
struct
  exception LexerError of string

  (* 文字列を受け取り、先頭から何文字が識別子名として切り出せるかを返す関数 *)
  (* getVarNのcodeの1文字目がアルファベットであることは呼び出し元で確認すること *)
  fun getVarN code =
      if
        code = ""
      then
        0
      else
        let
          val c1 = String.sub (code, 0) (* cはcodeの先頭の文字 *)
        in
          (* ひとまずrenaming prefixは変数名の一部として扱う *)
          if
            c1 = #"." (* 先頭文字が.の場合 *)
          then
            let
              val c2 = String.sub (code, 1)
            in
              if
                c2 = #"." orelse c2 = #"("
              then
                0
              else
                1 + getVarN (String.extract (code, 1, NONE))
            end
          else if
            Char.isSpace c1 orelse (Keywords.isSymbol c1 andalso c1 <> #"_") (* 先頭文字がスペース類もしくはアンダーバー以外の記号 (識別子の区切り文字) の場合  *)
          then
            0
          else
            1 + getVarN (String.extract (code, 1, NONE)) (* 先頭文字が識別子の一部である場合 *)
        end

  fun getVar code =
      let
        val varN       = getVarN code
        val allIdStr   = String.extract (code, 0,    SOME varN)
        val rest       = String.extract (code, varN, NONE)
        (*
        val allVarList = List.map String.implode (Utils.chopList (Utils.eqto #".") (String.explode allIdStr))
        *)
      in(*
        case allVarList of
          [str]        => ((NONE, str), rest)
        | [str1, str2] => ((SOME str1, str2), rest)
        | _            => raise LexerError "invalid identifier of renaming"*)
        (Var allIdStr, rest)
      end


  (* 文字列を受け取り、先頭から何文字 (何桁) 整数として切り出せるかを返す関数 *)
  fun getDigitsN code =
      if
        code = ""
      then
        0
      else
        let
          val c = String.sub (code, 0)
        in
          if
            Char.isDigit c
          then
            1 + getDigitsN (String.extract (code, 1, NONE))
          else
            0
        end


  (* 文字列リテラルの内容の始端からの文字列を受け取り、文字列リテラルの内容の終端まで何文字かを返す関数 *)
  fun getStrN code =
      if
        code = ""
      then
        raise LexerError "Unclosed STRING literal"
      else
        let
          val c = String.sub (code, 0)
        in
          case c of
            #"\"" => 0
          | #"\\" => if
                       String.size code = 1
                     then
                       raise LexerError "Unclosed STRING literal"
                     else
                       (case String.sub (code, 1) of
                          #"\"" => 2 + getStrN (String.extract (code, 2, NONE))
                        | _ => 1 + getStrN (String.extract (code, 1, NONE))
                       )
          | _ => 1 + getStrN (String.extract (code, 1, NONE))
        end


  (* 行コメント//の内容の始端からの文字列を受け取り、の終端までの文字数 (改行までの文字数) を返す関数 *)
  fun getCommentLineN code =
      if
        code = ""
      then
        0
      else
        let
          val c = String.sub (code, 0)
        in
          if
            c = #"\n"
          then
            1
          else
	          1 + getCommentLineN (String.extract (code, 1, NONE))
        end


(* /**/形式のコメントの内容の始端からの文字列を受け取り、終端までの文字数を返す関数*)
  fun getCommentN code =
      if
        String.size code < 2
      then
        raise LexerError "unclosed comment"
      else if
        String.isPrefix "*/" code
      then
        2
      else
	      1 + getCommentN (String.extract (code, 1, NONE))


  (* トークナイズ関数 *)
  (* val tokenize : string -> [BToken] *)
  (* ドットを使ったrenameされた識別子にもリストで対応しているが、モデル展開後のモデルにその記法が表れることはない *)
  fun tokenize code =
      if
        code = ""
      then
        []
      else
        let
          val c = String.sub (code, 0)
        in
          if
            Char.isSpace c
          then
            tokenize (String.extract (code, 1, NONE)) (* 空白読み飛ばし *)
	        else if
            c = #"/"
          then
            let
	            val c2 = String.sub (code, 1)
	          in
              if
                c2 = #"/"
              then
                let
                  val strN = getCommentLineN (String.extract (code, 2, NONE))
	              in
                  tokenize (String.extract (code, 2 + strN, NONE))
  	            end
	            else if
                c2 = #"*"
              then
	              let
                  val strN = getCommentN (String.extract (code, 2, NONE))
	              in
                  tokenize (String.extract (code, 2 + strN, NONE))
  	            end
	            else
                let
                  val klist = List.find (fn x => String.isPrefix x code) Keywords.keywords
	              in
                  if
                    klist <> NONE
                  then
                    let
                      val newSymbolBTokenString = valOf klist
                    in
                      (Keyword newSymbolBTokenString) :: tokenize (String.extract (code, String.size newSymbolBTokenString, NONE))
                    end
                  else
                    raise LexerError "unknown character"
	              end
            end
          else if
            c = #"\""
          then
            let
              val strN = getStrN (String.extract (code, 1, NONE))
            in
              StringLiteral (String.extract (code, 1, SOME strN)) :: tokenize (String.extract (code, 2 + strN, NONE))
            end
          else
            let
              val klist = List.find (fn x => String.isPrefix x code) Keywords.keywords
              val alist = List.find (fn x => String.isPrefix x code) Keywords.alphaKeywords
            in
              if
                klist <> NONE
              then
                let
                  val newSymbolBTokenString = valOf klist
                in
                  (Keyword newSymbolBTokenString) :: tokenize (String.extract (code, String.size newSymbolBTokenString, NONE))
                end
              else if
                alist <> NONE
              then
                let
                  val newAlphaBTokenString = valOf alist
                  val rest = String.extract (code, String.size newAlphaBTokenString, NONE)
                in
                  if
                    rest = "" orelse Char.isSpace (String.sub (rest, 0)) orelse (Keywords.isSymbol (String.sub (rest, 0)) (* コード終端または次がスペースまたは次が記号 *)
                    andalso (String.sub (rest, 0)) <> #"_") (* 次がアンダーバーでない *)
                  then
                    Keyword newAlphaBTokenString :: tokenize rest (* アルファベット予約語 *)
                  else if
                    Char.isAlpha (String.sub (rest, 0)) orelse String.sub (rest, 0) = #"_" orelse Char.isDigit (String.sub   (rest, 0)) (* 次がアルファベットか数字かアンダーバー *)
                  then
                    let
                      val (v, r) = getVar code
                    in
                      v :: tokenize r
                    end
                  else
                    raise LexerError "invalid character"
                end
              else if
                Char.isDigit c
              then
                let
                  val digitN = getDigitsN code
                  val rest = String.extract (code, digitN, NONE)
                in
                  if
                    rest = "" orelse String.sub (rest, 0) <> #"."
                  then
                    IntegerLiteral (valOf (IntInf.fromString (String.extract (code, 0, SOME digitN)))) :: tokenize rest
                  else if
                    rest <> "." andalso Char.isDigit (String.sub (rest, 1)) (* restは非空文字列 & restの先頭は"." & rest = "."でない & "."の次は数字 *)
                  then
                    let
                      val underpointRest = String.extract (rest, 1, NONE)
                      val fractionalDigitN = getDigitsN underpointRest
                      val realRest = String.extract (underpointRest, fractionalDigitN, NONE)
                    in
                      RealLiteral (BReal.fromString (String.extract (code, 0, SOME (digitN + 1 + fractionalDigitN)))) :: tokenize realRest
                    end
                  else
                    IntegerLiteral (valOf (IntInf.fromString (String.extract (code, 0, SOME digitN)))) :: tokenize rest (* 次が区間の".."の場合 *)
                end
              else if
                Char.isAlpha c
              then
                let
                  val (v, r) = getVar code
                in
                  v :: tokenize r
                end
              else
                raise LexerError "invalid character"
            end
        end
end
