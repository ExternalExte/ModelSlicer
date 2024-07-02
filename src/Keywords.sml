signature KEYWORDS =
sig
  val clauseKeywords : (string * int) list
  val keywords : string list
  val alphaKeywords : string list
  val isSymbol : char -> bool
end

structure Keywords :> KEYWORDS =
struct
  val clauseKeywords = [ (* 2個目の要素は節のソート用の数 *)
      ("CONSTRAINTS",        10),
      ("SEES",               20),
      ("INCLUDES",           30),
      ("PROMOTES",           40),
      ("EXTENDS",            50),
      ("USES",               60),
      ("IMPORTS",            65),
      ("SETS",               70),
      ("VALUES",             75),
      ("CONCRETE_CONSTANTS", 80),
      ("ABSTRACT_CONSTANTS", 90),
      ("CONSTANTS",          80),
      ("PROPERTIES",        100),
      ("CONCRETE_VARIABLES",110),
      ("ABSTRACT_VARIABLES",120),
      ("VARIABLES",         120),
      ("INVARIANT",         130),
      ("ASSERTIONS",        140),
      ("INITIALISATION",    150),
      ("OPERATIONS",        160),
      ("DEFINITIONS",      1000)
    ]

  (* アルファベットや数字を除いた記号 (アンダーバーを含む) *)

  val symbolChars = [#"!", #"\"", #"#", #".", #"$", #"%", #"&", #"'", #"(", #")", #"*", #"+", #",", #"-", #".", #"/", #":", #";", #"<", #"=", #">", #"_", #"?", #"@", #"[", #"\\", #"]", #"^", #"`", #"{", #"|", #"}", #"~" ]

  (* 記号を用いた予約語 *)
  val keywords = [
      (* 4文字 *)
      "+->>",
      "-->>",
      "/<<:",
      ">->>",
      (* 3文字 *)
      "/|\\",
      "\\|/",
      "+->",
      "-->",
      "/<:",
      "<->",
      "<--",
      "<<:",
      "<<|",
      "<=>",
      ">+>",
      ">->",
      "|->",
      "|>>",
      (* 2文字 *)
      "/\\",
      "\\/",
      "$0",
      "**",
      "->",
      "..",
      "/:",
      "/=",
      "::",
      ":=",
      "<+",
      "<-",
      "<:",
      "<=",
      "<|",
      "==",
      "=>",
      "><",
      ">=",
      "[]",
      "{}",
      "|>",
      "||",
      (* 1文字 *)
      "!",
      "#",
      "%",
      "&",
      "'",
      "!",
      "(",
      ")",
      "*",
      "+",
      ",",
      "-",
      ".",
      "/",
      ":",
      ";",
      "=",
      "<",
      ">",
      "[",
      "]",
      "^",
      "{",
      "|",
      "}",
      "~"
    ]
  (* alphaKeywordsRは辞書順、alphaKeywordsはその逆 *)
  val alphaKeywordsR = [
      "ABSTRACT_CONSTANTS",
      "ABSTRACT_VARIABLES",
      "ANY",
      "ASSERT",
      "ASSERTIONS",
      "BE",
      "BEGIN",
      "BOOL",
      "CASE",
      "CHOICE",
      "CONCRETE_CONSTANTS",
      "CONCRETE_VARIABLES",
      "CONSTANTS",
      "CONSTRAINTS",
      "DEFINITIONS",
      "DO",
      "EITHER",
      "ELSE",
      "ELSIF",
      "END",
      "EXTENDS",
      "FALSE",
      "FIN",      (* e *)
      "FIN1",     (* e *)
      "IF",
      "IMPLEMENTATION",
      "IMPORTS",
      "IN",
      "INCLUDES",
      "INITIALISATION",
      "INT",
      "INTEGER",
      "INTER", (* . *)
      "INVARIANT",
      "LET",
      "LOCAL_OPERATIONS",
      "MACHINE",
      "MAXINT",
      "MININT",
      "NAT",
      "NAT1",
      "NATURAL",
      "NATURAL1",
      "OF",
      "OPERATIONS",
      "OR",
      "PI",       (* . *)
      "POW",      (* e *)
      "POW1",     (* e *)
      "PRE",
      "PROMOTES",
      "PROPERTIES",
      "REAL",
      "REFINES",
      "REFINEMENT",
      "SEES",
      "SELECT",
      "SETS",
      "SIGMA",    (* . *)
      "STRING",
      "THEN",
      "TRUE",
      "UNION",    (* . *)
      "USES",
      "VALUES",
      "VAR",
      "VARIANT",
      "VARIABLES",
      "WHEN",
      "WHERE",
      "WHILE",
      "arity",    (* , *)
      "bfalse",
      "bin",
      "bool",     (* e *)
      "btree",    (* e *)
      "btrue",
      "card",     (* e *)
      "ceiling",  (* e *)
      "closure",
      "closure1",
      "conc",     (* e *)
      "const",
      "dom",      (* e *)
      "father",   (* , *)
      "first",    (* e *)
      "floor",    (* e *)
      "fnc",      (* e *)
      "front",    (* e *)
      "id",       (* e *)
      "infix",    (* e *)
      "inter",    (* e *)
      "iseq",     (* e *)
      "iseq1",    (* e *)
      "iterate",
      "last",     (* e *)
      "left",     (* e *)
      "max",      (* e *)
      "min",      (* e *)
      "mirror",   (* e *)
      "mod",
      "not",
      "or",
      "perm",     (* e *)
      "postfix",  (* e *)
      "pred",     (* e *)
      "prefix",   (* e *)
      "prj1",
      "prj2",
      "ran",      (* e *)
      "rank",     (* , *)
      "real",     (* e *)
      "rec",
      "rel",      (* e *)
      "rev",      (* e *)
      "right",    (* e *)
      "seq",      (* e *)
      "seq1",     (* e *)
      "size",     (* e *)
      "sizet",    (* e *)
      "skip",
      "son",      (* , *)
      "sons",     (* e *)
      "struct",
      "subtree",  (* , *)
      "succ",     (* e *)
      "tail",     (* e *)
      "top",      (* e *)
      "tree",     (* e *)
      "union"     (* e *)
    ]
  val alphaKeywords = rev alphaKeywordsR
  fun isSymbol x = List.exists (Utils.eqto x) symbolChars
end
