(* The compiler from expression to rp *)

(* This three structure definitions are what the lexer and parser *)

structure ExprLrVals = CCompLrValsFun(structure Token = LrParser.Token) (* Generate the LR values structure *)
structure ExprLex    = CCompLexFun(structure Tokens = ExprLrVals.Tokens)
structure ExprParser = Join( structure ParserData = ExprLrVals.ParserData
			     structure Lex        = ExprLex
			     structure LrParser   = LrParser
			   )

(* Build Lexers *)

