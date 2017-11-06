type pos = int
type lexresult = Tokens.token

val lineNum = ErrorMsg.lineNum
val linePos = ErrorMsg.linePos
fun err(pos1,pos2) = ErrorMsg.error pos1

fun eof() = let val pos = hd(!linePos) in Tokens.EOF(pos,pos) end

exception NotAnInt

fun getInt(optionInt : int option) = case optionInt of
  SOME(n) => n
  | _ => raise NotAnInt 

%%
%s COMMENT ;
letter = [a-zA-Z];
digit = [0-9];
id = {letter}({letter}|{digit}|_)*;
space = [\ \t];
quote = ["];
notQuote = [^"];
%%

<INITIAL>"float"	=> (Tokens.FLOAT(yypos, yypos + size yytext));
<INITIAL>"char"		=> (Tokens.CHAR(yypos, yypos + size yytext));
<INITIAL>"void"		=> (Tokens.VOID(yypos, yypos + size yytext));
<INITIAL>"break"    => (Tokens.BREAK(yypos, yypos + size yytext));
<INITIAL>"for"      => (Tokens.FOR(yypos, yypos + size yytext));
<INITIAL>"do"       => (Tokens.DO(yypos, yypos + size yytext));
<INITIAL>"while"    => (Tokens.WHILE(yypos, yypos + size yytext));
<INITIAL>"switch" 	=> (Tokens.SWITCH(yypos, yypos + size yytext));
<INITIAL>"if"       => (Tokens.IF(yypos, yypos + size yytext));
<INITIAL>"else"     => (Tokens.ELSE(yypos, yypos + size yytext));

<INITIAL>"printf"	=> (Tokens.PRINT(yypos, yypos + size yytext));
<INITIAL>"scanf" 	=> (Tokens.SCAN(yypos, yypos + size yytext));



<INITIAL>"||"  => (Tokens.OR(yypos, yypos + size yytext));
<INITIAL>"&&"  => (Tokens.AND(yypos, yypos + size yytext));
<INITIAL>">=" => (Tokens.GE(yypos, yypos + size yytext));
<INITIAL>">"  => (Tokens.GT(yypos, yypos + size yytext));
<INITIAL>"<=" => (Tokens.LE(yypos, yypos + size yytext));
<INITIAL>"<"  => (Tokens.LT(yypos, yypos + size yytext));
<INITIAL>"!=" => (Tokens.NEQ(yypos, yypos + size yytext));
<INITIAL>"=="  => (Tokens.EQ(yypos, yypos + size yytext));
<INITIAL>"/"  => (Tokens.DIVIDE(yypos, yypos + size yytext));
<INITIAL>"*"  => (Tokens.TIMES(yypos, yypos + size yytext));
<INITIAL>"-"  => (Tokens.MINUS(yypos, yypos + size yytext));
<INITIAL>"+"  => (Tokens.PLUS(yypos, yypos + size yytext));
<INITIAL>"{" => (Tokens.LBRACE(yypos, yypos + size yytext));
<INITIAL>"}" => (Tokens.RBRACE(yypos, yypos + size yytext));
<INITIAL>"(" => (Tokens.LPAREN(yypos, yypos + size yytext));
<INITIAL>")" => (Tokens.RPAREN(yypos, yypos + size yytext));
<INITIAL>"[" => (Tokens.LBRACK(yypos, yypos + size yytext));
<INITIAL>"]" => (Tokens.RBRACK(yypos, yypos + size yytext));
<INITIAL>"." => (Tokens.DOT(yypos, yypos + size yytext));
<INITIAL>"," => (Tokens.COMMA(yypos, yypos + size yytext));
<INITIAL>";" => (Tokens.SEMICOLON(yypos, yypos + size yytext));
<INITIAL>":" => (Tokens.COLON(yypos, yypos + size yytext));

<INITIAL>{id}                       => (Tokens.ID(yytext, yypos, yypos + size yytext));
<INITIAL>{quote}{notQuote}*{quote} => (Tokens.STRING(String.extract(yytext,1,SOME ((size yytext) - 2)), yypos, yypos + size yytext));
<INITIAL>{digit}+                   => (Tokens.INT(getInt (Int.fromString yytext), yypos, yypos + size yytext));

<INITIAL>"/*"   => (YYBEGIN COMMENT; continue());
<COMMENT>"*/"   => (YYBEGIN INITIAL; continue());
<COMMENT>.      => (print ("skipping comment " ^ yytext ^ "\n"); continue());

{space}+        => (continue());
"\n"            => (lineNum := !lineNum+1; linePos := yypos :: !linePos; continue());
. => (ErrorMsg.error yypos ("illegal character '" ^ yytext ^ "'"); continue());
