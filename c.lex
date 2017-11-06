type pos = int

type svalue        = Tokens.svalue
type ('a,'b) token = ('a,'b) Tokens.token
type lexresult     = (svalue,pos) token

val lineNum = ErrorMsg.lineNum
val linePos = ErrorMsg.linePos
fun err(pos1,pos2) = ErrorMsg.error pos1

fun eof() = let val pos = hd(!linePos) in Tokens.EOF(pos,pos) end

exception NotAnInt

fun getInt(optionInt : int option) = case optionInt of
  SOME(n) => n
  | _ => raise NotAnInt 


(*CC - Conditional Construct*)
%%
%header (functor CCompLexFun(structure Tokens : CComp_TOKENS ));

%s COMMENT;
letter = [a-zA-Z];
digit = [0-9];
realnum = ([0-9]+(\.[0-9]+)?);
id = {letter}({letter}|{digit}|_)*;
space = [\ \t];
quote = ["];
notQuote = [^"];
%%


<INITIAL>"void"	=> (Tokens.VOID(yypos, yypos + size yytext));
<INITIAL>"string"	=> (Tokens.STRING(yypos, yypos + size yytext));
<INITIAL>"short"	=> (Tokens.SHORT(yypos, yypos + size yytext));
<INITIAL>"long"	=> (Tokens.LONG(yypos, yypos + size yytext));
<INITIAL>"int"	    => (Tokens.INT(yypos, yypos + size yytext));
<INITIAL>"float"	=> (Tokens.FLOAT(yypos, yypos + size yytext));
<INITIAL>"double"	=> (Tokens.DOUBLE(yypos, yypos + size yytext));
<INITIAL>"char"	=> (Tokens.CHAR(yypos, yypos + size yytext));

<INITIAL>"continue"    => (Tokens.CONTINUE(yypos, yypos + size yytext));
<INITIAL>"break"    => (Tokens.BREAK(yypos, yypos + size yytext));
<INITIAL>"return"    => (Tokens.RETURN(yypos, yypos + size yytext));
<INITIAL>"while"    => (Tokens.WHILE(yypos, yypos + size yytext));
<INITIAL>"do"    => (Tokens.DO(yypos, yypos + size yytext));
<INITIAL>"for"    => (Tokens.FOR(yypos, yypos + size yytext));
<INITIAL>"else"    => (Tokens.ELSE(yypos, yypos + size yytext));
<INITIAL>"then"    => (Tokens.THEN(yypos, yypos + size yytext));
<INITIAL>"if"    => (Tokens.IF(yypos, yypos + size yytext));



<INITIAL>"&&"  => (Tokens.AND(yypos, yypos + size yytext));
<INITIAL>"||"  => (Tokens.OR(yypos, yypos + size yytext));
<INITIAL>"!="  => (Tokens.NEQ(yypos, yypos + size yytext));
<INITIAL>"=="  => (Tokens.EQ(yypos, yypos + size yytext));
<INITIAL>">"   => (Tokens.GT(yypos, yypos + size yytext));
<INITIAL>"<"   => (Tokens.LT(yypos, yypos + size yytext));
<INITIAL>">="  => (Tokens.GTE(yypos, yypos + size yytext));
<INITIAL>"<="  => (Tokens.LTE(yypos, yypos + size yytext));
<INITIAL>"="   => (Tokens.EQUALS(yypos, yypos + size yytext));


<INITIAL>"*"   => (Tokens.TIMES(yypos, yypos + size yytext));
<INITIAL>"-"   => (Tokens.MINUS(yypos, yypos + size yytext));
<INITIAL>"/"   => (Tokens.DIVIDE(yypos, yypos + size yytext));
<INITIAL>"+"   => (Tokens.PLUS(yypos, yypos + size yytext));
<INITIAL>"%"   => (Tokens.PERCENT(yypos, yypos + size yytext));

<INITIAL>"--"   => (Tokens.DEC(yypos, yypos + size yytext));
<INITIAL>"++"   => (Tokens.INC(yypos, yypos + size yytext));
<INITIAL>"!"   => (Tokens.BANG(yypos, yypos + size yytext));

<INITIAL>","   => (Tokens.COMMA(yypos, yypos + size yytext));
<INITIAL>"}"   => (Tokens.RCURLY(yypos, yypos + size yytext));
<INITIAL>"{"   => (Tokens.LCURLY(yypos, yypos + size yytext));
<INITIAL>")"   => (Tokens.RPAREN(yypos, yypos + size yytext));
<INITIAL>"("   => (Tokens.LPAREN(yypos, yypos + size yytext));
<INITIAL>";"   => (Tokens.SEMICOLON(yypos, yypos + size yytext));
<INITIAL>":"   => (Tokens.COLON(yypos, yypos + size yytext));
<INITIAL>"?"   => (Tokens.QUESTION(yypos, yypos + size yytext));

<INITIAL>{id}  => (Tokens.ID(yytext, yypos, yypos + size yytext));
<INITIAL>{quote}{notQuote}*{quote} => (Tokens.NNUM(String.extract(yytext,1,SOME ((size yytext) - 2)), yypos, yypos + size yytext));
{digit}+       => (Tokens.DNUM(getInt (Int.fromString yytext), yypos, yypos + size yytext));
{realnum}      => (Tokens.RNUM(Option.getOpt(Real.fromString(yytext),0.0), yypos, yypos + size yytext));

"/*"   => (YYBEGIN COMMENT; continue());
<COMMENT>"*/"   => (YYBEGIN INITIAL; continue());
<COMMENT>.      => (print ("skipping comment " ^ yytext ^ "\n"); continue());




{space}+        => (continue());
"\n"            => (lineNum := !lineNum+1; linePos := yypos :: !linePos; continue());
. => (ErrorMsg.error yypos ("illegal character '" ^ yytext ^ "'"); continue());
