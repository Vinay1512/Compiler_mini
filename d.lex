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
realnum = (([0-9]+(\.[0-9]+)?)|(\.[0-9]+))([eE][+-]?[0-9]+)?{floatingsuffix}?;
id = {letter}({letter}|{digit}|_)*;
space = [\ \t];
quote = ["];
notQuote = [^"];
%%


<TYPEDECL>"void"	=> (Tokens.VOID(yypos, yypos + size yytext));
<TYPEDECL>"string"	=> (Tokens.STRING(yypos, yypos + size yytext));
<TYPEDECL>"short"	=> (Tokens.SHORT(yypos, yypos + size yytext));
<TYPEDECL>"long"	=> (Tokens.LONG(yypos, yypos + size yytext));
<TYPEDECL>"int"	    => (Tokens.INT(yypos, yypos + size yytext));
<TYPEDECL>"float"	=> (Tokens.FLOAT(yypos, yypos + size yytext));
<TYPEDECL>"double"	=> (Tokens.DOUBLE(yypos, yypos + size yytext));
<TYPEDECL>"char"	=> (Tokens.CHAR(yypos, yypos + size yytext));

<CC>"continue"    => (Tokens.CONTINUE(yypos, yypos + size yytext));
<CC>"break"    => (Tokens.BREAK(yypos, yypos + size yytext));
<CC>"return"    => (Tokens.RETURN(yypos, yypos + size yytext));
<CC>"while"    => (Tokens.WHILE(yypos, yypos + size yytext));
<CC>"do"    => (Tokens.DO(yypos, yypos + size yytext));
<CC>"for"    => (Tokens.FOR(yypos, yypos + size yytext));
<CC>"else"    => (Tokens.ELSE(yypos, yypos + size yytext));
<CC>"then"    => (Tokens.THEN(yypos, yypos + size yytext));
<CC>"if"    => (Tokens.IF(yypos, yypos + size yytext));



<BLOP>"&&"  => (Tokens.AND(yypos, yypos + size yytext));
<BLOP>"||"  => (Tokens.OR(yypos, yypos + size yytext));
<BLOP>"!="  => (Tokens.NEQ(yypos, yypos + size yytext));
<BLOP>"=="  => (Tokens.EQ(yypos, yypos + size yytext));
<BLOP>">"   => (Tokens.GT(yypos, yypos + size yytext));
<BLOP>"<"   => (Tokens.LT(yypos, yypos + size yytext));
<BLOP>">="  => (Tokens.GTE(yypos, yypos + size yytext));
<BLOP>"<="  => (Tokens.LTE(yypos, yypos + size yytext));
<BLOP>"="   => (Tokens.EQUALS(yypos, yypos + size yytext));


<BAOP>"*"   => (Tokens.TIMES(yypos, yypos + size yytext));
<BAOP>"-"   => (Tokens.MINUS(yypos, yypos + size yytext));
<BAOP>"/"   => (Tokens.DIVIDE(yypos, yypos + size yytext));
<BAOP>"+"   => (Tokens.PLUS(yypos, yypos + size yytext));
<BAOP>"%"   => (Tokens.PERCENT(yypos, yypos + size yytext));

<UOP>"--"   => (Tokens.DEC(yypos, yypos + size yytext));
<UOP>"++"   => (Tokens.INC(yypos, yypos + size yytext));
<UOP>"!"   => (Tokens.BANG(yypos, yypos + size yytext));

<SYM>","   => (Tokens.COMMA(yypos, yypos + size yytext));
<SYM>"}"   => (Tokens.RCURLY(yypos, yypos + size yytext));
<SYM>"{"   => (Tokens.LCURLY(yypos, yypos + size yytext));
<SYM>")"   => (Tokens.RPAREN(yypos, yypos + size yytext));
<SYM>"("   => (Tokens.LPAREN(yypos, yypos + size yytext));
<SYM>";"   => (Tokens.SEMICOLON(yypos, yypos + size yytext));
<SYM>":"   => (Tokens.COLON(yypos, yypos + size yytext));
<SYM>"?"   => (Tokens.QUESTION(yypos, yypos + size yytext));

{id}                       => (Tokens.ID(yytext, yypos, yypos + size yytext));
{quote}{notQuote}*{quote} => (Tokens.NNUM(yytext, yypos, yypos + size yytext));
{digit}+                   => (Tokens.DNUM(getInt (Int.fromString yytext), yypos, yypos + size yytext));

"/*"   => (YYBEGIN COMMENT; continue());
<COMMENT>"*/"   => (YYBEGIN INITIAL; continue());
<COMMENT>.      => (print ("skipping comment " ^ yytext ^ "\n"); continue());

{space}+        => (continue());
"\n"            => (lineNum := !lineNum+1; linePos := yypos :: !linePos; continue());
. => (ErrorMsg.error yypos ("illegal character '" ^ yytext ^ "'"); continue());


%s C S; 


id	= [_A-Za-z][_A-Za-z0-9]*; 
octdigit	= [0-7];
hexdigit	= [0-9a-fA-F];
integersuffix   = ([uU][lL]?[lL]?|[lL][lL]?[uU]?);
hexnum	= 0[xX]{hexdigit}+{integersuffix}?; 
octnum	= 0{octdigit}+{integersuffix}?;
decnum	= (0|([1-9][0-9]*)){integersuffix}?;
floatingsuffix  = [flFL];
realnum = (([0-9]+(\.[0-9]+)?)|(\.[0-9]+))([eE][+-]?[0-9]+)?{floatingsuffix}?;
ws	= ("\012"|[\t\ ])*;

simplecharconst  = '[^\n\\]';
escapecharconst  = '\\[^\n]';

directive = #(.)*\n;

%%

<INITIAL,C>^{ws}{directive}     => (SourceMap.parseDirective sourceMap 
                         (yypos,yytext); continue());
<INITIAL,C>\n		=> (SourceMap.newline sourceMap yypos; continue());
<INITIAL,C>{ws}		=> (continue()); 


<INITIAL>"/*"		=> (YYBEGIN C; continue());
<C>"*/"	 	=> (YYBEGIN INITIAL; continue());
<C>.		=> (continue());


<INITIAL>\"		=> (charlist := [""]; stringstart := yypos; YYBEGIN S; continue());
<S>\"	        => (YYBEGIN INITIAL;Tokens.STRING(makeString charlist,!stringstart,yypos+1));
<S>\n		=> ((#err errWarn) (!stringstart,yypos,"unclosed string");
		    SourceMap.newline sourceMap yypos;
		    YYBEGIN INITIAL; Tokens.STRING(makeString charlist,!stringstart,yypos));
<S>[^"\\\n]*	=> (addString(charlist,yytext); continue());
<S>\\\n	       	=> (SourceMap.newline sourceMap yypos; continue());
<S>\\0		 => (addString(charlist,chr 0);continue());
<S>\\{octdigit}{3} => (addString(charlist, chr(mkOctChar(substring(yytext, 1, size(yytext)-1), yypos, yypos+size(yytext), errWarn))); continue());
<S>\\x{hexdigit}+ => (addString(charlist, chr(mkHexChar(substring(yytext, 2, size(yytext)-2), yypos, yypos+size(yytext), errWarn))); continue());
<S>\\\^[@-_]	=> (addString(charlist,chr(ordof(yytext,2)-ord("@"))); continue());
<S>\\.     	=> (addString(charlist, chr(special_char(yytext, yypos, yypos+size(yytext), errWarn))); continue());

<INITIAL>":"		=> (Tokens.COLON(yypos,yypos+1));
<INITIAL>";"		=> (Tokens.SEMICOLON(yypos,yypos+1));
<INITIAL>"("		=> (Tokens.LPAREN(yypos,yypos+1));
<INITIAL>")"		=> (Tokens.RPAREN(yypos,yypos+1));
<INITIAL>"["		=> (Tokens.LBRACE(yypos,yypos+1));
<INITIAL>"]"		=> (Tokens.RBRACE(yypos,yypos+1));
<INITIAL>"{"		=> (Tokens.LCURLY(yypos,yypos+1));
<INITIAL>"}"		=> (Tokens.RCURLY(yypos,yypos+1));
<INITIAL>"."		=> (Tokens.DOT(yypos,yypos+1));
<INITIAL>"..."	        => (Tokens.ELIPSIS(yypos,yypos+3));
<INITIAL>","		=> (Tokens.COMMA(yypos,yypos+1));
<INITIAL>"*"		=> (Tokens.TIMES(yypos,yypos+1));
<INITIAL>"!"		=> (Tokens.BANG(yypos,yypos+1));
<INITIAL>"^"		=> (Tokens.HAT(yypos,yypos+1));
<INITIAL>"+"		=> (Tokens.PLUS(yypos,yypos+1));
<INITIAL>"-"		=> (Tokens.MINUS(yypos,yypos+1));
<INITIAL>"++"		=> (Tokens.INC(yypos,yypos+2));
<INITIAL>"--"		=> (Tokens.DEC(yypos,yypos+2));
<INITIAL>"->"		=> (Tokens.ARROW(yypos,yypos+1));
<INITIAL>"/"		=> (Tokens.DIVIDE(yypos,yypos+1));
<INITIAL>"~"	        => (Tokens.TILDE(yypos,yypos+1));
<INITIAL>"?"		=> (Tokens.QUESTION(yypos,yypos+1));
<INITIAL>"|"		=> (Tokens.BAR(yypos,yypos+1));
<INITIAL>"&"		=> (Tokens.AMP(yypos,yypos+1));
<INITIAL>"%"		=> (Tokens.PERCENT(yypos,yypos+1));
<INITIAL>"<="		=> (Tokens.LTE(yypos,yypos+2));
<INITIAL>">="		=> (Tokens.GTE(yypos,yypos+2));
<INITIAL>"=="		=> (Tokens.EQ(yypos,yypos+2));
<INITIAL>"="	        => (Tokens.EQUALS(yypos,yypos+1));
<INITIAL>"+="		=> (Tokens.PLUSEQUALS(yypos,yypos+2));
<INITIAL>"-="		=> (Tokens.MINUSEQUALS(yypos,yypos+2));
<INITIAL>"^="		=> (Tokens.XOREQUALS(yypos,yypos+2));
<INITIAL>"%="		=> (Tokens.MODEQUALS(yypos,yypos+2));
<INITIAL>"*="		=> (Tokens.TIMESEQUALS(yypos,yypos+2));
<INITIAL>"/="		=> (Tokens.DIVEQUALS(yypos,yypos+2));
<INITIAL>"|="		=> (Tokens.OREQUALS(yypos,yypos+2));
<INITIAL>"&="		=> (Tokens.ANDEQUALS(yypos,yypos+2));
<INITIAL>"<<="	        => (Tokens.LSHIFTEQUALS(yypos,yypos+3));
<INITIAL>">>="	        => (Tokens.RSHIFTEQUALS(yypos,yypos+3));
<INITIAL>"<"		=> (Tokens.LT(yypos,yypos+1));
<INITIAL>">"		=> (Tokens.GT(yypos,yypos+1));
<INITIAL>"!="		=> (Tokens.NEQ(yypos,yypos+2));
<INITIAL>"||"		=> (Tokens.OR(yypos,yypos+2));
<INITIAL>"&&"		=> (Tokens.AND(yypos,yypos+2));
<INITIAL>"<<"		=> (Tokens.LSHIFT(yypos,yypos+2));
<INITIAL>">>"		=> (Tokens.RSHIFT(yypos,yypos+2));

<INITIAL>{octnum}	=> (Tokens.DECNUM(mkOctInt(yytext,yypos,yypos+size(yytext),errWarn),yypos, yypos+size(yytext)));
<INITIAL>{hexnum}	=> (Tokens.DECNUM(mkHexInt(yytext,yypos,yypos+size(yytext),errWarn),yypos, yypos+size(yytext)));
<INITIAL>{decnum}	=> (Tokens.DECNUM(mkInt (yytext,yypos,yypos+size(yytext),errWarn), yypos,yypos+size(yytext)));
<INITIAL>{realnum}      =>
(Tokens.REALNUM(mkRealNum(yytext,yypos,yypos+size(yytext),errWarn), yypos, yypos
+ size(yytext)));

<INITIAL>"'\\"{octdigit}{1,3}"'"	=> (let val s = substring(yytext, 2, size(yytext)-3)
				     in Tokens.CCONST(IntInf.fromInt (mkOctChar(s,yypos,yypos+size(yytext),errWarn)),
						      yypos,
					      yypos+size(yytext))
	                             end);

<INITIAL>"'\\x"{hexdigit}+"'"	=>  (let val s = substring(yytext, 3, size(yytext)-4)
				     in Tokens.CCONST(IntInf.fromInt (mkHexChar(s,yypos,yypos+size(yytext),errWarn)),
						      yypos,
						      yypos+size(yytext))
	                             end);


<INITIAL>{simplecharconst}	=> (let val cval = ordof(yytext,1)
	                            in Tokens.CCONST(Int.toLarge cval,yypos,yypos+size(yytext))
                                    end);
<INITIAL>{escapecharconst} => (Tokens.CCONST(IntInf.fromInt(special_char(substring(yytext,1,size(yytext)-2),yypos,yypos+size(yytext),errWarn)), yypos, yypos+size(yytext)));
<INITIAL>{id}        	=> (TokTable.checkToken(yytext,yypos));
<INITIAL>.        	=> (continue());

