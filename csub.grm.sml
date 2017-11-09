functor CCompLrValsFun(structure Token : TOKEN)
 : sig structure ParserData : PARSER_DATA
       structure Tokens : CComp_TOKENS
   end
 = 
struct
structure ParserData=
struct
structure Header = 
struct
structure AST = Abstract;

fun createx x = AST.EXPR(x);

fun createstruc (NONE,y) = {name=y,ctype=AST.Undetermined}
  | createstruc (SOME x,y) = {name=y,ctype=x};
fun createfor x = AST.STMT(AST.For(x))

fun createwhile x= AST.STMT(AST.While(x))

end
structure LrTable = Token.LrTable
structure Token = Token
local open LrTable in 
val table=let val actionRows =
"\
\\001\000\001\000\000\000\000\000\
\\001\000\002\000\119\000\004\000\075\000\008\000\074\000\009\000\073\000\
\\010\000\072\000\011\000\071\000\012\000\070\000\014\000\069\000\
\\015\000\068\000\016\000\067\000\018\000\066\000\019\000\065\000\
\\020\000\064\000\021\000\063\000\022\000\062\000\023\000\061\000\
\\024\000\060\000\025\000\059\000\026\000\058\000\000\000\
\\001\000\003\000\022\000\006\000\021\000\000\000\
\\001\000\003\000\027\000\004\000\026\000\018\000\025\000\000\000\
\\001\000\003\000\031\000\018\000\030\000\000\000\
\\001\000\003\000\055\000\004\000\041\000\006\000\021\000\007\000\054\000\
\\012\000\040\000\013\000\039\000\015\000\038\000\016\000\037\000\
\\017\000\036\000\027\000\035\000\028\000\034\000\029\000\033\000\
\\030\000\053\000\033\000\052\000\035\000\051\000\036\000\050\000\
\\037\000\049\000\038\000\048\000\000\000\
\\001\000\003\000\055\000\004\000\041\000\006\000\021\000\007\000\093\000\
\\012\000\040\000\013\000\039\000\015\000\038\000\016\000\037\000\
\\017\000\036\000\027\000\035\000\028\000\034\000\029\000\033\000\
\\030\000\053\000\033\000\052\000\035\000\051\000\036\000\050\000\
\\037\000\049\000\038\000\048\000\000\000\
\\001\000\003\000\055\000\004\000\041\000\006\000\021\000\012\000\040\000\
\\013\000\039\000\015\000\038\000\016\000\037\000\017\000\036\000\
\\027\000\035\000\028\000\034\000\029\000\033\000\030\000\053\000\
\\033\000\052\000\035\000\051\000\036\000\050\000\037\000\049\000\
\\038\000\048\000\000\000\
\\001\000\003\000\076\000\004\000\075\000\008\000\074\000\009\000\073\000\
\\010\000\072\000\011\000\071\000\012\000\070\000\014\000\069\000\
\\015\000\068\000\016\000\067\000\018\000\066\000\019\000\065\000\
\\020\000\064\000\021\000\063\000\022\000\062\000\023\000\061\000\
\\024\000\060\000\025\000\059\000\026\000\058\000\000\000\
\\001\000\003\000\085\000\004\000\075\000\008\000\074\000\009\000\073\000\
\\010\000\072\000\011\000\071\000\012\000\070\000\014\000\069\000\
\\015\000\068\000\016\000\067\000\018\000\066\000\019\000\065\000\
\\020\000\064\000\021\000\063\000\022\000\062\000\023\000\061\000\
\\024\000\060\000\025\000\059\000\026\000\058\000\000\000\
\\001\000\003\000\086\000\000\000\
\\001\000\003\000\087\000\000\000\
\\001\000\003\000\094\000\004\000\075\000\008\000\074\000\009\000\073\000\
\\010\000\072\000\011\000\071\000\012\000\070\000\014\000\069\000\
\\015\000\068\000\016\000\067\000\018\000\066\000\019\000\065\000\
\\020\000\064\000\021\000\063\000\022\000\062\000\023\000\061\000\
\\024\000\060\000\025\000\059\000\026\000\058\000\000\000\
\\001\000\003\000\115\000\000\000\
\\001\000\003\000\124\000\000\000\
\\001\000\003\000\131\000\000\000\
\\001\000\004\000\041\000\005\000\112\000\012\000\040\000\013\000\039\000\
\\015\000\038\000\016\000\037\000\017\000\036\000\027\000\035\000\
\\028\000\034\000\029\000\033\000\000\000\
\\001\000\004\000\041\000\012\000\040\000\013\000\039\000\015\000\038\000\
\\016\000\037\000\017\000\036\000\027\000\035\000\028\000\034\000\
\\029\000\033\000\000\000\
\\001\000\004\000\075\000\005\000\113\000\008\000\074\000\009\000\073\000\
\\010\000\072\000\011\000\071\000\012\000\070\000\014\000\069\000\
\\015\000\068\000\016\000\067\000\018\000\066\000\019\000\065\000\
\\020\000\064\000\021\000\063\000\022\000\062\000\023\000\061\000\
\\024\000\060\000\025\000\059\000\026\000\058\000\000\000\
\\001\000\004\000\075\000\005\000\123\000\008\000\074\000\009\000\073\000\
\\010\000\072\000\011\000\071\000\012\000\070\000\014\000\069\000\
\\015\000\068\000\016\000\067\000\018\000\066\000\019\000\065\000\
\\020\000\064\000\021\000\063\000\022\000\062\000\023\000\061\000\
\\024\000\060\000\025\000\059\000\026\000\058\000\000\000\
\\001\000\004\000\075\000\005\000\125\000\008\000\074\000\009\000\073\000\
\\010\000\072\000\011\000\071\000\012\000\070\000\014\000\069\000\
\\015\000\068\000\016\000\067\000\018\000\066\000\019\000\065\000\
\\020\000\064\000\021\000\063\000\022\000\062\000\023\000\061\000\
\\024\000\060\000\025\000\059\000\026\000\058\000\000\000\
\\001\000\004\000\090\000\000\000\
\\001\000\004\000\091\000\000\000\
\\001\000\004\000\092\000\000\000\
\\001\000\005\000\044\000\039\000\018\000\040\000\017\000\041\000\016\000\
\\042\000\015\000\043\000\014\000\044\000\013\000\045\000\012\000\000\000\
\\001\000\005\000\083\000\047\000\082\000\000\000\
\\001\000\005\000\121\000\047\000\120\000\000\000\
\\001\000\005\000\135\000\000\000\
\\001\000\017\000\019\000\000\000\
\\001\000\017\000\024\000\000\000\
\\001\000\017\000\084\000\000\000\
\\001\000\017\000\122\000\000\000\
\\001\000\039\000\018\000\040\000\017\000\041\000\016\000\042\000\015\000\
\\043\000\014\000\044\000\013\000\045\000\012\000\000\000\
\\138\000\039\000\018\000\040\000\017\000\041\000\016\000\042\000\015\000\
\\043\000\014\000\044\000\013\000\045\000\012\000\046\000\011\000\000\000\
\\139\000\039\000\018\000\040\000\017\000\041\000\016\000\042\000\015\000\
\\043\000\014\000\044\000\013\000\045\000\012\000\046\000\011\000\000\000\
\\140\000\000\000\
\\141\000\000\000\
\\142\000\000\000\
\\143\000\000\000\
\\144\000\000\000\
\\145\000\000\000\
\\146\000\000\000\
\\147\000\000\000\
\\148\000\000\000\
\\149\000\000\000\
\\150\000\000\000\
\\151\000\000\000\
\\152\000\000\000\
\\153\000\000\000\
\\154\000\000\000\
\\155\000\039\000\018\000\040\000\017\000\041\000\016\000\042\000\015\000\
\\043\000\014\000\044\000\013\000\045\000\012\000\046\000\011\000\000\000\
\\156\000\000\000\
\\157\000\000\000\
\\158\000\000\000\
\\159\000\000\000\
\\160\000\000\000\
\\161\000\000\000\
\\162\000\000\000\
\\163\000\000\000\
\\164\000\032\000\132\000\000\000\
\\165\000\000\000\
\\166\000\000\000\
\\167\000\000\000\
\\168\000\004\000\075\000\008\000\074\000\009\000\073\000\010\000\072\000\
\\011\000\071\000\012\000\070\000\014\000\069\000\015\000\068\000\
\\016\000\067\000\019\000\065\000\020\000\064\000\021\000\063\000\
\\022\000\062\000\023\000\061\000\024\000\060\000\025\000\059\000\
\\026\000\058\000\000\000\
\\169\000\004\000\075\000\009\000\073\000\010\000\072\000\011\000\071\000\
\\012\000\070\000\014\000\069\000\015\000\068\000\016\000\067\000\
\\019\000\065\000\020\000\064\000\021\000\063\000\022\000\062\000\
\\023\000\061\000\024\000\060\000\026\000\058\000\000\000\
\\170\000\004\000\075\000\009\000\073\000\010\000\072\000\011\000\071\000\
\\012\000\070\000\014\000\069\000\015\000\068\000\016\000\067\000\000\000\
\\171\000\004\000\075\000\009\000\073\000\010\000\072\000\011\000\071\000\
\\012\000\070\000\014\000\069\000\015\000\068\000\016\000\067\000\000\000\
\\172\000\004\000\075\000\009\000\073\000\010\000\072\000\011\000\071\000\
\\012\000\070\000\014\000\069\000\015\000\068\000\016\000\067\000\000\000\
\\173\000\004\000\075\000\009\000\073\000\010\000\072\000\011\000\071\000\
\\012\000\070\000\014\000\069\000\015\000\068\000\016\000\067\000\000\000\
\\174\000\004\000\075\000\009\000\073\000\010\000\072\000\011\000\071\000\
\\012\000\070\000\014\000\069\000\015\000\068\000\016\000\067\000\
\\019\000\065\000\020\000\064\000\021\000\063\000\022\000\062\000\000\000\
\\175\000\004\000\075\000\009\000\073\000\010\000\072\000\011\000\071\000\
\\012\000\070\000\014\000\069\000\015\000\068\000\016\000\067\000\
\\019\000\065\000\020\000\064\000\021\000\063\000\022\000\062\000\000\000\
\\176\000\004\000\075\000\009\000\073\000\010\000\072\000\011\000\071\000\
\\012\000\070\000\014\000\069\000\015\000\068\000\016\000\067\000\
\\019\000\065\000\020\000\064\000\021\000\063\000\022\000\062\000\
\\023\000\061\000\024\000\060\000\000\000\
\\177\000\004\000\075\000\008\000\074\000\009\000\073\000\010\000\072\000\
\\011\000\071\000\012\000\070\000\014\000\069\000\015\000\068\000\
\\016\000\067\000\018\000\066\000\019\000\065\000\020\000\064\000\
\\021\000\063\000\022\000\062\000\023\000\061\000\024\000\060\000\
\\025\000\059\000\026\000\058\000\000\000\
\\178\000\004\000\075\000\008\000\074\000\009\000\073\000\010\000\072\000\
\\011\000\071\000\012\000\070\000\014\000\069\000\015\000\068\000\
\\016\000\067\000\018\000\066\000\019\000\065\000\020\000\064\000\
\\021\000\063\000\022\000\062\000\023\000\061\000\024\000\060\000\
\\025\000\059\000\026\000\058\000\000\000\
\\179\000\004\000\075\000\009\000\073\000\010\000\072\000\014\000\069\000\
\\015\000\068\000\016\000\067\000\000\000\
\\180\000\004\000\075\000\009\000\073\000\010\000\072\000\014\000\069\000\
\\015\000\068\000\016\000\067\000\000\000\
\\181\000\004\000\075\000\015\000\068\000\016\000\067\000\000\000\
\\182\000\004\000\075\000\015\000\068\000\016\000\067\000\000\000\
\\183\000\004\000\075\000\015\000\068\000\016\000\067\000\000\000\
\\184\000\000\000\
\\185\000\000\000\
\\186\000\004\000\075\000\015\000\068\000\016\000\067\000\000\000\
\\187\000\004\000\075\000\015\000\068\000\016\000\067\000\000\000\
\\188\000\000\000\
\\189\000\000\000\
\\190\000\004\000\075\000\009\000\073\000\010\000\072\000\014\000\069\000\
\\015\000\068\000\016\000\067\000\000\000\
\\191\000\000\000\
\\192\000\000\000\
\\193\000\000\000\
\\194\000\000\000\
\\195\000\000\000\
\\196\000\004\000\041\000\012\000\040\000\013\000\039\000\015\000\038\000\
\\016\000\037\000\017\000\036\000\027\000\035\000\028\000\034\000\
\\029\000\033\000\000\000\
\\197\000\004\000\075\000\008\000\074\000\009\000\073\000\010\000\072\000\
\\011\000\071\000\012\000\070\000\014\000\069\000\015\000\068\000\
\\016\000\067\000\018\000\066\000\019\000\065\000\020\000\064\000\
\\021\000\063\000\022\000\062\000\023\000\061\000\024\000\060\000\
\\025\000\059\000\026\000\058\000\000\000\
\\198\000\004\000\075\000\008\000\074\000\009\000\073\000\010\000\072\000\
\\011\000\071\000\012\000\070\000\014\000\069\000\015\000\068\000\
\\016\000\067\000\018\000\066\000\019\000\065\000\020\000\064\000\
\\021\000\063\000\022\000\062\000\023\000\061\000\024\000\060\000\
\\025\000\059\000\026\000\058\000\000\000\
\\199\000\004\000\075\000\008\000\074\000\009\000\073\000\010\000\072\000\
\\011\000\071\000\012\000\070\000\014\000\069\000\015\000\068\000\
\\016\000\067\000\018\000\066\000\019\000\065\000\020\000\064\000\
\\021\000\063\000\022\000\062\000\023\000\061\000\024\000\060\000\
\\025\000\059\000\026\000\058\000\000\000\
\\200\000\000\000\
\\201\000\000\000\
\\202\000\000\000\
\\203\000\000\000\
\\204\000\000\000\
\\205\000\000\000\
\\206\000\000\000\
\\207\000\000\000\
\\208\000\000\000\
\"
val actionRowNumbers =
"\034\000\028\000\035\000\047\000\
\\048\000\042\000\041\000\002\000\
\\033\000\029\000\103\000\102\000\
\\101\000\100\000\099\000\098\000\
\\097\000\003\000\040\000\050\000\
\\039\000\036\000\004\000\017\000\
\\024\000\043\000\005\000\050\000\
\\017\000\044\000\008\000\086\000\
\\088\000\087\000\089\000\017\000\
\\017\000\017\000\017\000\017\000\
\\025\000\030\000\037\000\009\000\
\\049\000\058\000\010\000\011\000\
\\091\000\021\000\022\000\023\000\
\\052\000\062\000\006\000\012\000\
\\017\000\017\000\017\000\017\000\
\\017\000\017\000\017\000\017\000\
\\017\000\080\000\079\000\017\000\
\\017\000\017\000\017\000\017\000\
\\017\000\016\000\046\000\082\000\
\\081\000\073\000\085\000\018\000\
\\032\000\038\000\095\000\061\000\
\\056\000\055\000\013\000\092\000\
\\017\000\091\000\017\000\051\000\
\\045\000\071\000\064\000\070\000\
\\069\000\068\000\067\000\066\000\
\\065\000\072\000\076\000\075\000\
\\074\000\077\000\078\000\001\000\
\\026\000\093\000\083\000\090\000\
\\031\000\057\000\019\000\014\000\
\\020\000\017\000\017\000\084\000\
\\096\000\007\000\091\000\007\000\
\\063\000\094\000\054\000\015\000\
\\059\000\091\000\007\000\027\000\
\\060\000\007\000\053\000\000\000"
val gotoT =
"\
\\001\000\135\000\002\000\008\000\003\000\007\000\004\000\006\000\
\\005\000\005\000\006\000\004\000\007\000\003\000\008\000\002\000\
\\014\000\001\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\010\000\018\000\000\000\
\\003\000\007\000\004\000\006\000\005\000\005\000\006\000\004\000\
\\007\000\003\000\008\000\021\000\014\000\001\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\002\000\027\000\003\000\007\000\004\000\006\000\005\000\005\000\
\\006\000\004\000\007\000\003\000\008\000\002\000\009\000\026\000\
\\014\000\001\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\012\000\030\000\000\000\
\\014\000\041\000\015\000\040\000\000\000\
\\000\000\
\\010\000\045\000\011\000\044\000\012\000\043\000\000\000\
\\003\000\007\000\004\000\006\000\005\000\005\000\006\000\004\000\
\\007\000\003\000\008\000\021\000\009\000\054\000\014\000\001\000\000\000\
\\012\000\055\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\012\000\075\000\000\000\
\\012\000\076\000\000\000\
\\012\000\077\000\000\000\
\\012\000\078\000\000\000\
\\012\000\079\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\012\000\087\000\016\000\086\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\010\000\045\000\011\000\044\000\012\000\043\000\000\000\
\\000\000\
\\012\000\093\000\000\000\
\\012\000\094\000\000\000\
\\012\000\095\000\000\000\
\\012\000\096\000\000\000\
\\012\000\097\000\000\000\
\\012\000\098\000\000\000\
\\012\000\099\000\000\000\
\\012\000\100\000\000\000\
\\012\000\101\000\000\000\
\\000\000\
\\000\000\
\\012\000\102\000\000\000\
\\012\000\103\000\000\000\
\\012\000\104\000\000\000\
\\012\000\105\000\000\000\
\\012\000\106\000\000\000\
\\012\000\107\000\000\000\
\\012\000\109\000\013\000\108\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\014\000\112\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\012\000\114\000\000\000\
\\012\000\087\000\016\000\115\000\000\000\
\\012\000\116\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\012\000\124\000\000\000\
\\012\000\125\000\000\000\
\\000\000\
\\000\000\
\\010\000\045\000\011\000\126\000\012\000\043\000\000\000\
\\012\000\087\000\016\000\127\000\000\000\
\\010\000\045\000\011\000\128\000\012\000\043\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\012\000\087\000\016\000\131\000\000\000\
\\010\000\045\000\011\000\132\000\012\000\043\000\000\000\
\\000\000\
\\000\000\
\\010\000\045\000\011\000\134\000\012\000\043\000\000\000\
\\000\000\
\\000\000\
\"
val numstates = 136
val numrules = 71
val s = ref "" and index = ref 0
val string_to_int = fn () => 
let val i = !index
in index := i+2; Char.ord(String.sub(!s,i)) + Char.ord(String.sub(!s,i+1)) * 256
end
val string_to_list = fn s' =>
    let val len = String.size s'
        fun f () =
           if !index < len then string_to_int() :: f()
           else nil
   in index := 0; s := s'; f ()
   end
val string_to_pairlist = fn (conv_key,conv_entry) =>
     let fun f () =
         case string_to_int()
         of 0 => EMPTY
          | n => PAIR(conv_key (n-1),conv_entry (string_to_int()),f())
     in f
     end
val string_to_pairlist_default = fn (conv_key,conv_entry) =>
    let val conv_row = string_to_pairlist(conv_key,conv_entry)
    in fn () =>
       let val default = conv_entry(string_to_int())
           val row = conv_row()
       in (row,default)
       end
   end
val string_to_table = fn (convert_row,s') =>
    let val len = String.size s'
        fun f ()=
           if !index < len then convert_row() :: f()
           else nil
     in (s := s'; index := 0; f ())
     end
local
  val memo = Array.array(numstates+numrules,ERROR)
  val _ =let fun g i=(Array.update(memo,i,REDUCE(i-numstates)); g(i+1))
       fun f i =
            if i=numstates then g i
            else (Array.update(memo,i,SHIFT (STATE i)); f (i+1))
          in f 0 handle General.Subscript => ()
          end
in
val entry_to_action = fn 0 => ACCEPT | 1 => ERROR | j => Array.sub(memo,(j-2))
end
val gotoT=Array.fromList(string_to_table(string_to_pairlist(NT,STATE),gotoT))
val actionRows=string_to_table(string_to_pairlist_default(T,entry_to_action),actionRows)
val actionRowNumbers = string_to_list actionRowNumbers
val actionT = let val actionRowLookUp=
let val a=Array.fromList(actionRows) in fn i=>Array.sub(a,i) end
in Array.fromList(List.map actionRowLookUp actionRowNumbers)
end
in LrTable.mkLrTable {actions=actionT,gotos=gotoT,numRules=numrules,
numStates=numstates,initialState=STATE 0}
end
end
local open Header in
type pos = int
type arg = unit
structure MlyValue = 
struct
datatype svalue = VOID' | ntVOID of unit ->  unit
 | NNUM of unit ->  (string) | RNUM of unit ->  (real)
 | DNUM of unit ->  (int) | ID of unit ->  (string)
 | opexpr of unit ->  (AST.expression option)
 | argumentDeclList of unit ->  (AST.id list)
 | typespec of unit ->  (AST.ctype)
 | argumentExprList of unit ->  (AST.expression list)
 | expr of unit ->  (AST.expression)
 | statement of unit ->  (AST.statement)
 | compoundStatement of unit ->  (AST.statement)
 | ostatementlist of unit ->  (AST.statement list)
 | declaration of unit ->  (AST.declaration)
 | var of unit ->  (AST.declaration)
 | func of unit ->  (AST.declaration)
 | funcdef of unit ->  (AST.declaration)
 | funcproto of unit ->  (AST.declaration)
 | funcsign of unit ->  ( ( AST.id * (AST.id list) ) )
 | sections of unit ->  (AST.declaration list)
 | program of unit ->  (AST.declaration list)
end
type svalue = MlyValue.svalue
type result = AST.declaration list
end
structure EC=
struct
open LrTable
infix 5 $$
fun x $$ y = y::x
val is_keyword =
fn (T 7) => true | (T 29) => true | (T 30) => true | (T 31) => true | 
(T 32) => true | (T 33) => true | (T 34) => true | (T 35) => true | 
(T 36) => true | (T 37) => true | _ => false
val preferred_change : (term list * term list) list = 
nil
val noShift = 
fn (T 0) => true | _ => false
val showTerminal =
fn (T 0) => "EOF"
  | (T 1) => "COLON"
  | (T 2) => "SEMICOLON"
  | (T 3) => "LPAREN"
  | (T 4) => "RPAREN"
  | (T 5) => "LCURLY"
  | (T 6) => "RCURLY"
  | (T 7) => "QUESTION"
  | (T 8) => "PERCENT"
  | (T 9) => "DIVIDE"
  | (T 10) => "PLUS"
  | (T 11) => "MINUS"
  | (T 12) => "BANG"
  | (T 13) => "TIMES"
  | (T 14) => "INC"
  | (T 15) => "DEC"
  | (T 16) => "ID"
  | (T 17) => "EQUALS"
  | (T 18) => "LTE"
  | (T 19) => "GTE"
  | (T 20) => "LT"
  | (T 21) => "GT"
  | (T 22) => "EQ"
  | (T 23) => "NEQ"
  | (T 24) => "OR"
  | (T 25) => "AND"
  | (T 26) => "DNUM"
  | (T 27) => "RNUM"
  | (T 28) => "NNUM"
  | (T 29) => "IF"
  | (T 30) => "THEN"
  | (T 31) => "ELSE"
  | (T 32) => "FOR"
  | (T 33) => "DO"
  | (T 34) => "WHILE"
  | (T 35) => "RETURN"
  | (T 36) => "BREAK"
  | (T 37) => "CONTINUE"
  | (T 38) => "CHAR"
  | (T 39) => "DOUBLE"
  | (T 40) => "FLOAT"
  | (T 41) => "INT"
  | (T 42) => "LONG"
  | (T 43) => "SHORT"
  | (T 44) => "STRING"
  | (T 45) => "VOID"
  | (T 46) => "COMMA"
  | _ => "bogus-term"
local open Header in
val errtermvalue=
fn _ => MlyValue.VOID'
end
val terms : term list = nil
 $$ (T 46) $$ (T 45) $$ (T 44) $$ (T 43) $$ (T 42) $$ (T 41) $$ (T 40)
 $$ (T 39) $$ (T 38) $$ (T 37) $$ (T 36) $$ (T 35) $$ (T 34) $$ (T 33)
 $$ (T 32) $$ (T 31) $$ (T 30) $$ (T 29) $$ (T 25) $$ (T 24) $$ (T 23)
 $$ (T 22) $$ (T 21) $$ (T 20) $$ (T 19) $$ (T 18) $$ (T 17) $$ (T 15)
 $$ (T 14) $$ (T 13) $$ (T 12) $$ (T 11) $$ (T 10) $$ (T 9) $$ (T 8)
 $$ (T 7) $$ (T 6) $$ (T 5) $$ (T 4) $$ (T 3) $$ (T 2) $$ (T 1) $$ (T 
0)end
structure Actions =
struct 
exception mlyAction of int
local open Header in
val actions = 
fn (i392,defaultPos,stack,
    (()):arg) =>
case (i392,stack)
of  ( 0, ( ( _, ( MlyValue.sections sections1, sections1left, 
sections1right)) :: rest671)) => let val  result = MlyValue.program
 (fn _ => let val  (sections as sections1) = sections1 ()
 in (sections)
end)
 in ( LrTable.NT 0, ( result, sections1left, sections1right), rest671)

end
|  ( 1, ( rest671)) => let val  result = MlyValue.program (fn _ => ([]
))
 in ( LrTable.NT 0, ( result, defaultPos, defaultPos), rest671)
end
|  ( 2, ( ( _, ( MlyValue.declaration declaration1, declaration1left, 
declaration1right)) :: rest671)) => let val  result = 
MlyValue.sections (fn _ => let val  (declaration as declaration1) = 
declaration1 ()
 in ([declaration])
end)
 in ( LrTable.NT 1, ( result, declaration1left, declaration1right), 
rest671)
end
|  ( 3, ( ( _, ( MlyValue.declaration declaration1, _, 
declaration1right)) :: ( _, ( MlyValue.sections sections1, 
sections1left, _)) :: rest671)) => let val  result = MlyValue.sections
 (fn _ => let val  (sections as sections1) = sections1 ()
 val  (declaration as declaration1) = declaration1 ()
 in (sections@[declaration])
end)
 in ( LrTable.NT 1, ( result, sections1left, declaration1right), 
rest671)
end
|  ( 4, ( ( _, ( _, _, RPAREN1right)) :: _ :: ( _, ( MlyValue.ID ID1,
 _, _)) :: ( _, ( MlyValue.typespec typespec1, typespec1left, _)) :: 
rest671)) => let val  result = MlyValue.funcsign (fn _ => let val  (
typespec as typespec1) = typespec1 ()
 val  (ID as ID1) = ID1 ()
 in (createstruc(SOME (AST.Function(SOME typespec,[])),ID),[])
end)
 in ( LrTable.NT 2, ( result, typespec1left, RPAREN1right), rest671)

end
|  ( 5, ( ( _, ( _, _, RPAREN1right)) :: ( _, ( 
MlyValue.argumentDeclList argumentDeclList1, _, _)) :: _ :: ( _, ( 
MlyValue.ID ID1, _, _)) :: ( _, ( MlyValue.typespec typespec1, 
typespec1left, _)) :: rest671)) => let val  result = MlyValue.funcsign
 (fn _ => let val  (typespec as typespec1) = typespec1 ()
 val  (ID as ID1) = ID1 ()
 val  (argumentDeclList as argumentDeclList1) = argumentDeclList1 ()
 in (
createstruc(SOME (AST.Function(SOME typespec,argumentDeclList)),ID),argumentDeclList
)
end)
 in ( LrTable.NT 2, ( result, typespec1left, RPAREN1right), rest671)

end
|  ( 6, ( ( _, ( _, _, SEMICOLON1right)) :: ( _, ( MlyValue.funcsign 
funcsign1, funcsign1left, _)) :: rest671)) => let val  result = 
MlyValue.funcproto (fn _ => let val  (funcsign as funcsign1) = 
funcsign1 ()
 in (AST.FuncDecl((#1 funcsign),(#2 funcsign),NONE))
end)
 in ( LrTable.NT 3, ( result, funcsign1left, SEMICOLON1right), rest671
)
end
|  ( 7, ( ( _, ( MlyValue.compoundStatement compoundStatement1, _, 
compoundStatement1right)) :: ( _, ( MlyValue.funcsign funcsign1, 
funcsign1left, _)) :: rest671)) => let val  result = MlyValue.funcdef
 (fn _ => let val  (funcsign as funcsign1) = funcsign1 ()
 val  (compoundStatement as compoundStatement1) = compoundStatement1
 ()
 in (AST.FuncDecl((#1 funcsign),(#2 funcsign),SOME compoundStatement))

end)
 in ( LrTable.NT 4, ( result, funcsign1left, compoundStatement1right),
 rest671)
end
|  ( 8, ( ( _, ( MlyValue.funcproto funcproto1, funcproto1left, 
funcproto1right)) :: rest671)) => let val  result = MlyValue.func (fn
 _ => let val  (funcproto as funcproto1) = funcproto1 ()
 in (funcproto)
end)
 in ( LrTable.NT 5, ( result, funcproto1left, funcproto1right), 
rest671)
end
|  ( 9, ( ( _, ( MlyValue.funcdef funcdef1, funcdef1left, 
funcdef1right)) :: rest671)) => let val  result = MlyValue.func (fn _
 => let val  (funcdef as funcdef1) = funcdef1 ()
 in (funcdef)
end)
 in ( LrTable.NT 5, ( result, funcdef1left, funcdef1right), rest671)

end
|  ( 10, ( ( _, ( _, _, SEMICOLON1right)) :: ( _, ( MlyValue.ID ID1, _
, _)) :: ( _, ( MlyValue.typespec typespec1, typespec1left, _)) :: 
rest671)) => let val  result = MlyValue.var (fn _ => let val  (
typespec as typespec1) = typespec1 ()
 val  (ID as ID1) = ID1 ()
 in (AST.VarDecl(createstruc(SOME typespec,ID),NONE))
end)
 in ( LrTable.NT 6, ( result, typespec1left, SEMICOLON1right), rest671
)
end
|  ( 11, ( ( _, ( _, _, SEMICOLON1right)) :: ( _, ( MlyValue.ID ID1, _
, _)) :: ( _, ( _, VOID1left, _)) :: rest671)) => let val  result = 
MlyValue.var (fn _ => let val  (ID as ID1) = ID1 ()
 in (AST.VarDecl(createstruc(NONE,ID),NONE))
end)
 in ( LrTable.NT 6, ( result, VOID1left, SEMICOLON1right), rest671)

end
|  ( 12, ( ( _, ( _, _, SEMICOLON1right)) :: ( _, ( MlyValue.expr 
expr1, _, _)) :: _ :: ( _, ( MlyValue.ID ID1, _, _)) :: ( _, ( _, 
VOID1left, _)) :: rest671)) => let val  result = MlyValue.var (fn _ =>
 let val  (ID as ID1) = ID1 ()
 val  (expr as expr1) = expr1 ()
 in (AST.VarDecl(createstruc(NONE,ID),SOME expr))
end)
 in ( LrTable.NT 6, ( result, VOID1left, SEMICOLON1right), rest671)

end
|  ( 13, ( ( _, ( _, _, SEMICOLON1right)) :: ( _, ( MlyValue.expr 
expr1, _, _)) :: _ :: ( _, ( MlyValue.ID ID1, _, _)) :: ( _, ( 
MlyValue.typespec typespec1, typespec1left, _)) :: rest671)) => let
 val  result = MlyValue.var (fn _ => let val  (typespec as typespec1)
 = typespec1 ()
 val  (ID as ID1) = ID1 ()
 val  (expr as expr1) = expr1 ()
 in (AST.VarDecl(createstruc(SOME typespec,ID),SOME expr))
end)
 in ( LrTable.NT 6, ( result, typespec1left, SEMICOLON1right), rest671
)
end
|  ( 14, ( ( _, ( MlyValue.var var1, var1left, var1right)) :: rest671)
) => let val  result = MlyValue.declaration (fn _ => let val  (var as 
var1) = var1 ()
 in (var)
end)
 in ( LrTable.NT 7, ( result, var1left, var1right), rest671)
end
|  ( 15, ( ( _, ( MlyValue.func func1, func1left, func1right)) :: 
rest671)) => let val  result = MlyValue.declaration (fn _ => let val 
 (func as func1) = func1 ()
 in (func)
end)
 in ( LrTable.NT 7, ( result, func1left, func1right), rest671)
end
|  ( 16, ( ( _, ( MlyValue.statement statement1, _, statement1right))
 :: ( _, ( MlyValue.ostatementlist ostatementlist1, 
ostatementlist1left, _)) :: rest671)) => let val  result = 
MlyValue.ostatementlist (fn _ => let val  (ostatementlist as 
ostatementlist1) = ostatementlist1 ()
 val  (statement as statement1) = statement1 ()
 in (ostatementlist@[statement])
end)
 in ( LrTable.NT 8, ( result, ostatementlist1left, statement1right), 
rest671)
end
|  ( 17, ( rest671)) => let val  result = MlyValue.ostatementlist (fn
 _ => ([]))
 in ( LrTable.NT 8, ( result, defaultPos, defaultPos), rest671)
end
|  ( 18, ( ( _, ( _, _, RCURLY1right)) :: ( _, ( 
MlyValue.ostatementlist ostatementlist1, _, _)) :: ( _, ( 
MlyValue.sections sections1, _, _)) :: ( _, ( _, LCURLY1left, _)) :: 
rest671)) => let val  result = MlyValue.compoundStatement (fn _ => let
 val  (sections as sections1) = sections1 ()
 val  (ostatementlist as ostatementlist1) = ostatementlist1 ()
 in (AST.STMT(AST.Compound(sections,ostatementlist)))
end)
 in ( LrTable.NT 9, ( result, LCURLY1left, RCURLY1right), rest671)
end
|  ( 19, ( ( _, ( _, _, RCURLY1right)) :: ( _, ( 
MlyValue.ostatementlist ostatementlist1, _, _)) :: ( _, ( _, 
LCURLY1left, _)) :: rest671)) => let val  result = 
MlyValue.compoundStatement (fn _ => let val  (ostatementlist as 
ostatementlist1) = ostatementlist1 ()
 in (AST.STMT(AST.Compound([],ostatementlist)))
end)
 in ( LrTable.NT 9, ( result, LCURLY1left, RCURLY1right), rest671)
end
|  ( 20, ( ( _, ( MlyValue.statement statement1, _, statement1right))
 :: _ :: ( _, ( MlyValue.opexpr opexpr3, _, _)) :: _ :: ( _, ( 
MlyValue.opexpr opexpr2, _, _)) :: _ :: ( _, ( MlyValue.opexpr opexpr1
, _, _)) :: _ :: ( _, ( _, FOR1left, _)) :: rest671)) => let val  
result = MlyValue.statement (fn _ => let val  opexpr1 = opexpr1 ()
 val  opexpr2 = opexpr2 ()
 val  opexpr3 = opexpr3 ()
 val  (statement as statement1) = statement1 ()
 in (createfor(opexpr1,opexpr2,opexpr3,statement))
end)
 in ( LrTable.NT 10, ( result, FOR1left, statement1right), rest671)

end
|  ( 21, ( ( _, ( MlyValue.statement statement1, _, statement1right))
 :: _ :: ( _, ( MlyValue.expr expr1, _, _)) :: _ :: ( _, ( _, 
WHILE1left, _)) :: rest671)) => let val  result = MlyValue.statement
 (fn _ => let val  (expr as expr1) = expr1 ()
 val  (statement as statement1) = statement1 ()
 in (createwhile(expr,statement))
end)
 in ( LrTable.NT 10, ( result, WHILE1left, statement1right), rest671)

end
|  ( 22, ( ( _, ( _, _, SEMICOLON1right)) :: ( _, ( _, BREAK1left, _))
 :: rest671)) => let val  result = MlyValue.statement (fn _ => (
AST.STMT(AST.Break)))
 in ( LrTable.NT 10, ( result, BREAK1left, SEMICOLON1right), rest671)

end
|  ( 23, ( ( _, ( _, _, SEMICOLON1right)) :: ( _, ( _, CONTINUE1left,
 _)) :: rest671)) => let val  result = MlyValue.statement (fn _ => (
AST.STMT(AST.Continue)))
 in ( LrTable.NT 10, ( result, CONTINUE1left, SEMICOLON1right), 
rest671)
end
|  ( 24, ( ( _, ( _, _, SEMICOLON1right)) :: ( _, ( MlyValue.opexpr 
opexpr1, _, _)) :: ( _, ( _, RETURN1left, _)) :: rest671)) => let val 
 result = MlyValue.statement (fn _ => let val  (opexpr as opexpr1) = 
opexpr1 ()
 in (AST.STMT( AST.Return(opexpr) ))
end)
 in ( LrTable.NT 10, ( result, RETURN1left, SEMICOLON1right), rest671)

end
|  ( 25, ( ( _, ( MlyValue.compoundStatement compoundStatement1, 
compoundStatement1left, compoundStatement1right)) :: rest671)) => let
 val  result = MlyValue.statement (fn _ => let val  (compoundStatement
 as compoundStatement1) = compoundStatement1 ()
 in (compoundStatement)
end)
 in ( LrTable.NT 10, ( result, compoundStatement1left, 
compoundStatement1right), rest671)
end
|  ( 26, ( ( _, ( MlyValue.statement statement1, _, statement1right))
 :: _ :: ( _, ( MlyValue.expr expr1, _, _)) :: _ :: ( _, ( _, IF1left,
 _)) :: rest671)) => let val  result = MlyValue.statement (fn _ => let
 val  (expr as expr1) = expr1 ()
 val  (statement as statement1) = statement1 ()
 in (AST.STMT(AST.IfThen(expr,statement)))
end)
 in ( LrTable.NT 10, ( result, IF1left, statement1right), rest671)
end
|  ( 27, ( ( _, ( MlyValue.statement statement2, _, statement2right))
 :: _ :: ( _, ( MlyValue.statement statement1, _, _)) :: _ :: ( _, ( 
MlyValue.expr expr1, _, _)) :: _ :: ( _, ( _, IF1left, _)) :: rest671)
) => let val  result = MlyValue.statement (fn _ => let val  (expr as 
expr1) = expr1 ()
 val  statement1 = statement1 ()
 val  statement2 = statement2 ()
 in (AST.STMT(AST.IfThenElse(expr,statement1,statement2)))
end)
 in ( LrTable.NT 10, ( result, IF1left, statement2right), rest671)
end
|  ( 28, ( ( _, ( _, _, SEMICOLON1right)) :: ( _, ( MlyValue.expr 
expr1, expr1left, _)) :: rest671)) => let val  result = 
MlyValue.statement (fn _ => let val  (expr as expr1) = expr1 ()
 in (AST.STMT(AST.Expr(expr)))
end)
 in ( LrTable.NT 10, ( result, expr1left, SEMICOLON1right), rest671)

end
|  ( 29, ( ( _, ( _, SEMICOLON1left, SEMICOLON1right)) :: rest671)) =>
 let val  result = MlyValue.statement (fn _ => (
AST.STMT(AST.ErrorStmt)))
 in ( LrTable.NT 10, ( result, SEMICOLON1left, SEMICOLON1right), 
rest671)
end
|  ( 30, ( ( _, ( MlyValue.expr expr3, _, expr3right)) :: _ :: ( _, ( 
MlyValue.expr expr2, _, _)) :: _ :: ( _, ( MlyValue.expr expr1, 
expr1left, _)) :: rest671)) => let val  result = MlyValue.expr (fn _
 => let val  expr1 = expr1 ()
 val  expr2 = expr2 ()
 val  expr3 = expr3 ()
 in (createx(AST.QuestionColon(expr1,expr2,expr3)))
end)
 in ( LrTable.NT 11, ( result, expr1left, expr3right), rest671)
end
|  ( 31, ( ( _, ( MlyValue.expr expr2, _, expr2right)) :: _ :: ( _, ( 
MlyValue.expr expr1, expr1left, _)) :: rest671)) => let val  result = 
MlyValue.expr (fn _ => let val  expr1 = expr1 ()
 val  expr2 = expr2 ()
 in ( createx(AST.Binop(AST.Or,expr1,expr2) ))
end)
 in ( LrTable.NT 11, ( result, expr1left, expr2right), rest671)
end
|  ( 32, ( ( _, ( MlyValue.expr expr2, _, expr2right)) :: _ :: ( _, ( 
MlyValue.expr expr1, expr1left, _)) :: rest671)) => let val  result = 
MlyValue.expr (fn _ => let val  expr1 = expr1 ()
 val  expr2 = expr2 ()
 in ( createx(AST.Binop(AST.Lte,expr1,expr2) ))
end)
 in ( LrTable.NT 11, ( result, expr1left, expr2right), rest671)
end
|  ( 33, ( ( _, ( MlyValue.expr expr2, _, expr2right)) :: _ :: ( _, ( 
MlyValue.expr expr1, expr1left, _)) :: rest671)) => let val  result = 
MlyValue.expr (fn _ => let val  expr1 = expr1 ()
 val  expr2 = expr2 ()
 in ( createx(AST.Binop(AST.Gte,expr1,expr2) ))
end)
 in ( LrTable.NT 11, ( result, expr1left, expr2right), rest671)
end
|  ( 34, ( ( _, ( MlyValue.expr expr2, _, expr2right)) :: _ :: ( _, ( 
MlyValue.expr expr1, expr1left, _)) :: rest671)) => let val  result = 
MlyValue.expr (fn _ => let val  expr1 = expr1 ()
 val  expr2 = expr2 ()
 in ( createx(AST.Binop(AST.Lt,expr1,expr2) ))
end)
 in ( LrTable.NT 11, ( result, expr1left, expr2right), rest671)
end
|  ( 35, ( ( _, ( MlyValue.expr expr2, _, expr2right)) :: _ :: ( _, ( 
MlyValue.expr expr1, expr1left, _)) :: rest671)) => let val  result = 
MlyValue.expr (fn _ => let val  expr1 = expr1 ()
 val  expr2 = expr2 ()
 in ( createx(AST.Binop(AST.Gt,expr1,expr2) ))
end)
 in ( LrTable.NT 11, ( result, expr1left, expr2right), rest671)
end
|  ( 36, ( ( _, ( MlyValue.expr expr2, _, expr2right)) :: _ :: ( _, ( 
MlyValue.expr expr1, expr1left, _)) :: rest671)) => let val  result = 
MlyValue.expr (fn _ => let val  expr1 = expr1 ()
 val  expr2 = expr2 ()
 in ( createx(AST.Binop(AST.Eq,expr1,expr2) ))
end)
 in ( LrTable.NT 11, ( result, expr1left, expr2right), rest671)
end
|  ( 37, ( ( _, ( MlyValue.expr expr2, _, expr2right)) :: _ :: ( _, ( 
MlyValue.expr expr1, expr1left, _)) :: rest671)) => let val  result = 
MlyValue.expr (fn _ => let val  expr1 = expr1 ()
 val  expr2 = expr2 ()
 in ( createx(AST.Binop(AST.Neq,expr1,expr2) ))
end)
 in ( LrTable.NT 11, ( result, expr1left, expr2right), rest671)
end
|  ( 38, ( ( _, ( MlyValue.expr expr2, _, expr2right)) :: _ :: ( _, ( 
MlyValue.expr expr1, expr1left, _)) :: rest671)) => let val  result = 
MlyValue.expr (fn _ => let val  expr1 = expr1 ()
 val  expr2 = expr2 ()
 in ( createx(AST.Binop(AST.And,expr1,expr2) ))
end)
 in ( LrTable.NT 11, ( result, expr1left, expr2right), rest671)
end
|  ( 39, ( ( _, ( MlyValue.expr expr2, _, expr2right)) :: _ :: ( _, ( 
MlyValue.expr expr1, expr1left, _)) :: rest671)) => let val  result = 
MlyValue.expr (fn _ => let val  expr1 = expr1 ()
 val  expr2 = expr2 ()
 in ( createx(AST.Assign(expr1, expr2) ))
end)
 in ( LrTable.NT 11, ( result, expr1left, expr2right), rest671)
end
|  ( 40, ( ( _, ( MlyValue.expr expr1, _, expr1right)) :: ( _, ( _, 
BANG1left, _)) :: rest671)) => let val  result = MlyValue.expr (fn _
 => let val  (expr as expr1) = expr1 ()
 in ( createx(AST.Unop(AST.Not,expr) ))
end)
 in ( LrTable.NT 11, ( result, BANG1left, expr1right), rest671)
end
|  ( 41, ( ( _, ( MlyValue.expr expr2, _, expr2right)) :: _ :: ( _, ( 
MlyValue.expr expr1, expr1left, _)) :: rest671)) => let val  result = 
MlyValue.expr (fn _ => let val  expr1 = expr1 ()
 val  expr2 = expr2 ()
 in ( createx(AST.Binop(AST.Plus,expr1,expr2) ))
end)
 in ( LrTable.NT 11, ( result, expr1left, expr2right), rest671)
end
|  ( 42, ( ( _, ( MlyValue.expr expr2, _, expr2right)) :: _ :: ( _, ( 
MlyValue.expr expr1, expr1left, _)) :: rest671)) => let val  result = 
MlyValue.expr (fn _ => let val  expr1 = expr1 ()
 val  expr2 = expr2 ()
 in ( createx(AST.Binop(AST.Minus,expr1,expr2) ))
end)
 in ( LrTable.NT 11, ( result, expr1left, expr2right), rest671)
end
|  ( 43, ( ( _, ( MlyValue.expr expr2, _, expr2right)) :: _ :: ( _, ( 
MlyValue.expr expr1, expr1left, _)) :: rest671)) => let val  result = 
MlyValue.expr (fn _ => let val  expr1 = expr1 ()
 val  expr2 = expr2 ()
 in ( createx(AST.Binop(AST.Times,expr1,expr2) ))
end)
 in ( LrTable.NT 11, ( result, expr1left, expr2right), rest671)
end
|  ( 44, ( ( _, ( MlyValue.expr expr2, _, expr2right)) :: _ :: ( _, ( 
MlyValue.expr expr1, expr1left, _)) :: rest671)) => let val  result = 
MlyValue.expr (fn _ => let val  expr1 = expr1 ()
 val  expr2 = expr2 ()
 in ( createx(AST.Binop(AST.Divide,expr1,expr2) ))
end)
 in ( LrTable.NT 11, ( result, expr1left, expr2right), rest671)
end
|  ( 45, ( ( _, ( MlyValue.expr expr2, _, expr2right)) :: _ :: ( _, ( 
MlyValue.expr expr1, expr1left, _)) :: rest671)) => let val  result = 
MlyValue.expr (fn _ => let val  expr1 = expr1 ()
 val  expr2 = expr2 ()
 in ( createx(AST.Binop(AST.Mod,expr1,expr2) ))
end)
 in ( LrTable.NT 11, ( result, expr1left, expr2right), rest671)
end
|  ( 46, ( ( _, ( _, _, INC1right)) :: ( _, ( MlyValue.expr expr1, 
expr1left, _)) :: rest671)) => let val  result = MlyValue.expr (fn _
 => let val  (expr as expr1) = expr1 ()
 in (createx(AST.Unop(AST.PostInc,expr)))
end)
 in ( LrTable.NT 11, ( result, expr1left, INC1right), rest671)
end
|  ( 47, ( ( _, ( _, _, DEC1right)) :: ( _, ( MlyValue.expr expr1, 
expr1left, _)) :: rest671)) => let val  result = MlyValue.expr (fn _
 => let val  (expr as expr1) = expr1 ()
 in (createx(AST.Unop(AST.PostDec,expr)))
end)
 in ( LrTable.NT 11, ( result, expr1left, DEC1right), rest671)
end
|  ( 48, ( ( _, ( MlyValue.expr expr1, _, expr1right)) :: ( _, ( _, 
INC1left, _)) :: rest671)) => let val  result = MlyValue.expr (fn _ =>
 let val  (expr as expr1) = expr1 ()
 in (createx(AST.Unop(AST.PreInc,expr)))
end)
 in ( LrTable.NT 11, ( result, INC1left, expr1right), rest671)
end
|  ( 49, ( ( _, ( MlyValue.expr expr1, _, expr1right)) :: ( _, ( _, 
DEC1left, _)) :: rest671)) => let val  result = MlyValue.expr (fn _ =>
 let val  (expr as expr1) = expr1 ()
 in (createx(AST.Unop(AST.PreDec,expr)))
end)
 in ( LrTable.NT 11, ( result, DEC1left, expr1right), rest671)
end
|  ( 50, ( ( _, ( _, _, RPAREN1right)) :: _ :: ( _, ( MlyValue.expr 
expr1, expr1left, _)) :: rest671)) => let val  result = MlyValue.expr
 (fn _ => let val  (expr as expr1) = expr1 ()
 in (createx(AST.Call(expr,[])))
end)
 in ( LrTable.NT 11, ( result, expr1left, RPAREN1right), rest671)
end
|  ( 51, ( ( _, ( _, _, RPAREN1right)) :: ( _, ( 
MlyValue.argumentExprList argumentExprList1, _, _)) :: _ :: ( _, ( 
MlyValue.expr expr1, expr1left, _)) :: rest671)) => let val  result = 
MlyValue.expr (fn _ => let val  (expr as expr1) = expr1 ()
 val  (argumentExprList as argumentExprList1) = argumentExprList1 ()
 in (createx(AST.Call(expr,argumentExprList)))
end)
 in ( LrTable.NT 11, ( result, expr1left, RPAREN1right), rest671)
end
|  ( 52, ( ( _, ( MlyValue.expr expr1, _, expr1right)) :: ( _, ( _, 
MINUS1left, _)) :: rest671)) => let val  result = MlyValue.expr (fn _
 => let val  (expr as expr1) = expr1 ()
 in (createx(AST.Unop(AST.Negate,expr)))
end)
 in ( LrTable.NT 11, ( result, MINUS1left, expr1right), rest671)
end
|  ( 53, ( ( _, ( MlyValue.NNUM NNUM1, NNUM1left, NNUM1right)) :: 
rest671)) => let val  result = MlyValue.expr (fn _ => let val  (NNUM
 as NNUM1) = NNUM1 ()
 in (createx(AST.StringConst(NNUM)))
end)
 in ( LrTable.NT 11, ( result, NNUM1left, NNUM1right), rest671)
end
|  ( 54, ( ( _, ( MlyValue.DNUM DNUM1, DNUM1left, DNUM1right)) :: 
rest671)) => let val  result = MlyValue.expr (fn _ => let val  (DNUM
 as DNUM1) = DNUM1 ()
 in (createx(AST.IntConst(DNUM)))
end)
 in ( LrTable.NT 11, ( result, DNUM1left, DNUM1right), rest671)
end
|  ( 55, ( ( _, ( MlyValue.RNUM RNUM1, RNUM1left, RNUM1right)) :: 
rest671)) => let val  result = MlyValue.expr (fn _ => let val  (RNUM
 as RNUM1) = RNUM1 ()
 in (createx(AST.RealConst(RNUM)))
end)
 in ( LrTable.NT 11, ( result, RNUM1left, RNUM1right), rest671)
end
|  ( 56, ( ( _, ( MlyValue.ID ID1, ID1left, ID1right)) :: rest671)) =>
 let val  result = MlyValue.expr (fn _ => let val  (ID as ID1) = ID1
 ()
 in ( createx(AST.Id(createstruc(NONE,ID))))
end)
 in ( LrTable.NT 11, ( result, ID1left, ID1right), rest671)
end
|  ( 57, ( ( _, ( _, _, RPAREN1right)) :: ( _, ( MlyValue.expr expr1,
 _, _)) :: ( _, ( _, LPAREN1left, _)) :: rest671)) => let val  result
 = MlyValue.expr (fn _ => let val  (expr as expr1) = expr1 ()
 in (expr)
end)
 in ( LrTable.NT 11, ( result, LPAREN1left, RPAREN1right), rest671)

end
|  ( 58, ( rest671)) => let val  result = MlyValue.opexpr (fn _ => (
NONE))
 in ( LrTable.NT 15, ( result, defaultPos, defaultPos), rest671)
end
|  ( 59, ( ( _, ( MlyValue.expr expr1, expr1left, expr1right)) :: 
rest671)) => let val  result = MlyValue.opexpr (fn _ => let val  (expr
 as expr1) = expr1 ()
 in (SOME expr)
end)
 in ( LrTable.NT 15, ( result, expr1left, expr1right), rest671)
end
|  ( 60, ( ( _, ( MlyValue.expr expr1, expr1left, expr1right)) :: 
rest671)) => let val  result = MlyValue.argumentExprList (fn _ => let
 val  (expr as expr1) = expr1 ()
 in ([expr])
end)
 in ( LrTable.NT 12, ( result, expr1left, expr1right), rest671)
end
|  ( 61, ( ( _, ( MlyValue.expr expr1, _, expr1right)) :: _ :: ( _, ( 
MlyValue.argumentExprList argumentExprList1, argumentExprList1left, _)
) :: rest671)) => let val  result = MlyValue.argumentExprList (fn _ =>
 let val  (argumentExprList as argumentExprList1) = argumentExprList1
 ()
 val  (expr as expr1) = expr1 ()
 in (argumentExprList@[expr])
end)
 in ( LrTable.NT 12, ( result, argumentExprList1left, expr1right), 
rest671)
end
|  ( 62, ( ( _, ( MlyValue.ID ID1, _, ID1right)) :: ( _, ( 
MlyValue.typespec typespec1, typespec1left, _)) :: rest671)) => let
 val  result = MlyValue.argumentDeclList (fn _ => let val  (typespec
 as typespec1) = typespec1 ()
 val  (ID as ID1) = ID1 ()
 in ([createstruc(SOME typespec,ID)])
end)
 in ( LrTable.NT 14, ( result, typespec1left, ID1right), rest671)
end
|  ( 63, ( ( _, ( MlyValue.ID ID1, _, ID1right)) :: ( _, ( 
MlyValue.typespec typespec1, _, _)) :: _ :: ( _, ( 
MlyValue.argumentDeclList argumentDeclList1, argumentDeclList1left, _)
) :: rest671)) => let val  result = MlyValue.argumentDeclList (fn _ =>
 let val  (argumentDeclList as argumentDeclList1) = argumentDeclList1
 ()
 val  (typespec as typespec1) = typespec1 ()
 val  (ID as ID1) = ID1 ()
 in (argumentDeclList@[createstruc(SOME typespec,ID)])
end)
 in ( LrTable.NT 14, ( result, argumentDeclList1left, ID1right), 
rest671)
end
|  ( 64, ( ( _, ( _, CHAR1left, CHAR1right)) :: rest671)) => let val  
result = MlyValue.typespec (fn _ => (AST.Numeric(AST.CHAR)))
 in ( LrTable.NT 13, ( result, CHAR1left, CHAR1right), rest671)
end
|  ( 65, ( ( _, ( _, DOUBLE1left, DOUBLE1right)) :: rest671)) => let
 val  result = MlyValue.typespec (fn _ => (AST.Numeric(AST.DOUBLE)))
 in ( LrTable.NT 13, ( result, DOUBLE1left, DOUBLE1right), rest671)

end
|  ( 66, ( ( _, ( _, FLOAT1left, FLOAT1right)) :: rest671)) => let
 val  result = MlyValue.typespec (fn _ => (AST.Numeric(AST.FLOAT)))
 in ( LrTable.NT 13, ( result, FLOAT1left, FLOAT1right), rest671)
end
|  ( 67, ( ( _, ( _, INT1left, INT1right)) :: rest671)) => let val  
result = MlyValue.typespec (fn _ => (AST.Numeric(AST.INT)))
 in ( LrTable.NT 13, ( result, INT1left, INT1right), rest671)
end
|  ( 68, ( ( _, ( _, LONG1left, LONG1right)) :: rest671)) => let val  
result = MlyValue.typespec (fn _ => (AST.Numeric(AST.LONG)))
 in ( LrTable.NT 13, ( result, LONG1left, LONG1right), rest671)
end
|  ( 69, ( ( _, ( _, SHORT1left, SHORT1right)) :: rest671)) => let
 val  result = MlyValue.typespec (fn _ => (AST.Numeric(AST.SHORT)))
 in ( LrTable.NT 13, ( result, SHORT1left, SHORT1right), rest671)
end
|  ( 70, ( ( _, ( _, STRING1left, STRING1right)) :: rest671)) => let
 val  result = MlyValue.typespec (fn _ => (AST.NonNumeric))
 in ( LrTable.NT 13, ( result, STRING1left, STRING1right), rest671)

end
| _ => raise (mlyAction i392)
end
val void = MlyValue.VOID'
val extract = fn a => (fn MlyValue.program x => x
| _ => let exception ParseInternal
	in raise ParseInternal end) a ()
end
end
structure Tokens : CComp_TOKENS =
struct
type svalue = ParserData.svalue
type ('a,'b) token = ('a,'b) Token.token
fun EOF (p1,p2) = Token.TOKEN (ParserData.LrTable.T 0,(
ParserData.MlyValue.VOID',p1,p2))
fun COLON (p1,p2) = Token.TOKEN (ParserData.LrTable.T 1,(
ParserData.MlyValue.VOID',p1,p2))
fun SEMICOLON (p1,p2) = Token.TOKEN (ParserData.LrTable.T 2,(
ParserData.MlyValue.VOID',p1,p2))
fun LPAREN (p1,p2) = Token.TOKEN (ParserData.LrTable.T 3,(
ParserData.MlyValue.VOID',p1,p2))
fun RPAREN (p1,p2) = Token.TOKEN (ParserData.LrTable.T 4,(
ParserData.MlyValue.VOID',p1,p2))
fun LCURLY (p1,p2) = Token.TOKEN (ParserData.LrTable.T 5,(
ParserData.MlyValue.VOID',p1,p2))
fun RCURLY (p1,p2) = Token.TOKEN (ParserData.LrTable.T 6,(
ParserData.MlyValue.VOID',p1,p2))
fun QUESTION (p1,p2) = Token.TOKEN (ParserData.LrTable.T 7,(
ParserData.MlyValue.VOID',p1,p2))
fun PERCENT (p1,p2) = Token.TOKEN (ParserData.LrTable.T 8,(
ParserData.MlyValue.VOID',p1,p2))
fun DIVIDE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 9,(
ParserData.MlyValue.VOID',p1,p2))
fun PLUS (p1,p2) = Token.TOKEN (ParserData.LrTable.T 10,(
ParserData.MlyValue.VOID',p1,p2))
fun MINUS (p1,p2) = Token.TOKEN (ParserData.LrTable.T 11,(
ParserData.MlyValue.VOID',p1,p2))
fun BANG (p1,p2) = Token.TOKEN (ParserData.LrTable.T 12,(
ParserData.MlyValue.VOID',p1,p2))
fun TIMES (p1,p2) = Token.TOKEN (ParserData.LrTable.T 13,(
ParserData.MlyValue.VOID',p1,p2))
fun INC (p1,p2) = Token.TOKEN (ParserData.LrTable.T 14,(
ParserData.MlyValue.VOID',p1,p2))
fun DEC (p1,p2) = Token.TOKEN (ParserData.LrTable.T 15,(
ParserData.MlyValue.VOID',p1,p2))
fun ID (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 16,(
ParserData.MlyValue.ID (fn () => i),p1,p2))
fun EQUALS (p1,p2) = Token.TOKEN (ParserData.LrTable.T 17,(
ParserData.MlyValue.VOID',p1,p2))
fun LTE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 18,(
ParserData.MlyValue.VOID',p1,p2))
fun GTE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 19,(
ParserData.MlyValue.VOID',p1,p2))
fun LT (p1,p2) = Token.TOKEN (ParserData.LrTable.T 20,(
ParserData.MlyValue.VOID',p1,p2))
fun GT (p1,p2) = Token.TOKEN (ParserData.LrTable.T 21,(
ParserData.MlyValue.VOID',p1,p2))
fun EQ (p1,p2) = Token.TOKEN (ParserData.LrTable.T 22,(
ParserData.MlyValue.VOID',p1,p2))
fun NEQ (p1,p2) = Token.TOKEN (ParserData.LrTable.T 23,(
ParserData.MlyValue.VOID',p1,p2))
fun OR (p1,p2) = Token.TOKEN (ParserData.LrTable.T 24,(
ParserData.MlyValue.VOID',p1,p2))
fun AND (p1,p2) = Token.TOKEN (ParserData.LrTable.T 25,(
ParserData.MlyValue.VOID',p1,p2))
fun DNUM (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 26,(
ParserData.MlyValue.DNUM (fn () => i),p1,p2))
fun RNUM (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 27,(
ParserData.MlyValue.RNUM (fn () => i),p1,p2))
fun NNUM (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 28,(
ParserData.MlyValue.NNUM (fn () => i),p1,p2))
fun IF (p1,p2) = Token.TOKEN (ParserData.LrTable.T 29,(
ParserData.MlyValue.VOID',p1,p2))
fun THEN (p1,p2) = Token.TOKEN (ParserData.LrTable.T 30,(
ParserData.MlyValue.VOID',p1,p2))
fun ELSE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 31,(
ParserData.MlyValue.VOID',p1,p2))
fun FOR (p1,p2) = Token.TOKEN (ParserData.LrTable.T 32,(
ParserData.MlyValue.VOID',p1,p2))
fun DO (p1,p2) = Token.TOKEN (ParserData.LrTable.T 33,(
ParserData.MlyValue.VOID',p1,p2))
fun WHILE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 34,(
ParserData.MlyValue.VOID',p1,p2))
fun RETURN (p1,p2) = Token.TOKEN (ParserData.LrTable.T 35,(
ParserData.MlyValue.VOID',p1,p2))
fun BREAK (p1,p2) = Token.TOKEN (ParserData.LrTable.T 36,(
ParserData.MlyValue.VOID',p1,p2))
fun CONTINUE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 37,(
ParserData.MlyValue.VOID',p1,p2))
fun CHAR (p1,p2) = Token.TOKEN (ParserData.LrTable.T 38,(
ParserData.MlyValue.VOID',p1,p2))
fun DOUBLE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 39,(
ParserData.MlyValue.VOID',p1,p2))
fun FLOAT (p1,p2) = Token.TOKEN (ParserData.LrTable.T 40,(
ParserData.MlyValue.VOID',p1,p2))
fun INT (p1,p2) = Token.TOKEN (ParserData.LrTable.T 41,(
ParserData.MlyValue.VOID',p1,p2))
fun LONG (p1,p2) = Token.TOKEN (ParserData.LrTable.T 42,(
ParserData.MlyValue.VOID',p1,p2))
fun SHORT (p1,p2) = Token.TOKEN (ParserData.LrTable.T 43,(
ParserData.MlyValue.VOID',p1,p2))
fun STRING (p1,p2) = Token.TOKEN (ParserData.LrTable.T 44,(
ParserData.MlyValue.VOID',p1,p2))
fun VOID (p1,p2) = Token.TOKEN (ParserData.LrTable.T 45,(
ParserData.MlyValue.VOID',p1,p2))
fun COMMA (p1,p2) = Token.TOKEN (ParserData.LrTable.T 46,(
ParserData.MlyValue.VOID',p1,p2))
end
end
