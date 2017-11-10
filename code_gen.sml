
structure AST = Abstract;

structure Code_gen =
struct

fun extostring (AST.EXPR(x)) = String.Concat("(",[corextostring(x),")"])
  | extostring _ = print "Error"

fun corextostring(AST.IntConst x) = Int.toString(x)
  | corextostring(AST.RealConst x) = Real.toString(x)
  | corextostring(AST.StringConst x) = x
  | corextostring(AST.Call(x,[])) = String.concat([extostring(x),"()"])
  | corextostring(AST.Call(x,y)) = let
                                      val expry = String.extract((String.Concat(map (fn z => String.Concat([",",extostring(z)])) y)),1,NONE)
                                    in
                                      String.concat([extostring(x),"(",expry,")"])
                                    end
  | corextostring(AST.Assign(x,y)) = String.concat([extostring(x),"=",extostring(y)])
  | corextostring(AST.QuestionColon(x,y,z)) = String.concat([extostring(x),"?",extostring(y),":",extostring(z)])
  | corextostring(AST.Binop(x,y,z)) = String.concat([extostring(y),binoptostring(x),extostring(z)])
  | corextostring(AST.Unop(x,y)) = unopextostring(AST.Unop(x,y))
  | corextostring(AST.Id x) = #name x;
  | corextostring(AST.ErrorExpr) = print "Error Passing Expression"


fun unopextostring (AST.Not     , y) = String.Concat(["!",extostring(y)])
  | unopextostring (AST.PreInc  , y) = String.Concat(["++",extostring(y)])
  | unopextostring (AST.PreDec  , y) = String.Concat(["--",extostring(y)])
  | unopextostring (AST.PostInc , y) = String.Concat([extostring(y),"++"])
  | unopextostring (AST.PostDec , y) = String.Concat([extostring(y),"--"])   
  | unopextostring (AST.Negate  , y) = String.Concat(["-",extostring(y)]) 


(*Note Javascript returns output of 1 && 2 as 2 not true*)
fun binoptostring AST.Plus   = "+"  
  | binoptostring AST.Minus  = "-"  
  | binoptostring AST.Times  = "*"  
  | binoptostring AST.Divide = "/"  
  | binoptostring AST.Mod    = "%"  
  | binoptostring AST.Gt     = ">"  
  | binoptostring AST.Lt     = "<"  
  | binoptostring AST.Gte    = ">=" 
  | binoptostring AST.Lte    = "<="  
  | binoptostring AST.Eq     = "=="  
  | binoptostring AST.Neq    = "!="  
  | binoptostring AST.And    = "&&"  
  | binoptostring AST.Or     = "||"  

fun extostring (AST.STMT(x)) = String.Concat([corestostring(x),"\n"])
  | extostring _ = print "Error"


fun convert_statements([],s) = s
  | convert_statements(statm::statms,s) = let val s1 = convert_statement(statm)
                                              val s_new = String.concat([s,s1]) in
                                              convert_statements(statms,s_new)
                                          end

and convert_statement(Absyn.decl(x,y)) = String.concat(["var " , x ," = " , expr_to_string(y),";" , "\n"])
  | convert_statement(Absyn.assign(x,y)) = String.concat([x ," = " , expr_to_string(y),";" ,"\n"])
  | convert_statement(Absyn.ifelse(statm1,exp,statm2)) =
                let val e = expr_to_string(exp)
                    val s1 = convert_statement(statm1)
                    val s2 = convert_statement(statm2) in
                    String.concat(["if ( ",e ," )", "{" , "\n" , s1 , "}","\n", "else ","{" ,"\n",s2 , "}"])
                end

  | convert_statement(Absyn.loop(exp,statms)) = let val e = expr_to_string(exp)
                                                    val s = convert_statements(statms,"") in
                      String.concat(["while","(", e,")","{","\n",s,"}","\n"])
                      end
  | convert_statement(Absyn.ifstat(statm,exp)) = let val e = expr_to_string(exp)
                                                     val s1 = convert_statement(statm) in
                                      String.concat(["if"," ( ",e," ) ", " { " ,"\n",s1,"}"])
                                  end
  | convert_statement(Absyn.Break) = "break"
  | convert_statement(Absyn.Continue) = "continue"
  | convert_statement(Absyn.Return) = "return"




fun convert_to_js(absyn) = let val statm = hd absyn
                               val code_gen = convert_statement(statm) in
                               code_gen
                            end


fun code_generator(filename,file_to_write) = let val absyn = Parse.parse(filename)
                                                 val file_out = TextIO.openOut file_to_write
                                                 val gen_code = convert_to_js(absyn)
                                                 fun write_output(t) = TextIO.output(file_out,t)
                                            in
                                                write_output(gen_code);
                                                TextIO.closeOut(file_out)

                                             end


end
