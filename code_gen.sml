
structure AST = Abstract;

structure Code_gen =
struct

exception ErrorExpression;
exception TypeDeclError;
exception ErrorStatement;
(*fun extostring (AST.EXPR(x)) = String.concat(["(",(corextostring(x)),")"])*)
  (*| extostring _  = raise ErrorExpression*)

fun extostring (AST.EXPR(x)) =  corextostring(x)

and corextostring(AST.IntConst x) = Int.toString(x)
  | corextostring(AST.RealConst x) = Real.toString(x)
  | corextostring(AST.StringConst x) = String.concat(["\"",x,"\""])
  | corextostring(AST.Call(x,[])) = let 
                                      val z = extostring(x)
                                    in 
                                      if(z="print") then
                                        String.concat(["console.log","()"])
                                      else 
                                        String.concat([z,"()"])
                                    end
  | corextostring(AST.Call(x,y)) = let
                                      val expry = String.extract((String.concat(map (fn z => String.concat([",",extostring(z)])) y)),1,NONE)
                                      val z = extostring(x)
                                    in
                                      if(z="print") then
                                        String.concat(["console.log","(",expry,")"])
                                      else 
                                        String.concat([z,"(",expry,")"])
                                      
                                    end
  | corextostring(AST.Assign(x,y)) = String.concat([extostring(x)," = ",extostring(y)])
  | corextostring(AST.QuestionColon(x,y,z)) = String.concat([extostring(x)," ? ",extostring(y)," : ",extostring(z)])
  | corextostring(AST.Binop(x,y,z)) = String.concat([extostring(y),binoptostring(x),extostring(z)])
  | corextostring(AST.Unop(x,y)) = unopextostring((x,y))
  | corextostring(AST.Id x) =  #name x  
  | corextostring(AST.ErrorExpr) = raise ErrorExpression


and unopextostring (AST.Not     , y) = String.concat(["!",extostring(y)])
  | unopextostring (AST.PreInc  , y) = String.concat(["++",extostring(y)])
  | unopextostring (AST.PreDec  , y) = String.concat(["--",extostring(y)])
  | unopextostring (AST.PostInc , y) = String.concat([extostring(y),"++"])
  | unopextostring (AST.PostDec , y) = String.concat([extostring(y),"--"])   
  | unopextostring (AST.Negate  , y) = String.concat(["-",extostring(y)]) 


(*Note Javascript returns output of 1 && 2 as 2 not true*)
and binoptostring AST.Plus   = " + "  
  | binoptostring AST.Minus  = " - "  
  | binoptostring AST.Times  = " * "  
  | binoptostring AST.Divide = " / "  
  | binoptostring AST.Mod    = " % "  
  | binoptostring AST.Gt     = " > "  
  | binoptostring AST.Lt     = " < "  
  | binoptostring AST.Gte    = " >= " 
  | binoptostring AST.Lte    = " <= "  
  | binoptostring AST.Eq     = " == "   
  | binoptostring AST.Neq    = " != "  
  | binoptostring AST.And    = " & &"  
  | binoptostring AST.Or     = " || "  

and stostring (AST.STMT(x)) = String.concat([corestostring(x),"; \n"])
  (*| stostring _  = raise ErrorStatement*)

and slisttostring ([]) = "\n"
  | slisttostring x = String.concat((map (stostring) x))


and corestostring(AST.Expr x) = extostring( x)
  | corestostring(AST.Compound (x,y)) = String.concat(["{",decllisttostring(x),slisttostring(y),"}"])
  | corestostring(AST.While (x,y)) = String.concat(["while (",extostring(x),") \n \t",stostring(y)])
  | corestostring(AST.For (x,y,z,s)) = String.concat(["for (",opextostring(x),";",opextostring(y),";",opextostring(z),") \n \t",stostring(s)])
  | corestostring(AST.Break)  = "break"
  | corestostring(AST.Continue)  = "continue"
  | corestostring(AST.Return x) = String.concat(["return",opextostring(x)])
  | corestostring(AST.IfThen (x,y)) = String.concat(["if (",extostring(x),") \n \t",stostring(y)])
  | corestostring(AST.IfThenElse (x,y,z)) = String.concat(["if (",extostring(x),") \n \t",stostring(y),"else \n \t",stostring(z)])
  | corestostring _  = raise ErrorStatement

and opextostring (NONE) = ""
  | opextostring (SOME x) = extostring(x)


and decltostring (AST.VarDecl(x,y)) = String.concat([ctypetostring((#ctype x)),(#name x)," = ",opextostring(y),"; \n"])
  | decltostring (AST.FuncDecl(x,y,z)) = String.concat(["function ",#name x,"(",idlisttostring(y),")",opstostring(z),"\n"])

and opstostring (NONE) = ";"
  | opstostring (SOME x) = String.concat(["\n \t",stostring(x)])

and idtostring x = #name x

and idlisttostring [] = ""
  | idlisttostring x  = String.extract((String.concat(map (fn z => String.concat([",",idtostring(z)])) x)),1,NONE)

and decllisttostring ([]) = "\n"
  | decllisttostring (x)  = String.concat((map (decltostring) x))
(*
fun ctypetostring (AST.Numeric x) = String.concat()
  | ctypetostring (AST.NonNumeric x) = "var"
  | ctypetostring (AST.Function x) = 
  | ctypetostring _ = raise "TYPE Decl ERROR";
*)

and ctypetostring (AST.Undetermined) = raise TypeDeclError
  | ctypetostring (AST.Function(x,y)) = "function "
  | ctypetostring (x) = "var "


fun convert_to_js(x:AST.ast) = decllisttostring(x)


fun gencode(filename,file_to_write) = let val absyn = Parse.parse(filename)
                                                 val file_out = TextIO.openOut file_to_write
                                                 val gen_code = convert_to_js(absyn)
                                                 fun write_output(t) = TextIO.output(file_out,t)
                                            in
                                                write_output(gen_code);
                                                TextIO.closeOut(file_out)

                                             end


end
