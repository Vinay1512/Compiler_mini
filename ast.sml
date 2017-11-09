(*
To Be Added:
 Function prototypes now include only :: (int a,int b) and not (int,int)
*)
structure Abstract	  =
struct

	datatype intKind = CHAR | INT | LONG | FLOAT | DOUBLE | SHORT

    

	datatype binop
	    = Plus | Minus | Times | Divide | Mod
	    | Gt | Lt | Gte | Lte | Eq | Neq | And | Or
	
	datatype unop
	    = Not  | PreInc | PostInc | PreDec | PostDec

	datatype declaration
    	= VarDecl of id * (expression option)
    	| FuncDecl of id * id list * (statement option)

    and statement = STMT of coreStatement 

    and coreStatement
	    = Expr of expression 
	    | Compound of declaration list * statement list (*Imposes all declarations should be in start*)
	    | While of expression * statement
	    | Do of expression * statement
	    | For of expression option * expression option * expression option * statement
	    | Break
	    | Continue
	    | Return of expression option
	    | IfThen of expression * statement
	    | IfThenElse of expression * statement * statement
	    
	    | ErrorStmt
	
	and expression = EXPR of coreExpression
    
    and coreExpression
	    = IntConst of int
	    | RealConst of real
	    | StringConst of string                 
	    | Call of expression * expression list (*Function Call*)
        | Assign of expression * expression
	    | QuestionColon of expression * expression * expression (*Terneary*)
	    (*| Comma of expression * expression (* Maybe later use for printf*)*)
	    | Binop of binop * expression * expression
	    | Unop of unop * expression
	    | Id of id
	    | ErrorExpr	

   (*
    fun eqInt(CHAR, CHAR) = true
    | eqInt(SHORT, SHORT) = true
    | eqInt(INT, INT) = true
    | eqInt(LONG, LONG) = true
    | eqInt(FLOAT, FLOAT) = true
    | eqInt(DOUBLE, DOUBLE) = true
    | eqInt _ = false
    *)
 	and ctype
	    = Numeric of intKind 
	    | NonNumeric (*Only String support*)
	    | Function of ctype option * (id list)
	    | Undetermined
	    

	 
	withtype id = { name: string, ctype:ctype} (* associated type *)     



	type ast = declaration list
end;