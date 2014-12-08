(*Ezra Varady
* ezra.varady@students.olin.edu*)

(* Internal representation *)

datatype value = VInt of int
               | VBool of bool
               | VList of value list
      	       | VPair of value * value
               | VFun of function

and expr = EVal of value
         | EAdd of expr * expr
         | ESub of expr * expr
         | EMul of expr * expr
         | ENeg of expr
         | EEq of expr * expr
         | EIf of expr * expr * expr
         | ELet of string * expr * expr
         | EIdent of string
         | ECall of string * expr

         | ECons of expr * expr
         | EIsEmpty of expr
         | EHead of expr
         | ETail of expr

         | EPair of expr * expr
         | EFirst of expr
         | ESecond of expr
         | ESlet of (string * expr) list * expr

         | ECallE of expr * expr

and function = FDef of string * expr   



(* Functions to create errors *)

fun evalError msg = raise Fail ("Eval Error @ "^msg)

fun unimplemented msg = raise Fail ("CODE NOT IMPLEMENTED - "^msg)




(* Primitive operations *)

fun applyAdd (VInt i1) (VInt i2) = VInt (i1+i2)
  | applyAdd _ _ = evalError "applyAdd"

fun applyMul (VInt i1) (VInt i2) = VInt (i1*i2)
  | applyMul _ _ = evalError "applyMul"

fun applyNeg (VInt i) = VInt (~ i)
  | applyNeg _ = evalError "applyNeg"

fun applyEq (VInt i1) (VInt i2) = VBool (i1 = i2)
  | applyEq (VBool b1) (VBool b2) = VBool (b1 = b2)
  | applyEq _ _ = evalError "applyEq"

fun applySub v1 v2 = applyAdd v1 (applyNeg v2)




(* COMPLETE THE FOLLOWING FOR QUESTION 1 *)

fun applyPair i j  = VPair (i,j)

fun applyFirst (VPair (x,y))  = x 
  | applyFirst _ = evalError "apllyFirst"

fun applySecond (VPair (x,y)) = y
  | applySecond _ = evalError "applySecond"

fun applyCons i (VList j) = VList(i::j)
  | applyCons i j = evalError "applyCons"

fun applyIsEmpty i = 
  if i = (VList [])
  then (VBool true)
  else (VBool false)

fun applyHead (VList []) = evalError "applyHeadTop"
  | applyHead (VList (v::vl)) = v
  | applyHead _ = evalError "applyHead"

fun reverseVL (VList []) = []
  | reverseVL (VList (x::xl)) = (reverseVL (VList xl))@[x]
  | reverseVL _ = evalError "reverseVL"

(*Brendan provided invaluable help in finding 2 nasty bugs in applyTail*)
fun applyTail (VList []) = evalError "applyTail"
  | applyTail (VList (v::vl)) =  (VList vl)
  | applyTail _ = evalError "applyTail"

(* Substitution function -- COMPLETE the missing cases *)
fun idMatch (((ident,exp):(string*expr))::bndgs) id = 
    if not (ident = id) 
    then idMatch bndgs id
    else false 
  | idMatch [] id = true

fun subst (EVal v) id e = EVal v
  | subst (EAdd (e1,e2)) id e = EAdd (subst e1 id e, subst e2 id e)
  | subst (ESub (e1,e2)) id e = ESub (subst e1 id e, subst e2 id e)
  | subst (EMul (e1,e2)) id e = EMul (subst e1 id e, subst e2 id e)
  | subst (ENeg e1) id e = ENeg (subst e1 id e)
  | subst (EEq (e1,e2)) id e = EEq (subst e1 id e, subst e2 id e)
  | subst (EIf (e1,e2,e3)) id e = EIf (subst e1 id e, 
                                       subst e2 id e,
                                       subst e3 id e)
  | subst (ELet (id',e1,e2)) id e = 
      if id = id'
      then ELet (id',subst e1 id e, e2)
      else ELet (id',subst e1 id e, subst e2 id e)
  | subst (EIdent id') id e = if id = id'
                                then e
                              else EIdent id'
  | subst (ECall (n,e1)) id e = ECall (n,subst e1 id e)
  | subst (ECons (e1,e2)) id e = ECons (subst e1 id e, subst e2 id e) 
  | subst (EIsEmpty e1) id e = EIsEmpty (subst e1 id e)
  | subst (EHead e1) id e = EHead (subst e1 id e)
  | subst (ETail e1) id e = ETail (subst e1 id e)
  | subst (EPair (e1,e2)) id e = EPair (subst e1 id e, subst e2 id e) 
  | subst (EFirst e1) id e = EFirst (subst e1 id e) 
  | subst (ESecond e1) id e = ESecond (subst e1 id e)
  | subst (ESlet (bnds,e1)) id e =
    if idMatch bnds id
    then ESlet ((expSub bnds id e), (subst e1 id e))
    else ESlet ((expSub bnds id e), e1)
    
  | subst (ECallE (e1,e2)) id e = ECallE (subst e1 id e, subst e2 id e) 

and expSub ((ident, exp)::bndgs) id e = (ident, subst exp id e)::(expSub bndgs id e)
  | expSub [] id e = []


    (* Lookup a function name in the function environment *)

fun lookup name [] = evalError ("lookup - "^name)
  | lookup name ((n,f)::fenv) = 
      if (n = name)
        then f
      else lookup name fenv 

(* Evaluation function -- COMPLETE the missing cases *)

fun eval _ (EVal v) = v
  | eval fenv (EAdd (e1,e2)) = applyAdd (eval fenv e1) (eval fenv e2)
  | eval fenv (ESub (e1,e2)) = applySub (eval fenv e1) (eval fenv e2)
  | eval fenv (EMul (e1,e2)) = applyMul (eval fenv e1) (eval fenv e2)
  | eval fenv (ENeg e) = applyNeg (eval fenv e)
  | eval fenv (EEq (e1,e2)) = applyEq (eval fenv e1) (eval fenv e2)
  | eval fenv (EIf (e1,e2,e3)) = evalIf fenv (eval fenv e1) e2 e3
  | eval fenv (ELet (n,e1,e2)) = evalLet fenv n (eval fenv e1) e2
  | eval fenv (EIdent id) = VFun (lookup id fenv)
  | eval fenv (ECall (name,e)) = 
                evalCall fenv (lookup name fenv) (eval fenv e)
  | eval fenv (ESlet (bnds,f)) = evalSLet fenv bnds f 
  | eval fenv (ECons (e1,e2)) =  applyCons (eval fenv e1) (eval fenv e2)
  | eval fenv (EIsEmpty e) = (applyIsEmpty  (eval fenv e:value))
  | eval fenv (EHead e) = applyHead (eval fenv e)
  | eval fenv (ETail e) = applyTail (eval fenv e)
  | eval fenv (EPair (e1,e2)) = applyPair (eval fenv e1) (eval fenv e2) 
  | eval fenv (EFirst e) = applyFirst (eval fenv e)
  | eval fenv (ESecond e) = applySecond (eval fenv e)
  | eval fenv (ECallE (func, e)) = (evalE fenv (eval fenv func) e)

and evalE fenv (VFun (FDef (param, body))) e =
    eval fenv (subst body param e)

and evalCall fenv (FDef (param,body)) arg = 
      eval fenv (subst body param (EVal arg))

and evalIf fenv (VBool true) ethen eelse = eval fenv ethen
  | evalIf fenv (VBool false) ethen eelse = eval fenv eelse
  | evalIf _ _ _ _ = evalError "evalIf"

and evalLet fenv id v body = eval fenv (subst body id (EVal v))

and evalSLet fenv (((ident, exp):(string*expr))::bnd)  f = evalSLet fenv bnd (subst f ident exp)
  | evalSLet fenv [] f = eval fenv f

(* Sample functions for testing *)

val succ = ("succ",
            FDef ("n",
	          EAdd (EIdent "n", EVal (VInt 1))))

val pred = ("pred",
	    FDef ("n",
		  ESub (EIdent "n", EVal (VInt 1))))

val exp = ("exp",
    	   FDef ("args",
		 ELet ("a", EFirst (EIdent "args"),
		       ELet ("n", ESecond (EIdent "args"),
			     EIf (EEq (EIdent "n", EVal (VInt 0)),
				  EVal (VInt 1),
				  EMul (EIdent "a",
					ECall ("exp",
					       EPair (EIdent "a",
						      ECall ("pred",
							     EIdent "n")))))))))

val addT = ("addT", 
	    FDef ("args",
		  ELet ("a", EFirst (EIdent "args"),
			ELet ("b", ESecond (EIdent "args"),
			      EAdd (EIdent "a", EIdent "b")))))

val swap = ("swap",
	    FDef ("args",
		  ELet ("x", EFirst (EIdent "args"),
			ELet ("y", ESecond (EIdent "args"),
			      ESlet ([("x",EIdent "y"),("y",EIdent "x")],
				     EPair (EIdent "x", 
					    EIdent "y"))))))

val append = ("append", 
	      FDef ("args",
		    ELet ("xs",EFirst (EIdent "args"),
			  ELet ("ys",ESecond (EIdent "args"),
				EIf (EIsEmpty (EIdent "xs"),
				     EIdent "ys",
				     ECons (EHead (EIdent "xs"),
					    ECall ("append",
						   EPair (ETail (EIdent "xs"),
							  EIdent "ys"))))))))

val length = ("length",
	      FDef ("xs",
		    EIf (EIsEmpty (EIdent "xs"),
			 EVal (VInt 0),
			 EAdd (EVal (VInt 1),
			       ECall ("length", ETail (EIdent "xs"))))))



val twice = ("twice",
             FDef ("args",
		   ELet ("f", EFirst (EIdent "args"),
			 ELet ("x", ESecond (EIdent "args"),
			       ECallE (EIdent "f", 
				       ECallE (EIdent "f",
					       EIdent "x"))))))

val mapf = ("mapf",
	    FDef ("args",
		  ELet ("f", EFirst (EIdent "args"),
			ELet ("xs", ESecond (EIdent "args"),
			      EIf (EIsEmpty (EIdent "xs"),
				   EVal (VList []),
				   ECons (ECallE (EIdent "f",
						  EHead (EIdent "xs")),
					  ECall ("mapf",
						 EPair (EIdent "f",
							ETail (EIdent "xs")))))))))
