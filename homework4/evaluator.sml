(* 
 *   CODE FOR HOMEWORK 4
 *)


structure Evaluator = struct

  structure I = InternalRepresentation



  exception Evaluation of string

  fun evalError msg = raise Evaluation msg


  (* 
   *   Primitive operations
   *)

  fun primPlus (I.VInt a) (I.VInt b) = I.VInt (a+b)
    | primPlus _ _ = evalError "primPlus"

  fun primMinus (I.VInt a) (I.VInt b) = I.VInt (a-b)
    | primMinus _ _ = evalError "primMinus"

  fun primHd (I.VList (head::body)) = head

  fun primTl (I.VList (head::body)) = I.VList body

  fun primEq (I.VInt a) (I.VInt b) = I.VBool (a=b)
    | primEq (I.VBool a) (I.VBool b) = I.VBool (a=b)
    | primEq (I.VList (a::al)) (I.VList (b::bl)) =
        (case primEq a b
        of (I.VBool true) => primEq (I.VList al) (I.VList bl) 
         | (I.VBool false) => I.VBool false
         | _ => evalError "primEQ")
    | primEq (I.VList []) (I.VList []) = I.VBool true
    | primEq _ _ = I.VBool false

  fun primLess (I.VInt a) (I.VInt b) = I.VBool (a<b)
    | primLess _ _ = I.VBool false
	
  fun primCons a (I.VList b) = I.VList (a::b)
    |  primCons _ _ = evalError "cannot apply primCons"

    
  
  fun intervalGen (I.VInt a) (I.VInt b) (I.VList ll) =
    if a=b then (primCons (I.VInt a) (I.VList ll))
    else intervalGen (I.VInt a) (I.VInt (b-1)) (primCons (I.VInt b) (I.VList ll)) 
  
  fun primInterval (I.VInt a) (I.VInt b) = intervalGen (I.VInt a) (I.VInt b) (I.VList [])
     
  fun lookup (name:string) [] = evalError ("failed lookup for "^name)
    | lookup name ((n,v)::env) = 
        if (n = name) then 
	  v
	else lookup name env 


(*
   *   Evaluation functions
   * 
   *)


  fun eval _ (I.EVal v) = v
    | eval env (I.EFun (n,e)) = I.VClosure (n,e,env)
    | eval env (I.EIf (e,f,g)) = evalIf env (eval env e) f g
    | eval env (I.ELet (name,e,f)) = evalLet env name (eval env e) f
    | eval env (I.ELetFun (name,param,e,f)) = evalLetFun env name param e f
    | eval env (I.EIdent n) = lookup n env
    | eval env (I.EApp (e1,e2)) = evalApp env (eval env e1) (eval env e2)
    | eval env (I.EPrimCall1 (f,e1)) = f (eval env e1)
    | eval env (I.EPrimCall2 (f,e1,e2)) = f (eval env e1) (eval env e2)
    | eval env (I.ERecord fs) = I.VRecord (map (fn (x,y) => (x, (eval env y))) fs)
    | eval env (I.EField (e,s)) =  lookup s (case eval env e of (I.VRecord r) =>
        r | _ => evalError "Parse field lied")
      
  and evalApp _ (I.VClosure (n,body,env)) v = eval ((n,v)::env) body
    | evalApp _ (I.VRecClosure (f,n,body,env)) v = let
	  val new_env = [(f,I.VRecClosure (f,n,body,env)),(n,v)]@env
      in 
	  eval new_env body
      end
    | evalApp _ _ _ = evalError "cannot apply non-functional value"

  and evalIf env (I.VBool true) f g = eval env f
    | evalIf env (I.VBool false) f g = eval env g
    | evalIf _ _ _ _ = evalError "evalIf"
		       
  and evalLet env id v body = eval ((id,v)::env) body

  and evalLetFun env id param expr body = let
      val f = I.VRecClosure (id, param, expr, env)
  in
      eval ((id,f)::env) body
  end

  fun primMap (I.VClosure f) (I.VList []) = (I.VList []) 
    | primMap (I.VClosure (n,body,env)) (I.VList (l::ll)) =
    let 
        val head = eval env (I.EApp (I.EFun (n,body), I.EVal l))
    in 
        (case primMap (I.VClosure (n,body,env)) (I.VList ll)
        of (I.VList tail) => I.VList (head::tail)) 
    end

  fun primFilter (I.VClosure f) (I.VList []) = (I.VList [])
    | primFilter (I.VClosure (n,body,env)) (I.VList (l::ll)) =
    let 
        val head = eval env (I.EApp (I.EFun (n,body), I.EVal l))
    in 
        (case head 
        of (I.VBool true) =>  
        (case primFilter (I.VClosure (n,body,env)) (I.VList ll)
        of (I.VList tail) => I.VList (l::tail))
         | (I.VBool false) =>
        (case primFilter (I.VClosure (n,body,env)) (I.VList ll)
        of (I.VList tail) => I.VList ([]@tail)))
    end


  (* 
   *   Initial environment (already in a form suitable for the environment)
   *)

  val initialEnv = 
      [("add", I.VClosure ("a", 
			   I.EFun ("b", 
				   I.EPrimCall2 (primPlus,
						 I.EIdent "a",
						 I.EIdent "b")),
			   [])),
       ("sub", I.VClosure ("a", 
			   I.EFun ("b", 
				   I.EPrimCall2 (primMinus,
						 I.EIdent "a",
						 I.EIdent "b")),
			   [])),
       ("equal", I.VClosure ("a",
			  I.EFun ("b",
				  I.EPrimCall2 (primEq,
						I.EIdent "a",
						I.EIdent "b")),
			  [])),
       ("less", I.VClosure ("a",
			    I.EFun ("b",
				    I.EPrimCall2 (primLess,
						  I.EIdent "a",
						  I.EIdent "b")),
			    [])),
       ("nil", I.VList ([])),
       ("cons", I.VClosure ("x",
                I.EFun ("xs",
                    I.EPrimCall2 (primCons,
                        I.EIdent "x",
                        I.EIdent "xs")),[]
                        )),
       ("map", I.VClosure ("f",
               I.EFun ("xs",
                   I.EPrimCall2 (primMap,
                   I.EIdent "f",
                   I.EIdent "xs")),[]
                        )),
       ("filter", I.VClosure ("f",
                  I.EFun ("xs",
                      I.EPrimCall2 (primFilter,
                      I.EIdent "f",
                      I.EIdent "xs")),[]
                      )),
       ("hd", I.VClosure ("x",
              I.EPrimCall1 (primHd,
                  I.EIdent "x"),[])),
                  
       ("interval", I.VClosure ("q",
                    I.EFun ("f",
                    I.EPrimCall2 (primInterval,
                    I.EIdent "q",
                    I.EIdent "f")),[])),
       ("tl", I.VClosure ("x",
              I.EPrimCall1 (primTl,
                  I.EIdent "x"),[]))]
  
end
