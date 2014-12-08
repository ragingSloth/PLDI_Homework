(*Ezra Varady
* ezra.varady@students.olin.edu*)

fun gcd a 0 = if a < 0 then ~a else a
  | gcd 0 a = if a < 0 then ~a else a
  | gcd  a b = 
    if a > b orelse ~a > b then gcd b (a mod b)
    else gcd a (b mod a)

fun lcm a b = 
  if a*b>0 then (a*b) div  (gcd a b)
    else ~(a*b) div  (gcd a b)

fun expHelper pow a 1 = pow
  | expHelper pow a n = expHelper (pow*a) a (n-1)

fun exp a 0 = 1
  | exp a 1 = a
  | exp a n = expHelper a a n

fun tetraHelper a pow 1 = pow
  | tetraHelper a pow n = tetraHelper a (exp a pow) (n-1)

fun tetra a 0 = 1
  | tetra 0 n = 1
  | tetra a n = tetraHelper a a n

fun sum [] = 0
  | sum (x::xl) = if length xl > 0 then x + sum xl
    else x

fun prod [] = 0
  | prod (x::xl) = if length xl > 0 then x * prod xl
    else x
fun dropFirst [] = []
  | dropFirst (x::xl) = xl

fun every_other [] = []
  | every_other (x::xl) = x::every_other (dropFirst xl)

fun flatten [] = []
  | flatten (x::xl) = x@flatten xl

fun first [] = []
  | first (x::xl) = [x]

fun reverse [] = []
  | reverse (x::xs) = (reverse xs)@[x]

fun revL [] = []
  | revL (x::xl) = (reverse x)::(revL xl)

fun heads [] = []
  | heads (x::xl) = (first x)@(heads xl)

fun tails [] = []
  | tails xl = heads (revL xl)

fun scaleList n [] = []
  | scaleList n (x::xl) = (n*x)::(scaleList n xl)

fun scaleMat n [] = []
  | scaleMat n (x::xl) = (scaleList n x)::(scaleMat n xl)
  
fun addList [] [] = []
  | addList (x::xl) (y::yl) = (x+y)::(addList xl yl)

fun addMat [] [] = []
  | addMat (x::xl) (y::yl) = (addList x y)::(addMat xl yl) 

exception TypeError of string

exception DivisionByZero of string

fun scaleVec a [] = []
  | scaleVec a (x::xs) = (a*x)::(scaleVec a xs)

fun addVec [] [] = []
  | addVec (x::xs) (y::ys) = (x+y)::(addVec xs ys)
  | addVec _ _ = []

fun inner [] [] = 0
  | inner (x::xs) (y::ys) = (x*y) + (inner xs ys)
  | inner _ _ = 0

datatype value = VInt of int
	       | VVec of int list
	       | VMat of int list list
	       | VRat of int * int

datatype expr = EInt of int
	      | EVec of int list
	      | EMat of int list list
          | ERat of int*int
          | EAdd of expr * expr
	      | ESub of expr * expr
	      | EMul of expr * expr
	      | ENeg of expr
	      | EDiv of expr * expr
 fun dubNeg (r:int*int) = 
  if #1 r < 0 andalso #2 r < 0 then (#1 r - #1 r*2, #2 r - #2 r*2)
  else r

fun simplifyRat (r:int*int) =  
  if #2 r = 0 then raise DivisionByZero "division by zero\n" 
  else dubNeg((#1 r div (gcd (#1 r:int) (#2 r:int)), #2 r div (gcd (#1 r:int) (#2r:int))))

fun addRat (r:int*int)( s:int*int) = simplifyRat((#1 r*(lcm (#2 r:int) (#2 s:int)) div #2 r + #1 s*((lcm (#2 r:int) (#2 s:int)) div #2 s),(lcm (#2 r:int) (#2 s:int))))
  
and mulRat (r:int*int) (l:int*int) = simplifyRat((#1 r * #1 l, #2 r * #2 l))

fun negRat (r:int*int) = mulRat (~1,1) r 

fun flipRat (r:int*int) = (#2 r, #1 r)

fun applyAdd (VInt i) (VInt j) = VInt (i+j)
  | applyAdd (VVec v) (VVec w) = VVec (addVec v w)
  | applyAdd (VMat m) (VMat n) = VMat (addMat m n)
  | applyAdd (VInt i) (VRat r) = VRat (addRat (i,1) r)
  | applyAdd (VRat r) (VRat l) = VRat (addRat r l)
  | applyAdd (VRat r) (VInt i) = VRat (addRat (i,1) r)
  | applyAdd _ _ = raise TypeError "applyAdd"

fun applyMul (VInt i) (VInt j) = VInt (i*j)
  | applyMul (VInt i) (VVec v) = VVec (scaleVec i v)
  | applyMul (VVec v) (VVec w) = VInt (inner v w)
  | applyMul (VInt i) (VMat m) = VMat (scaleMat i m)
  | applyMul (VInt i) (VRat r) = VRat (mulRat (i,1) r)
  | applyMul (VRat r) (VRat l) = VRat (mulRat r l)
  | applyMul (VRat r) (VInt i) = VRat (mulRat (i,1) r)
  | applyMul _ _ = raise TypeError "applyMul"

fun applyDiv (VInt i) (VInt j) = VRat (simplifyRat (i,j))
  | applyDiv (VInt i) (VRat r) = VRat (mulRat (1,i) r)
  | applyDiv (VRat r) (VRat l) = VRat (mulRat r (flipRat l))
  | applyDiv (VRat r) (VInt i) = VRat (mulRat (1,i) r)

fun applyNeg (VInt i) = VInt (~ i)
  | applyNeg (VVec v) = VVec (scaleVec ~1 v)
  | applyNeg (VMat m) = VMat (scaleMat ~1 m)
  | applyNeg (VRat r) = VRat (mulRat (~1,1) r)

fun applySub a b = applyAdd a (applyNeg b)


fun eval (EInt i) = VInt i
  | eval (EAdd (e,f)) = applyAdd (eval e) (eval f)
  | eval (ESub (e,f)) = applySub (eval e) (eval f)
  | eval (EMul (e,f)) = applyMul (eval e) (eval f)
  | eval (ENeg e) = applyNeg (eval e)
  | eval (EVec v) = VVec v
  | eval (EMat m) = VMat m 
  | eval (ERat r) = VRat r
  | eval (EDiv (e,f)) = applyDiv (eval e) (eval f)
