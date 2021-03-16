// T-501-FMAL, Spring 2021, Assignment 3

// Test cases for Problem 4
let n = ref (NoLink "'n", 0)
let o = ref (NoLink "'o", 0)
let unifyTest t1 t2 =
  n := (NoLink "'n", 0);
  o := (NoLink "'o", 0);
  unify t1 t2;
  showType t1
// > unifyTest Float Float;;
// val it : string = "Float"
// > unifyTest Float (Vector (LNum 2));;
// System.Exception: cannot unify Float and Vector(2)
// > unifyTest Float (Vector (LVar n));;
// System.Exception: cannot unify Float and Vector('n)
// > unifyTest (Vector (LVar n)) (Vector (LNum 5));;
// val it : string = "Vector(5)"
// > unifyTest (Vector (LVar n)) (Vector (LVar o));;
// val it : string = "Vector('n)"
// > unifyTest (Vector (LVar n)) (Vector (LVar n));;
// val it : string = "Vector('n)"
// > unifyTest (Fun (LVar n, Vector (LVar n))) (Fun (LVar o, Vector (LVar o)));;
// val it : string = "Vector('n) -> Vector('n)"
// > unifyTest (Fun (LVar n, Vector (LVar o))) (Fun (LVar o, Vector (LVar n)));;
// val it : string = "Vector('n) -> Vector('n)"
// > unifyTest (Fun (LVar n, Vector (LVar o))) (Fun (LNum 4, Vector (LVar n)));;
// val it : string = "Vector(4) -> Vector(4)"
// > unifyTest (Fun (LVar n, Vector (LNum 7))) (Fun (LNum 4, Vector (LNum 8)));;
// System.Exception: lengths 7 and 8 differ
// > unifyTest (Vector (LNum 7)) (Fun (LVar n, Vector (LVar o)));;
// System.Exception: cannot unify Vector(7) and Vector('n) -> Vector('o)
// > unifyTest (Fun (LNum 7, Float)) (Fun (LVar n, Vector (LVar o)));;
// System.Exception: cannot unify Float and Vector('o)

// Test cases for Problem 5

// > inferTop (Plus (NumF 2., NumF 3.));;
// val it : string = "Float"
// > inferTop (Plus (Vect [2.;3.], Vect [3.;4.]));;
// val it : string = "Vector(2)"
// > inferTop (Plus (NumF 2., Vect [1.]));;
// System.Exception: cannot unify Float and Vector(1)
// > inferTop (Plus (Vect [1.; 2.], Vect [3.; 4.; 5.]));;
// System.Exception: lengths 2 and 3 differ
// > inferTop (Scale (NumF 1., Vect [2.;3.]));;
// val it : string = "Vector(2)"
// > inferTop (Scale (Vect [1.], Vect [2.;3.]));;
// System.Exception: expected a float
// > inferTop (IfPositive (NumF 1., Vect [2.;3.], NumF 3.));;
// System.Exception: cannot unify Vector(2) and Float
// > inferTop (Average (Vect [2.;3.]));;
// val it : string = "Float"
// > inferTop (Average (NumF 2.));;
// System.Exception: expected a vector
// > inferTop (LetFun ("f", "x", Var "x", Var "f"));;
// val it : string = "Vector('o) -> Vector('o)"
// > inferTop (LetFun ("f", "x", LetFun ("g", "y", Plus (Var "x", Var "y"), Var "g"), Var "f"));;
// val it : string = "Vector('p) -> Vector('p) -> Vector('p)"
// > inferTop (LetFun ("f", "x", Plus (Var "x", Vect [4.; 5.]), Var "f"));;
// val it : string = "Vector(2) -> Vector(2)"
// > inferTop (LetFun ("f", "x", LetFun ("g", "y", Average (Plus (Var "x", Var "y")), Var "g"), Var "f"));;
// val it : string = "Vector('p) -> Vector('p) -> Float"
let neg = LetFun ("neg", "x", Scale (NumF -1.0, Var "x"), Var "neg");;
let zero = LetFun ("zero", "x", Plus (Var "x", Call (neg, Var "x")), Var "zero");;
let abs = LetFun ("abs", "x", IfPositive (Average (Var "x"), Var "x", Call (neg, Var "x")), Var "abs");;
// > inferTop neg;;
// val it : string = "Vector('o) -> Vector('o)"
// > inferTop zero;;
// val it : string = "Vector('q) -> Vector('q)"
// > inferTop abs;;
// val it : string = "Vector('q) -> Vector('q)"

