import Lean

open Lean

/-! ## 1
Create expression `1 + 2` with `Expr.app`.
-/

/-- expression of `Nat.zero` -/
def z := Expr.const ``Nat.zero []

/-- expression of `n : Nat` -/
def natExpr : Nat → Expr
| 0 => z
| n + 1 => .app (.const ``Nat.succ []) (natExpr n)

/-- `sumExpr a b` is an expression of `a + b`. -/
def sumExpr : Nat → Nat → Expr
| n, m => mkAppN (.const ``Nat.add []) #[natExpr n, natExpr m]

def oneAddTwo := sumExpr 1 2

#eval oneAddTwo

elab "oneAddTwo" : term => return oneAddTwo

#check oneAddTwo

/- ## 2
Create expression `1 + 2` with `Lean.mkAppN`.
-/

#eval oneAddTwo

/- ## 3
Create expression `fun x => 1 + x`.
-/

/-- expression of `Nat : Type`-/
def nat : Expr := .const ``Nat []

def oneAdd : Expr :=
  .lam `x nat
    (mkAppN (.const ``Nat.add []) #[mkNatLit 1, .bvar 0])
    BinderInfo.default

elab "oneAdd" : term => return oneAdd

#check oneAdd

/- ## 4
Create expression `fun a, fun b, fun c, (b * a) + c`.
-/

def mulAdd : Expr :=
  .lam `a nat (
      .lam `b nat (
        .lam `c nat (
          mkAppN (.const ``Nat.add []) #[
            mkAppN (.const ``Nat.mul []) #[.bvar 1, .bvar 2],
            .bvar 0
          ]
        )
        BinderInfo.default
      )
      BinderInfo.default
    )
    BinderInfo.default

elab "mulAdd" : term => return mulAdd

#check mulAdd

/- ## 5
Create expression `fun x y => x + y`.
-/

def add : Expr :=
  .lam `x nat (
    .lam `y nat (
      mkAppN (.const ``Nat.add []) #[.bvar 1, .bvar 0]
    )
    BinderInfo.default
  )
  BinderInfo.default

elab "add" : term => return add

#check add

/- ## 6
Create expression `fun x, String.append "hello, " x`.
-/

/-- expression of `String : Type` -/
def string : Expr := .const ``String []

def hello : Expr :=
  .lam `x string (
    mkAppN (.const ``String.append []) #[
      mkStrLit "hello, ",
      .bvar 0
    ]
  )
  BinderInfo.default

elab "hello" : term => return hello

#check hello

/- ## 7
Create expression `∀ x : Prop, x ∧ x`.
-/

def prop : Expr := .sort Level.zero

def seven : Expr :=
  .forallE
    `x prop
    (mkAppN (.const ``And []) #[.bvar 0, .bvar 0])
    BinderInfo.default

elab "seven" : term => return seven
#check seven

/- ## 8
Create expression `Nat → String`.
-/

def eight : Expr :=
  .forallE
    `x nat
    string
    BinderInfo.default

elab "eight" : term => return eight
#check eight

/- ## 9
Create expression `fun (p : Prop) => (λ hP : p => hP)`.
-/

def nine : Expr :=
  .lam `p prop (
    .lam
      `hP (.bvar 0) (.bvar 0)
      BinderInfo.default
  )
  BinderInfo.default

elab "nine" : term => return nine
#check nine

/- ## 10
Create expression `Type 6`.
-/

def ten : Expr := .sort (7 : Level)

#synth ∀ n, OfNat Level n

elab "ten" : term => return ten
#check ten
