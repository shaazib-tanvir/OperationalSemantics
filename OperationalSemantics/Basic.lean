import Lean
import Lean.Meta
import Std

namespace WHILE

def BoolLit := Bool
deriving Repr
def NatLit := Nat
deriving Repr

inductive Literal where
  | bool : BoolLit → Literal
  | nat : NatLit → Literal
deriving Repr

structure Var where
  ident : String
deriving Repr, DecidableEq

inductive UnaryOp where
  | not : UnaryOp
deriving Repr

inductive BinaryOp where
  | add : BinaryOp
  | sub : BinaryOp
  | and : BinaryOp
  | or : BinaryOp
  | gt : BinaryOp
deriving Repr

inductive Expr where
  | lit : Literal → Expr
  | var : Var → Expr
  | unary : UnaryOp → Expr → Expr
  | binary : BinaryOp → Expr → Expr → Expr
deriving Repr

inductive Program where
  | skip : Program
  | assignment : Var → Expr → Program
  | seq : Program → Program → Program
  | cond : Expr → Program → Program → Program
  | while : Expr → Program → Program
deriving Repr

declare_syntax_cat while_lit

syntax "T" : while_lit
syntax "⊥" : while_lit
syntax num : while_lit

open Lean Lean.Meta in
def elabLit (stx : Syntax) : MetaM Lean.Expr := do
  match stx with
  | `(while_lit| T) =>
    return mkAppN (.const ``Literal.bool []) #[.const ``true []]
  | `(while_lit| ⊥) =>
    return mkAppN (.const ``Literal.bool []) #[.const ``false []]
  | `(while_lit| $n:num) =>
    return mkAppN (.const ``Literal.nat []) #[mkNatLit n.getNat]
  | _ => return ← Lean.Elab.throwUnsupportedSyntax

elab "test_while_lit" x:while_lit : term => elabLit x

declare_syntax_cat while_unary

syntax "¬" : while_unary

open Lean Lean.Meta in
def elabUnary (stx : Syntax) : MetaM Lean.Expr := do
  match stx with
  | `(while_unary| ¬) =>
    return .const ``UnaryOp.not []
  | _ => return ← Lean.Elab.throwUnsupportedSyntax

elab "test_while_un" x:while_unary : term => elabUnary x

declare_syntax_cat while_binary

syntax " + " : while_binary
syntax " - " : while_binary
syntax " ∨ " : while_binary
syntax " ∧ " : while_binary
syntax " > " : while_binary

open Lean Lean.Meta in
def elabBinary (stx : Syntax) : MetaM Lean.Expr := do
  match stx with
  | `(while_binary| +) => return .const ``BinaryOp.add []
  | `(while_binary| -) => return .const ``BinaryOp.sub []
  | `(while_binary| ∧) => return .const ``BinaryOp.and []
  | `(while_binary| ∨) => return .const ``BinaryOp.or []
  | `(while_binary| >) => return .const ``BinaryOp.gt []
  | _ => return ← Lean.Elab.throwUnsupportedSyntax

elab "test_while_bin" x:while_binary : term => elabBinary x

declare_syntax_cat while_expr

syntax while_lit : while_expr
syntax ident : while_expr
syntax while_unary while_expr : while_expr
syntax while_expr while_binary while_expr : while_expr
syntax "(" while_expr ")" : while_expr

open Lean Lean.Meta in
def identToVar (name : Lean.TSyntax `ident) : Lean.Expr := mkAppN (.const ``Var.mk []) #[mkStrLit name.getId.getString!]

open Lean Lean.Meta in
partial def elabExpr (stx : Syntax) : MetaM Lean.Expr := do
  match stx with
  | `(while_expr| $lit:while_lit) =>
    return mkAppN (.const ``Expr.lit []) #[(← elabLit lit)]
  | `(while_expr| $name:ident) =>
    return mkAppN (.const ``Expr.var []) #[identToVar name]
  | `(while_expr| $u:while_unary $e:while_expr) =>
    return mkAppN (.const ``Expr.unary []) #[← elabUnary u, ← elabExpr e]
  | `(while_expr| $e:while_expr $b:while_binary $e':while_expr) =>
    return mkAppN (.const ``Expr.binary []) #[← elabBinary b, ← elabExpr e, ← elabExpr e']
  | `(while_expr| ( $e:while_expr )) =>
    elabExpr e
  | _ => return ← Lean.Elab.throwUnsupportedSyntax

elab "test_while_expr" e:while_expr : term => elabExpr e

#eval test_while_expr a + 2

declare_syntax_cat while_program

syntax "skip" : while_program
syntax ident ":=" while_expr : while_program
syntax while_program ";" while_program : while_program
syntax "if" while_expr "then" while_program "else" while_program : while_program
syntax "while" while_expr "do" while_program : while_program

open Lean Lean.Meta in
partial def elabProgram (stx : Syntax) : MetaM Lean.Expr :=
  match stx with
  | `(while_program| skip) =>
    return .const ``Program.skip []
  | `(while_program| $x:ident := $e:while_expr) =>
    return mkAppN (.const ``Program.assignment []) #[identToVar x, ← elabExpr e]
  | `(while_program| $s:while_program; $s':while_program) =>
    return mkAppN (.const ``Program.seq []) #[← elabProgram s, ← elabProgram s']
  | `(while_program| if $b:while_expr then $s:while_program else $s':while_program) =>
    return mkAppN (.const ``Program.cond []) #[← elabExpr b, ← elabProgram s, ← elabProgram s']
  | `(while_program| while $b:while_expr do $s:while_program) =>
    return mkAppN (.const ``Program.while []) #[← elabExpr b, ← elabProgram s]
  | _ => Lean.Elab.throwUnsupportedSyntax

elab "⟪ " p:while_program " ⟫" : term => elabProgram p

#eval ⟪
if x > 2 then
  x := x + 1;
  y := x
else x := x - 1
⟫

#check ⟪ skip ⟫

inductive Value where
  | bool : Bool → Value
  | nat : Nat → Value
deriving Repr

def State := Var → Value
def SProp := State → Prop

def Literal.eval (l : Literal) : Value :=
  match l with
  | bool b => Value.bool b
  | nat n => Value.nat n

-- typeError currently takes unit but it should probably take info to synthesize the error message
-- i don't care enough for that rn so future me's problem =)
def Unary.applyM [Monad m] (u : UnaryOp) (x : Value) (typeError : Unit → m Value) : m Value := do
  match u, x with
  | .not, .bool b => return Value.bool (!b)
  | _, _ => return ← typeError ()

def Binary.applyM [Monad m] (b : BinaryOp) (x : Value) (y : Value) (typeError : Unit → m Value) : m Value := do
  match b, x, y with
  | .add, .nat u, .nat v => return Value.nat (u + v)
  | .sub, .nat u, .nat v => return Value.nat (u - v)
  | .or, .bool b₀, .bool b₁ => return Value.bool (b₀ || b₁)
  | .and, .bool b₀, .bool b₁ => return Value.bool (b₀ && b₁)
  | _, _, _ => return ← typeError ()

def Expr.evalM [Monad m] (e : Expr) (s : State) (typeError : Unit → m Value) : m Value := do
  match e with
  | lit l => return l.eval
  | var v => return s v
  | unary u e => return ← Unary.applyM u (← Expr.evalM e s typeError) typeError
  | binary b e₀ e₁ =>
    return ← Binary.applyM b (← Expr.evalM e₀ s typeError) (← Expr.evalM e₁ s typeError) typeError

def Expr.eval? (e : Expr) (s : State) : Option Value :=
  Expr.evalM e s (fun _ => none)

syntax (name := evalExpr) "⟦" term ";" term "⟧" : term

macro_rules
  | `(⟦$e:term ; $s:term⟧) => `(Expr.eval? $e $s)

declare_syntax_cat state_decl
syntax ident " ← " while_lit : state_decl

syntax (name := state_expr) "{" state_decl,* "}" : term

def evalStateExpr (litList : List (String × Literal)) : State :=
  fun v => match (litList.find? (fun x => x.fst = v.ident)) with
  | .none => Value.nat 0
  | .some y => y.snd.eval

open Lean Lean.Meta in
def elabStateExpr (stx : Syntax) : MetaM Lean.Expr := do
  match stx with
  | `(state_expr| { $sdecs:state_decl,* }) =>
    let mut litList := []
    for stx in sdecs.getElems do
      match stx with
        | `(state_decl| $x:ident ← $l:while_lit) =>
          litList := litList.insert (← mkAppM ``Prod.mk #[mkStrLit x.getId.toString, (← elabLit l)])
        | _ => continue

    let prodType := (← mkAppM ``Prod #[.const ``String [], .const ``Literal []])
    let exprList := ← mkListLit prodType litList
    return ← mkAppM ``evalStateExpr #[exprList]
  | _ => return ← Lean.Elab.throwUnsupportedSyntax

open Lean in
@[app_unexpander evalStateExpr]
def unexpandEvalStateExpr : PrettyPrinter.Unexpander
  | `($_ [$[($x:str, $y:term)],*]) => do
    let x := x.reverse.map fun str => Lean.mkIdent (.mkStr1 str.getString)
    let y ← y.reverse.mapM fun term => do
      match term with
      | `(Literal.nat $n:num) => return ← `(while_lit| $n:num)
      | `(Literal.bool true) => return ← `(while_lit| T)
      | `(Literal.bool false) => return ← `(while_lit| ⊥)
      | _ => throw ()

    `({$[$x:ident ← $y:while_lit],*})
  | _ => throw ()

#eval test_while_lit T
elab s:state_expr : term => elabStateExpr s
#check ({x ← 2, y ← T})

end WHILE
