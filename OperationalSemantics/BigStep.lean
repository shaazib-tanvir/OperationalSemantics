import OperationalSemantics.Basic

namespace WHILE

inductive BigStep : (Program × State) → State → Prop where
  | skip {s : State} : BigStep (⟪ skip ⟫, s) s
  | assignment {s : State} {v : Var} {e : Expr}
    (he : ∃ e' : Value, Option.some e' = e.eval? s)
    : BigStep ((Program.assignment v e), s)
    (fun x => if x = v then Exists.choose e' else s x)
  | seq {s t u : State} {p₀ p₁ : Program}
    (hp₀ : BigStep (p₀, s) t)
    (hp₁ : BigStep (p₁, t) u)
    : BigStep ((Program.seq p₀ p₁), s) u
  | cond_if {s t : State} {e : Expr} {pif pelse : Program}
    (hpif : BigStep (pif, s) t)
    (htrue : e.eval? s = Option.some (Value.bool true))
    : BigStep ((Program.cond e pif pelse), s) t
  | cond_else {s t : State} {e : Expr} {pif pelse : Program}
    (hpif : BigStep (pelse, s) t)
    (hpfalse : e.eval? s = Option.some (Value.bool false))
    : BigStep ((Program.cond e pif pelse), s) t
  | while_true {s t u : State} {e : Expr} {p : Program}
    (htrue : e.eval? s = Option.some (Value.bool true))
    (hp : BigStep (p, s) t)
    (hwhile : BigStep ((Program.while e p), t) u)
    : BigStep ((Program.while e p), s) u
  | while_false {s : State} {e : Expr} {p : Program}
    (hfalse : e.eval? s = Option.some (Value.bool false))
    : BigStep ((Program.while e p), s) s

end WHILE
