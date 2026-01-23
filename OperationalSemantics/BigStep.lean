import OperationalSemantics.Basic

namespace WHILE

inductive BigStep : (Program × State) → State → Prop where
  | skip {s : State} : BigStep (⟪ skip ⟫, s) s
  | assignment {s : State} {v : Var} {e : Expr}
    (he : ∃ w : Value, Option.some w = ⟦ e; s ⟧)
    : BigStep ((Program.assignment v e), s)
    (fun x => if x = v then Exists.choose e' else s x)
  | seq {s t u : State} {p₀ p₁ : Program}
    (hp₀ : BigStep (p₀, s) t)
    (hp₁ : BigStep (p₁, t) u)
    : BigStep ((Program.seq p₀ p₁), s) u
  | cond_if {s t : State} {e : Expr} {pif pelse : Program}
    (hpif : BigStep (pif, s) t)
    (htrue : ⟦ e; s ⟧ = Option.some (Value.bool true))
    : BigStep ((Program.cond e pif pelse), s) t
  | cond_else {s t : State} {e : Expr} {pif pelse : Program}
    (hpif : BigStep (pelse, s) t)
    (hpfalse : ⟦ e; s ⟧ = Option.some (Value.bool false))
    : BigStep ((Program.cond e pif pelse), s) t
  | while_true {s t u : State} {e : Expr} {p : Program}
    (htrue : ⟦ e; s ⟧ = Option.some (Value.bool true))
    (hp : BigStep (p, s) t)
    (hwhile : BigStep ((Program.while e p), t) u)
    : BigStep ((Program.while e p), s) u
  | while_false {s : State} {e : Expr} {p : Program}
    (hfalse : ⟦ e; s ⟧ = Option.some (Value.bool false))
    : BigStep ((Program.while e p), s) s

infixl:60 " ▷ " => BigStep

theorem skip_state_invariant (s : State) : (⟪ skip ⟫, s) ▷ s := by constructor

example : (⟪ skip ⟫, {x ← 2, y ← 2}) ▷ {y ← 2, x ← 2} := by
  apply skip_state_invariant

end WHILE
