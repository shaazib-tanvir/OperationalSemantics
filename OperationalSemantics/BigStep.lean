import OperationalSemantics.Basic

namespace WHILELang

inductive BigStep : (Program × State) → State → Prop where
  | skip {s : State} : BigStep (⟪ skip ⟫, s) s
  | assignment {s : State} (v : Var) (e : Expr)
    (he : ∃ w : Value, Option.some w = ⟦ e; s ⟧)
    : BigStep ((Program.assignment v e), s) (s.sub v (Exists.choose he))
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
    (hwhile : BigStep ((Program.while_do e p), t) u)
    : BigStep ((Program.while_do e p), s) u
  | while_false {s : State} {e : Expr} {p : Program}
    (hfalse : ⟦ e; s ⟧ = Option.some (Value.bool false))
    : BigStep ((Program.while_do e p), s) s

infixl:60 " ▷ " => BigStep

theorem skip_state_invariant (s : State) : (⟪ skip ⟫, s) ▷ s := by
  exact @BigStep.skip s

@[grind =]
theorem big_step_skip_iff (s t : State) : (⟪ skip ⟫, s) ▷ t ↔ s = t := by
  constructor
  · intro h
    cases h; rfl
  · intro h
    rw [h]
    apply skip_state_invariant

@[grind =]
theorem big_step_assignment_iff (s t : State) (v : Var) (e : Expr) : (Program.assignment v e, s) ▷ t ↔ ∃ w : Value, ⟦ e; s ⟧ = Option.some w ∧ t = s.sub v w := by
  constructor
  · intro h
    cases h with | assignment x e he
    obtain ⟨ w, he ⟩ := he
    grind only [Exists.choose_spec]
  · rintro ⟨ w, heval, ht ⟩
    rw [ht]
    have hexists : ∃ w' : Value, some w' = e.eval? s := by
      exists w
      simp [*]
    have h : hexists.choose = w := by
      grind only [Exists.choose_spec]
    rw [←h]
    apply @BigStep.assignment s v e hexists

@[grind =]
theorem big_step_seq_iff (s t : State) (p₀ p₁ : Program) : (Program.seq p₀ p₁, s) ▷ t ↔ ∃ u : State, (p₀, s) ▷ u ∧ (p₁, u) ▷ t := by
  constructor
  · intro h
    cases h with | @seq _ u _ d e f g
    exists u
  · rintro ⟨ u, ⟨ h₀, h₁ ⟩ ⟩
    exact BigStep.seq h₀ h₁

@[grind =]
theorem big_step_cond_iff
  (s t : State) (e : Expr) (pif pelse : Program)
  : (Program.cond e pif pelse, s) ▷ t ↔
  (.some (Value.bool true) = ⟦ e; s ⟧ ∧ (pif, s) ▷ t) ∨
  (.some (Value.bool false) = ⟦ e; s ⟧ ∧ (pelse, s) ▷ t) := by
    constructor
    · intro h
      cases h with
      | cond_if hpif htrue =>
        left
        grind
      | cond_else hpelse hfalse =>
        right
        grind
    · intro h
      rcases h with h | h
      · grind [BigStep.cond_if]
      · grind [BigStep.cond_else]

@[grind =]
theorem big_step_while_iff
  (s t : State) (e : Expr) (p : Program)
  : (Program.while_do e p, s) ▷ t ↔
  (.some (Value.bool true) = ⟦ e; s ⟧ ∧ ∃ u : State, (p, s) ▷ u ∧ (Program.while_do e p, u) ▷ t) ∨
  (.some (Value.bool false) = ⟦ e; s ⟧ ∧ s = t) := by
    constructor
    · intro h
      cases h with
      | @while_true _ u _ _ _ htrue hp hwhile => grind
      | @while_false s _ _ hfalse => grind
    · intro h
      rcases h with h | h
      · grind [BigStep.while_true]
      · grind [BigStep.while_false]

theorem big_step_while_iff'
  (s t : State) (e : Expr) (p : Program)
  : (Program.while_do e p, s) ▷ t ↔
  ∃ states : List State, states[0]? = s ∧ states[states.length - 1]? = t ∧
  ⟦ e; t ⟧ = .some (Value.bool false) ∧
  (∀ i : Fin (states.length - 1), (p, states[i]) ▷ states[(i : Nat) + 1] ∧ ⟦ e; states[i] ⟧ = .some (Value.bool true)) := by
    constructor
    · sorry
    · rintro ⟨ states, ⟨ h0, hn, hfalse, htrue ⟩ ⟩
      revert s
      induction states with
      | nil => grind
      | cons head states states_ih =>
        intro s h0
        simp only [Fin.getElem_fin, List.length_cons, Nat.zero_lt_succ, getElem?_pos,
          List.getElem_cons_zero, Option.some.injEq, Nat.add_one_sub_one, Nat.lt_add_one,
          List.getElem_cons_succ] at *
        simp [h0] at *; clear h0
        match states with
        | [] => grind
        | head' :: states =>
          have hn' : (head' :: states)[(head' :: states).length - 1]? = some t := by
            grind
          specialize states_ih hn'
          have htrue' : ∀ (i : Fin ((head' :: states).length - 1)), (p, (head' :: states)[↑i]) ▷ (head' :: states)[↑i + 1] ∧ e.eval? (head' :: states)[↑i] = some (Value.bool true) := by
            intro i
            specialize htrue ⟨ i + 1, by grind ⟩
            grind
          specialize states_ih htrue'
          simp at states_ih
          apply BigStep.while_true
          · specialize htrue ⟨ 0, by grind ⟩
            grind
          · specialize htrue ⟨ 0, by grind ⟩
            obtain ⟨ htrue, - ⟩ := htrue
            simp at htrue
            exact htrue
          · exact states_ih

theorem big_step_deterministic (p : Program) (s t u : State) (hstep : (p, s) ▷ t ∧ (p, s) ▷ u) : t = u := by
  obtain ⟨ step₀, step₁ ⟩ := hstep
  revert s t u
  induction p with
  | «skip» =>
    grind
  | assignment v e =>
    grind
  | seq p₀ p₁ hp₀ hp₁ =>
    intro s t u hp0 hp1
    cases hp0 with | @seq _ v _ _ _ h0 h1
    cases hp1 with | @seq _ v' _ _ _ h0' h1'
    specialize hp₀ s v v'
    specialize hp₁ v t u
    grind
  | cond e pif pelse hif helse =>
    grind
  | while_do e p hp =>
    sorry

end WHILELang
