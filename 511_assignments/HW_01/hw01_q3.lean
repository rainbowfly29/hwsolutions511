import Mathlib.Data.Real.Basic
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel


example (P Q R : Prop) (h : P ∧ (Q → R)) : P → (Q → R) :=
begin
  intro h1,
  have h2 : Q → R := h.right,
  intro h3,
  exact h2 h3,
end

example (P Q R : Prop) (h : P → (Q → R)) : (P → Q) → (P → R) :=
begin
  intro h1,
  intro h2,
  have h3 := h1 h2,
  have h4 := h h2,
  exact h4 h3,
end

example (P Q R : Prop) (h : P → (Q → R)) : (P → Q) → (P → R) :=
begin
  intro h1,
  intro h2,
  have h3 := h1 h2,
  have h4 := h h2,
  exact h4 h3,
end