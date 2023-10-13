import Mathlib.Data.Real.Basic
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel
lemma de_morgan_2 {p q : Prop} : (¬p ∧ ¬q) → ¬(p ∨ q) := by
  intro h
  obtain ⟨h_not_p ,h_not_q⟩ : (¬p ∧ ¬q) := h 
  intro h_or,
  cases h_or with h_p h_q,
  { exact h_not_p h_p },  -- contradiction for p
  { exact h_not_q h_q }   -- contradiction for q


lemma de_morgan_4 {p q : Prop} : ¬(p∧q) → (¬p∨¬q) := by
                              -- obtained by closing box [1-13]
intro h
have h1 : p → (¬p∨¬q) := by
{ intro h p
show ¬p∨¬q ;
have h not q : ¬q := by { intro h q
-- obtained by closing box [2-7]
-- obtained by closing box [3-5]
show False ; apply h (And.intro h p h q) } ; apply Or.intro right (¬p) h not q }
have h2 : ¬p → (¬p∨¬q) := by -- obtained by closing box [9-10] { intro h not p
show ¬p∨¬q ; apply Or.intro left (¬q) h not p } apply Or.elim (Classical.em p) h1 h2




