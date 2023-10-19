import Mathlib.Data.Real.Basic
import Mathlib.Tactic.IntervalCases
import Library.Theory.Comparison
import Library.Theory.Parity
import Library.Theory.Prime
import Library.Tactic.ModCases
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Use


-- 4(a)
example {P Q : α → Prop} (h : ∀ x, P x ↔ Q x) : (∃ x, P x) ↔ (∃ x, Q x) := by
  constructor
  . intro ha
    obtain ⟨x, hx⟩ := ha
    use x
    have hpqx: P x ↔ Q x := h x
    obtain ⟨hpq, hqp⟩ := hpqx  
    apply hpq hx
  . intro hb
    obtain ⟨x, hx⟩ := hb
    use x
    have hpqx: P x ↔ Q x := h x
    obtain ⟨hpq, hqp⟩ := hpqx  
    apply hqp hx



-- 4(b)
example (P : α → β → Prop) : (∃ x y, P x y) ↔ ∃ y x, P x y := by
  constructor
  . intro ha
    obtain ⟨x, hx⟩ := ha
    obtain ⟨y, hy⟩ := hx 
    use y
    use x
    apply hy
  . intro hb
    obtain ⟨x, hx⟩ := hb
    obtain ⟨y, hy⟩ := hx 
    use y
    use x
    apply hy


-- 4(c)
example (P : α → β → Prop) : (∀ x y, P x y) ↔ ∀ y x, P x y := by
  constructor
  . intro ha
    have hb: ∀ y x, P x y
    · intro y x
      apply ha
    apply hb
  . intro hb
    have ha: ∀ x y, P x y
    · intro x y
      apply hb
    apply ha


-- 4(d)
example (P : α → Prop) (Q : Prop) : ((∃ x, P x) ∧ Q) ↔ ∃ x, (P x ∧ Q) := by
  constructor
  . intro ha
    obtain ⟨hx, hq⟩ := ha
    obtain ⟨x, hx'⟩ := hx 
    use x
    apply And.intro hx' hq
  . intro ha
    obtain ⟨x, hxq⟩ := ha
    obtain ⟨hx, hq⟩ := hxq 
    constructor
    . use x
      apply hx
    . apply hq


-- the below are taken from the MOP 
def Tribalanced (x : ℝ) : Prop := ∀ n : ℕ, (1 + x / n)^n < 3
def Superpowered (k : ℕ) : Prop := ∀ n : ℕ, Prime (k^k^n + 1)

theorem superpowered_one : Superpowered 1 := by
  intro n
  conv => ring_nf -- simplifies goal from `Prime (1 ^ 1 ^ n + 1)` to `Prime 2`
  apply prime_two

-- 5(a)
example : ∃ x : ℝ, Tribalanced x ∧ ¬ Tribalanced (x + 1) := by
  by_cases h: Tribalanced 1
  . use 1
    constructor
    . apply h
    . ring
      intro ha
      simp [Tribalanced] at h
      have hb:= ha 2
      simp at hb
      have : 4 < 3 := by 
      {
        calc
          4 = (1 + 1) ^ 2 := by ring
          _ < 3 := by addarith[hb]
      }
      contradiction
  . use 0
    constructor
    . intro n
      simp
      numbers
    . ring; apply h


-- 5(b)
example : ∃ k : ℕ, Superpowered k ∧ ¬ Superpowered (k + 1) := by
  use 1
  constructor
  . apply superpowered_one
  . intro h
    simp [Superpowered] at h
    have h_4294967297_p : Prime ((1+1) ^ (1+1) ^ 5 + 1) := h 5 -- this is 4294967297
    conv at h_4294967297_p => numbers
    have h_4294967297_n_pr : ¬ Prime 4294967297
    · apply not_prime 641 6700417
      · numbers -- 641 not eq 1
      · numbers --  641 not eq 4294967297
      · ring 
    contradiction
