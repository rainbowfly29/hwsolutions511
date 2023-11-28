import Mathlib.Data.Real.Basic
import Mathlib.Tactic.IntervalCases
import Library.Theory.Comparison
import Library.Theory.Parity
import Library.Theory.Prime
import Library.Tactic.Rel
import Library.Tactic.ModCases
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Use
import Library.Theory.ParityModular
import Mathlib.Tactic.Set
import Library.Tactic.ExistsDelaborator
import Library.Tactic.FiniteInductive
import Library.Tactic.Induction
import Mathlib.Tactic.GCongr

set_option push_neg.use_distrib true
open Function

/- 2 points -/
theorem problem4a : ¬ ∀ (f : ℤ → ℤ), Surjective f → Surjective (fun x ↦ 2 * f x) := by
  dsimp [Surjective]
  push_neg
  use fun x ↦ x
  constructor
  · intro a
    use a
    ring
  · use 1
    intro x
    simp
    obtain hzero | hone := le_or_succ_le x 0
    · apply ne_of_lt --x <= 0
      calc
        2 * x ≤ 2 * 0 := by rel[hzero]
        _ = 0 := by ring
        _ < 1 := by extra
    · apply ne_of_gt --x >= 1
      calc
        2 * x ≥ 2 * 1 := by rel[hone]
        _ = 1 + 1 := by ring
        _ > 1 := by extra

/- 2 points -/
theorem problem4b : ¬ ∀ c : ℝ, Surjective (fun x ↦ c * x) := by
  dsimp[Surjective]
  push_neg
  use 0, 1
  intro x
  ring
  numbers

/- 3 points -/
theorem problem4c {f : ℚ → ℚ} (hf : ∀ x y, x < y → f x < f y) : Injective f := by
  dsimp [Injective]
  intro a b h
  obtain hl | hab | hg := lt_trichotomy a b
  . have hx := ne_of_lt (hf a b hl)
    contradiction
  . apply hab
  . have hx := ne_of_gt (hf b a hg)
    contradiction

/- 3 points -/
theorem problem4d {f : X → ℕ} {x0 : X} (h0 : f x0 = 0) {i : X → X}
    (hi : ∀ x, f (i x) = f x + 1) : Surjective f := by
  dsimp[Surjective]
  intro a
  simple_induction a with x hx
  . use x0
    apply h0
  . obtain ⟨a, hx⟩ := hx
    use i a
    rw [hi, hx]

/- 2 points -/
theorem problem5a : Bijective (fun (x : ℝ) ↦ 4 - 3 * x) := by
  dsimp[Bijective]
  constructor
  · dsimp[Injective]
    intro a b h
    calc
      a = ((4 - 3 * a) - 4) / (-3) := by ring
      _ = ((4 - 3 * b) - 4) / (-3) := by rw[h]
      _ = b := by ring
  · dsimp[Surjective]
    intro y
    use (4 - y) / 3
    ring

/- 2 points -/
theorem problem5b : ¬ Bijective (fun (x : ℝ) ↦ x ^ 2 + 2 * x) := by
  by_cases ha : Bijective (fun (x : ℝ) ↦ x ^ 2 + 2 * x)
  · dsimp[Bijective] at ha
    obtain ⟨ha, hb⟩ := ha
    dsimp[Injective] at ha
    have hc : ¬ ∀ {x1 x2 : ℝ}, x1 ^ 2 + 2 * x1 = x2 ^ 2 + 2 * x2 → x1 = x2 := by
      push_neg
      use -2
      use 0
      constructor
      · ring
      · numbers
    contradiction
  · apply ha

def Inverse (f : X → Y) (g : Y → X) : Prop := g ∘ f = id ∧ f ∘ g = id

def u (x : ℝ) : ℝ := 5 * x + 1

noncomputable def v (x : ℝ) : ℝ := (x - 1) / 5

/- 3 points -/
theorem problem5c : Inverse u v := by
  dsimp[Inverse]
  dsimp [(.∘.)] at *
  dsimp[id]
  constructor
  · ext x
    calc
      v (u x) = ((u x) - 1) / 5 := by rw[v]
      _ = ((5 * x + 1) - 1) / 5 := by rw[u]
      _ = x := by ring
  · ext x
    rw[u, v]
    ring

/- 3 points -/
theorem problem5d {f : X → Y} (hf : Injective f) {g : Y → Z} (hg : Injective g) :
    Injective (g ∘ f) := by
  dsimp[Injective] at *
  intro a b
  intro hab
  apply hf (hg hab)
