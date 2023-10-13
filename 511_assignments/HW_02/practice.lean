

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
import Mathlib.Data.Real.Basic



attribute [-instance] Int.instDivInt_1 Int.instDivInt EuclideanDomain.instDiv Nat.instDivNat


  

--5(a)
example {a b : ℝ} (h : ∀ x, x ≥ a ∨ x ≤ b) : a ≤ b := by
  have h1 : (a+b)/2 ≥ a ∨ (a+b)/2 ≤ b := by apply h
  obtain ha | hb := h1
  . calc
      b = 2 * ((a + b) / 2) - a := by ring
      _ ≥ 2 * a - a := by rel [ha]
      _ = a := by ring
  . calc
      a = 2 * ((a + b) / 2) - b := by ring
      _ ≤ 2 * b - b := by rel [hb]
      _ = b := by ring  




-- 5(b)
example : ∃ c : ℝ, ∀ x y, x ^ 2 + y ^ 2 ≤ 4 → x + y ≥ c := by
  use -3
  intro x y h
  have hp : -3 ≤ (x+y) ∧ (x+y) ≤ 3
  · apply abs_le_of_sq_le_sq'
    calc 
      (x + y)^2 ≤ (x + y)^2 + (x - y)^2 := by extra
      _ = 2 * (x^2 + y^2) := by ring
      _ ≤ 2 * 4 := by rel[h]
      _ ≤  3 ^ 2 := by numbers
    numbers
  addarith[hp]


-- 5(c)
example {n : ℤ} (hn : ∀ m, 1 ≤ m → m ≤ 5 → m ∣ n) : 15 ∣ n := by
  have h1 := hn 3
  simp at h1 
  have h2 := hn 5
  simp at h2
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  use -3 * b + 2 * a
  calc 
    n = -9 * n  + 10 * n := by ring
    _ = -9 * (5 * b) + 10 * n := by rw[hb]
    _ = 15 * (-3 * b) + 10 * n := by ring
    _ = 15 * (-3 * b) + 10 * (3 * a) := by rw[ha]
    _ = 15 * (-3 * b) + 15 * (2 * a) := by ring
    _ = 15 * (-3 * b + 2 * a) := by ring

notation3 (prettyPrint := false) "forall_sufficiently_large "(...)", "r:(scoped P => ∃ C, ∀ x ≥ C, P x) => r
--5(d)
example : forall_sufficiently_large x : ℝ, x ^ 3 + 3 * x ≥ 7 * x ^ 2 + 12 := by
  dsimp
  use 10
  intro n h1
  calc
    n ^ 3 + 3 * n = n * (n^2 + 3) := by ring
    _ ≥ 10 * (n^2 + 3) := by rel[h1]
    _ = 10*n^2 + 30 := by ring
    _ = 7*n ^ 2 + 3 * n^2 + 30 := by ring
    _ ≥  7*n ^ 2 + 3*10^2 + 30 := by rel[h1]
    _ =  7*n ^2 + 12 + 318 := by ring
    _ ≥  7*n ^2 + 12 := by extra


--6a

example {x : ℝ} : x ^ 2 + x - 6 = 0 ↔ x = -3 ∨ x = 2 := by
  constructor
  . intro h
    have h1: (x + 3) * (x - 2) = 0 := by
      calc
        (x + 3) * (x - 2) = x^2 + x - 6 := by ring
        _ = 0 := by rw[h]
    have hab := eq_zero_or_eq_zero_of_mul_eq_zero h1
    obtain ha | hb := hab
    left
    . calc
        x = (x + 3) - 3 := by ring
        _ = 0 - 3 := by rw[ha]
        _ = -3 := by numbers
    right
    . calc
        x = (x - 2) + 2 := by ring
        _ = 0 + 2 := by rw[hb]
        _ = 2 := by numbers
  . intro h
    obtain ha | hb := h
    . calc
        x^2 + x - 6 = (x + 3) * (x - 2) := by ring
        _ = (-3 + 3) * (x - 2) := by rw[ha]
        _ = 0 := by ring
    . calc 
        x^2 + x - 6 = (x - 2) * (x + 3) := by ring
        _ = (2 - 2) * (x + 3) := by rw[hb]
        _ = 0 := by ring

-- 6b
example {a : ℤ} : a^2 - 5*a + 5 ≤ -1 ↔ a = 2 ∨ a = 3 := by
  constructor
  . intro h
    have h1 := calc 
      (2*a-5)^2 = 4*(a ^ 2 - 5 * a + 5) + 5 := by ring
      _ ≤ 4 * -1 + 5 := by rel[h]
      _ = 1^2 := by ring
    have h2 : (0:ℤ) ≤1 := by numbers
    obtain ⟨h3, h4⟩ := abs_le_of_sq_le_sq' h1 h2
    have h3 : 2*2 ≤ 2*a := by addarith[h3]
    cancel 2 at h3
    have h4 : 2*a ≤ 2*3 := by addarith[h4]
    cancel 2 at h4
    interval_cases a
    · left; numbers
    · right; numbers
  . intro h
    obtain ha | hb := h
    . rw [ha]
      numbers
    . rw [hb]
      numbers