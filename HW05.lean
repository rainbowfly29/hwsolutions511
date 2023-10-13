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
    
example {n : ℤ} : 63 ∣ n ↔ 7 ∣ n ∧ 9 ∣ n := by
  dsimp [(· ∣ ·)] at *
  constructor
  . intro h
    obtain ⟨a, ha⟩ := h
    constructor
    . use 9*a
      calc
        n = 63*a := by rw[ha]
        _ = 7* (9*a) := by ring
    . use 7*a
      calc
        n = 63*a := by rw[ha]
        _ = 9* (7*a) := by ring
  . intro h
    obtain ⟨hx, hy⟩ := h
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    use 4*b - 3*a
    calc
      n = 28*n - 27*n := by ring
      _ = 28*(9*b) - 27*n := by rw[hb]
      _ = 28*(9*b) - 27*(7*a) := by rw[ha]
      _ = 63 * (4*b - 3*a) := by ring

-- 4(b)
example {k : ℕ} : (k ^ 2 ≤ 6) ↔ (k = 0 ∨ k = 1 ∨ k = 2) := by
  constructor
  . intro h_k
    have h0 := le_or_gt k 0
    obtain hl | hg := h0
    . left
      simp at hl
      apply hl 
    . right
      have h1 := le_or_gt k 1
      obtain ha | hb := h1
      . left
        have  hx : k>=1 := by addarith [hg]
        apply le_antisymm ha hx
      . right 
        have hy : k>=2 := by addarith [hb]
        have hc: k^2 < 3^2 := 
          calc
            k^2 <= 6 := by rel [h_k]
            _ <= 9 := by ring
            _ = 3^2 := by numbers
        cancel 2 at hc
        addarith [hy, hc]
  . intro hz
    obtain h0 | h12 := hz
    . calc
      k^2 = k*k := by ring
      _ = 0 * k := by rw[h0]
      _ ≤ 0 := by ring
      _ ≤ 6 := by addarith 
    . obtain h1 | h2 := h12
      . calc
        k^2 = k*k := by ring
        _ = 1*1 := by rw[h1]
        _ ≤ 1 := by ring
        _ ≤ 6 := by addarith 
      . calc
        k^2 = k*k := by ring
        _ = 2*2 := by rw[h2]
        _ ≤ 4 := by ring
        _ ≤ 6 := by addarith 

-- 5(a)

-- 5(b) 
example : ∃! x : ℚ, 4 * x - 3 = 9 := by
  use 3
  dsimp
  constructor
  . numbers
  . intro y h
    calc
      y = ((4*y-3) +3)/4 := by ring
      _ = (9 + 3)/4 := by rw [h]
      _ = 3 := by numbers

-- 5(c)
example : ∃! n : ℕ, ∀ a, n ≤ a := by
  use 0
  dsimp
  constructor
  . intro a
    addarith
  intro x hx
  have hx' : x ≤ 0 := hx 0
  addarith[hx']

-- 6(a)

example {p : ℕ} (hp : 2 ≤ p) (H : ∀ m : ℕ, 1 < m → m < p → ¬m ∣ p) : Prime p := by
  constructor
  · apply hp -- show that `2 ≤ p`
  intro m hx
  have hp' : 0 < p := by extra
  have h1m : 1 ≤ m := Nat.pos_of_dvd_of_pos hx hp'
  obtain hm | hm_left : 1 = m ∨ 1 < m := eq_or_lt_of_le h1m
  · -- the case `m = 1`
    left
    addarith [hm]
  -- the case `1 < m`
  . right
    have hy: m≤p := by apply Nat.le_of_dvd hp' hx
    obtain h1 | h2 : m = p ∨ m < p := eq_or_lt_of_le hy
    apply h1
    have h_contra := by apply H m hm_left h2 hx
    contradiction


-- 6(b)

--6(c)

example {x y : ℝ} (n : ℕ) (hx : 0 ≤ x) (hn : 0 < n) (h : y ^ n ≤ x ^ n) :
    y ≤ x := by
  cancel n at h

--6(d)

example (p : ℕ) (h : Prime p) : p = 2 ∨ Odd p := by
  obtain ⟨hp, H⟩ := h
  obtain h_gt | h_eq := lt_or_eq_of_le hp
  . right
    have h_odd: ¬Nat.Even p:= by
      intro h_even
      obtain ⟨x, hx⟩ := h_even
      have h_div_2: 2 ∣ p := by
        use x
        rw [hx]
      obtain h2 := H 2 h_div_2
      obtain hl| hr := h2
      . contradiction
      . rw [hr] at h_gt
        have h_gt': 0<0 := by addarith[h_gt]
        contradiction
    obtain h_even' | h_odd'  := Nat.even_or_odd p
    . contradiction
    . apply h_odd'
  . left
    rw[h_eq]
