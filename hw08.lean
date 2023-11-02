import Mathlib.Data.Real.Basic
import Library.Theory.Parity
import Library.Tactic.Induction
import Library.Tactic.ModCases
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Use


notation3 (prettyPrint := false) "forall_sufficiently_large "(...)", "r:(scoped P => ∃ C, ∀ x ≥ C, P x) => r

/- 2 points -/
-- 4(a)
example {a b d : ℤ} (h : a ≡ b [ZMOD d]) (n : ℕ) : a ^ n ≡ b ^ n [ZMOD d] := by
  simple_induction n with k IA
  . extra
  . obtain ⟨x, hx⟩:= IA
    obtain⟨y, hy⟩ := h
    use (a * x + b^k * y)
    calc
      a^(k+1) - b^(k+1) = a * (a^k - b^k) + b^k * (a-b) := by ring
      _ = a * (d * x) + b^k * (d * y) := by rw[hx,hy]
      _ = d* (a * x + b^k * y) := by ring


/- 3 points -/
-- 4(b)
example : forall_sufficiently_large n : ℕ, 2 ^ n ≥ n ^ 2 := by
  dsimp
  use 4
  intro n hn
  induction_from_starting_point n, hn with x hx IH
  · -- base case
    numbers
  · -- inductive step
    calc
    2^(x+1)
      = 2*2^x := by ring
    _ ≥ 2*x^2 := by rel [IH]
    _ = x^2 + x*x := by ring
    _ ≥ x^2 + 4*x := by rel [hx]
    _ = x^2 + 2*x + 2*x := by ring
    _ ≥ x^2 + 2*x + 2*4 := by rel [hx]
    _ = x^2 + 2*x + 1 + 7 := by ring
    _ = (x+1)^2 + 7 := by ring
    _ ≥ (x+1)^2 := by extra


/- 2 points -/
-- 4(c)
theorem problem4c {a : ℝ} (ha : -1 ≤ a) (n : ℕ) : (1 + a) ^ n ≥ 1 + n * a := by
  simple_induction n with x IH
  . simp
  . have ha : 0 ≤ 1+a := by addarith [ha]
    have h1 : (1 + a)^(x+1) ≥ 1 + (x+1)*a := by 
      calc
        (1+a)^(x+1)
        = (1+a) * (1+a)^x := by ring
        _ ≥ (1 + a) * (1 + x*a) := by rel[IH]
        _ = 1 + a + x*a + x*a^2 := by ring
        _ = 1 + a*(1+x) + x*a^2 := by ring
        _ ≥ 1 + a*(1+x) := by extra
    apply h1

/- 3 points -/
-- 4 (d)
theorem problem4d : forall_sufficiently_large n : ℕ, (3:ℤ) ^ n ≥ 2 ^ n + 100 := by
  dsimp
  use 5
  intro n hn
  induction_from_starting_point n, hn with x hk IH
  · -- base case
    numbers
  · -- inductive step
    calc
      (3:ℤ)^(x+1) = 2*(3^x) + (3^x) := by ring
      _ ≥ 2*(3^x) := by extra
      _ ≥ 2 * (2^x + 100) := by rel [IH]
      _ = 2^(x+1) + 100+100 := by ring
      _ ≥  2^(x+1) + 100 := by extra


/- 5 points -/
def foo : ℕ → ℕ
  | 0     => 1
  | n + 1 => foo (n) + 2 * n + 3

/- 5 points -/
theorem problem5b {n : ℕ} : ∃ (k : ℕ), foo (n) = k ^ 2 := by
  use n+1
  simple_induction n with n IH
  . dsimp[foo]
    numbers
  . dsimp[foo]
    ring
    rw[IH]
    ring



