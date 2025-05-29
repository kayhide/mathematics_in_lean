import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S05

section

variable {x y : ℝ}

example (h : y > x ^ 2) : y > 0 ∨ y < -1 := by
  left
  linarith [pow_two_nonneg x]

example (h : -y > x ^ 2 + 1) : y > 0 ∨ y < -1 := by
  right
  linarith [pow_two_nonneg x]

example (h : y > 0) : y > 0 ∨ y < -1 :=
  Or.inl h

example (h : y < -1) : y > 0 ∨ y < -1 :=
  Or.inr h

example : x < |y| → x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    intro h; left; exact h
  · rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  case inl h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  case inr h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  next h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  next h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  match le_or_gt 0 y with
    | Or.inl h =>
      rw [abs_of_nonneg h]
      intro h; left; exact h
    | Or.inr h =>
      rw [abs_of_neg h]
      intro h; right; exact h

namespace MyAbs

theorem le_abs_self (x : ℝ) : x ≤ |x| := by
  apply le_abs.mpr
  left
  exact le_rfl

theorem neg_le_abs_self (x : ℝ) : -x ≤ |x| := by
  apply le_abs.mpr
  right
  exact le_rfl

theorem abs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  apply abs_le.mpr
  constructor
  . linarith [neg_le_abs_self x, neg_le_abs_self y]
  . linarith [le_abs_self x, le_abs_self y]

theorem lt_abs : x < |y| ↔ x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  . rw [abs_of_nonneg h]
    constructor
    . exact Or.inl
    . intro h'
      rcases h' with h'' | h''
      . exact h''
      . exact lt_of_lt_of_le h'' (Left.neg_le_self h)
  . rw [abs_of_neg h]
    constructor
    . exact Or.inr
    . intro h'
      rcases h' with h'' | h''
      . apply lt_trans h''
        exact Right.self_lt_neg h
      . exact h''

theorem abs_lt : |x| < y ↔ -y < x ∧ x < y := by
  rcases le_or_gt 0 x with h | h
  . rw [abs_of_nonneg h]
    constructor
    . intro h'
      exact ⟨by linarith, h'⟩
    . rintro ⟨_, h'⟩
      exact h'
  . rw [abs_of_neg h]
    constructor
    . intro h'
      exact ⟨neg_lt_of_neg_lt h', by linarith⟩
    . rintro ⟨h', _⟩
      exact neg_lt_of_neg_lt h'

end MyAbs

end

example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by
  rcases lt_trichotomy x 0 with xlt | xeq | xgt
  · left
    exact xlt
  · contradiction
  · right; exact xgt

example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rw [mul_assoc]
    apply dvd_mul_right
  · rw [mul_comm, mul_assoc]
    apply dvd_mul_right

example {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by
  rcases h with ⟨x, y, h⟩
  rcases h with h' | h'
  repeat
    linarith [pow_two_nonneg x, pow_two_nonneg y]

example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have : x - 1 = 0 ∨ x + 1 = 0 → x = 1 ∨ x = -1 := by
    intro h'
    rcases h' with h'' | h''
    . left
      calc
        x = x - 1 + 1 := by ring
        _ = 0 + 1 := by rw [h'']
        _ = 1 := by ring
    . right
      calc
        x = x + 1 - 1 := by ring
        _ = 0 - 1 := by rw [h'']
        _ = -1 := by ring
  apply this
  apply eq_zero_or_eq_zero_of_mul_eq_zero
  calc
    (x - 1) * (x + 1) = x ^ 2 - 1 := by ring
    _ = 1 - 1 := by rw [h]
    _ = 0 := by ring

-- Another solution, without using zero divisors
example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  rcases le_or_gt 0 x with h' | h'
  . left
    apply (sq_eq_sq₀ h' (by norm_num)).mp
    rw [h]
    ring
  . right
    apply neg_eq_iff_eq_neg.mp
    have : 0 ≤ -x := by
      apply le_neg.mp
      apply le_of_lt
      rw [neg_zero]
      exact h'
    apply (sq_eq_sq₀ this (by norm_num)).mp
    rw [neg_sq, h]
    ring

example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have : x - y = 0 ∨ x + y = 0 → x = y ∨ x = -y := by
    intro h'
    rcases h' with h'' | h''
    . left
      calc
        x = x - y + y := by ring
        _ = 0 + y := by rw [h'']
        _ = y := by ring
    . right
      calc
        x = x + y - y := by ring
        _ = 0 - y := by rw [h'']
        _ = -y := by ring
  apply this
  apply eq_zero_or_eq_zero_of_mul_eq_zero
  calc
    (x - y) * (x + y) = x ^ 2 - y ^ 2 := by ring
    _ = y ^ 2 - y ^ 2 := by rw [h]
    _ = 0 := by ring

-- Another solution, without using zero divisors
example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  rcases le_or_gt 0 y with ynonneg | yneg
  . rcases le_or_gt 0 x with xnonneg | xneg
    . left
      apply (sq_eq_sq₀ xnonneg ynonneg).mp
      exact h
    . right
      apply neg_eq_iff_eq_neg.mp
      apply (sq_eq_sq₀ (by linarith) ynonneg).mp
      rw [neg_sq]
      exact h
  . rcases le_or_gt 0 x with xnonneg | xneg
    . right
      apply (sq_eq_sq₀ xnonneg (by linarith)).mp
      rw [neg_sq]
      exact h
    . left
      apply neg_inj.mp
      apply (sq_eq_sq₀ (by linarith) (by linarith)).mp
      rw [neg_sq, neg_sq]
      exact h

section
variable {R : Type*} [CommRing R] [IsDomain R]
variable (x y : R)

example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have : x - 1 = 0 ∨ x + 1 = 0 → x = 1 ∨ x = -1 := by
    intro h'
    rcases h' with h'' | h''
    . left
      calc
        x = x - 1 + 1 := by ring
        _ = 0 + 1 := by rw [h'']
        _ = 1 := by ring
    . right
      calc
        x = x + 1 - 1 := by ring
        _ = 0 - 1 := by rw [h'']
        _ = -1 := by ring
  apply this
  apply eq_zero_or_eq_zero_of_mul_eq_zero
  calc
    (x - 1) * (x + 1) = x ^ 2 - 1 := by ring
    _ = 1 - 1 := by rw [h]
    _ = 0 := by ring

example (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have : x - y = 0 ∨ x + y = 0 → x = y ∨ x = -y := by
    intro h'
    rcases h' with h'' | h''
    . left
      calc
        x = x - y + y := by ring
        _ = 0 + y := by rw [h'']
        _ = y := by ring
    . right
      calc
        x = x + y - y := by ring
        _ = 0 - y := by rw [h'']
        _ = -y := by ring
  apply this
  apply eq_zero_or_eq_zero_of_mul_eq_zero
  calc
    (x - y) * (x + y) = x ^ 2 - y ^ 2 := by ring
    _ = y ^ 2 - y ^ 2 := by rw [h]
    _ = 0 := by ring

end

example (P : Prop) : ¬¬P → P := by
  intro h
  cases em P
  · assumption
  · contradiction

example (P : Prop) : ¬¬P → P := by
  intro h
  by_cases h' : P
  · assumption
  contradiction

example (P Q : Prop) : P → Q ↔ ¬P ∨ Q := by
  constructor
  . intro h
    by_cases h' : P
    . exact Or.inr (h h')
    . exact Or.inl h'
  . intro h p
    rcases h with h' | h'
    . contradiction
    . assumption
