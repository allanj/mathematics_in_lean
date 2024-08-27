import Mathlib.Data.Real.Basic
import Mathlib.Data.Dfinsupp.Interval

theorem ex20240808a (x y z : ℝ) : x * y * z = x * z * y := by
  rw [mul_assoc]
  rw [mul_comm y z]
  rw [← mul_assoc]


example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  apply le_trans
  · apply h₀
  . apply h₁

section
variable (a b c : ℝ)
variable (h : a ≤ b) (h' : b ≤ c)
#check (le_refl : ∀ a : Real, a ≤ a)
#check (le_refl a : a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)
#check (le_trans h : b ≤ c → a ≤ c)
#check (le_trans h h' : a ≤ c)
end


theorem ex20240808b (a b c d : ℝ) (h₀ : a ≤ b) (h₁ : b ≤ c) (h₂ : c ≤ d)
    : a + a ≤ c + d := by
  have h₃ : a ≤ c := by apply le_trans h₀ h₁
  have h₄ : a ≤ d := by apply le_trans h₃ h₂
  apply add_le_add h₃ h₄

theorem ex20240808b_backward (a b c d : ℝ) (h₀ : a ≤ b) (h₁ : b ≤ c) (h₂ : c ≤ d)
    : a + a ≤ c + d := by
  apply add_le_add
  -- Goal: a ≤ c and a ≤ d
  apply le_trans h₀ h₁
  apply le_trans _ h₂
  apply le_trans h₀ h₁
