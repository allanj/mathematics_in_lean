import Mathlib.Tactic
import Mathlib.Util.Delaborators
-- import Mathlib.Data.Nat.Prime
import Mathlib.Data.Real.Basic

/-
complete ex20240815 a1, a2, a3 and a4.
-/
theorem ex20240815a1 {A B : Prop} : A ∧ (A → B) → B := by
  intro h
  rcases h with ⟨h₀, h₁⟩
  exact h₁ h₀


theorem ex20240815a2 {A B : Prop} (h : A ∧ (A → B)) : B := by
  rcases h with ⟨h₀, h₁⟩
  exact h₁ h₀

theorem ex20240815a3 {A B : Prop} : A → (A → B) → B := by
  intro h₀ h₁
  exact h₁ h₀

theorem ex20240815a4 {A B : Prop} (hA : A) (hAImB : A → B) : B := by
  exact hAImB hA


/-
Complete b1 and b2.
For b2, you have to complete the sorry part based on the given code.
-/
theorem ex20240815b1 {P Q : Prop} : (P → Q) → (¬Q → ¬P) := by
  intro h0 h1 h2
  have h3 := h0 h2
  contradiction


theorem ex20240815b2
    {a b : ℝ} {f : ℝ → ℝ} (h : Monotone f) (h' : f a < f b) :
    a < b := by
  have h_ab := @h b a   -- b ≤ a → f b ≤ f a
  have h_inv_ab : ¬f b ≤ f a → ¬b ≤ a := by
    contrapose!
    intro hb_lt_a
    exact h_ab hb_lt_a
  simp [h'] at h_inv_ab
  exact h_inv_ab


/-
Complete the sorry part based on the given code.
In the third line you must use `rcases h' ...` as is described in the comment.
-/
theorem ex20240815c {c : ℝ} (h : c ≠ 0) : Function.Injective fun x ↦ c * x := by
  intro x₁ x₂ h'
  simp at h'
  rcases h' with h' | h'
  · exact h'
  . contradiction
