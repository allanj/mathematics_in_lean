import Mathlib
import Aesop
open BigOperators Real Nat Topology Rat
/- ex20240829a -/
/- Complete the proof.

   One possible way is to base your Lean code on the following proof in natural language:
   1. get a = d * something1 and b = d * something2
   2. write down what (a % b) is and show it is (d * something3)
   3. replacing (a % b) = d * something3 back to the goal
-/

theorem ex20240829a {a b d : ℤ} (h1 : d ∣ a) (h2 : d ∣ b) : d ∣ (a % b) := by
  obtain ⟨k1, hk1⟩ := h1
  obtain ⟨k2, hk2⟩ := h2
  use k1 - k2 * (a / b)

  calc
    a % b = a - b * (a / b) := by rw [Int.emod_def]
    _ = d * k1 - d * k2 * (a / b) := by rw [hk1, hk2]
    _ = d * (k1 - k2 * (a / b)) := by
      rw [mul_sub]
      rw [← mul_assoc]


/- ex20240829b -/
section ex20240829b
/- Complete the proof for ex20240829b1, which is based on the excercise
   `theorem fac_pos` as in MIL ch 5.2,
   but we do it using Finset.range and BigOperator ∏, instead of recursive def

   Requirement:
   * Use the Tactic `induction'`
-/
def f_id' : ℕ → ℕ
  | 0 => 1
  | k => k

#check Nat.succ_pos
theorem ex20240829b1 (n : ℕ) : ∏ i in Finset.range (n + 1), f_id' i > 0 := by
  induction' n with k hk
  · -- Base case: n = 0
    simp [f_id']
  · -- Inductive step: n = k + 1
    rw [Finset.range_succ]
    rw [Finset.prod_insert]
    · apply Nat.mul_pos
      · exact Nat.succ_pos k
      · exact hk
    · simp

/- Complete the proof for ex20240829b2, which is based on the excercise
   `theorem sum_id` as in MIL ch 5.2,
   but we do it using recursive def, instead of Finset.range and BigOperator ∑

   Requirement:
   * Use the Tactic `induction'`
-/
def sum_id' : ℕ → ℕ
  | 0 => 0
  | k + 1 => k + 1 + sum_id' k


theorem ex20240829b2 (n : ℕ) : sum_id' n = n * (n + 1) / 2 := by
  induction' n with k hk
  · -- Base case: n = 0
    simp [sum_id']
  · -- Inductive step: n = k + 1
    calc
      sum_id' (k + 1) = (k + 1) + sum_id' k := by rw [sum_id']
      _ = (k + 1) + k * (k + 1) / 2 := by rw [hk]
      _ = 1 + k + (k + k ^ 2) / 2 := by
        ring_nf
      _ = (1 + k) * 2 / 2 + (k + k ^ 2) / 2 := by
        congr
        ring_nf
        simp
        rw [add_comm 1 k]
      _ = (2 + 2 * k) / 2 + (k + k ^ 2) / 2 := by
        ring_nf
      _ = (2 + 2 * k + k + k ^ 2) / 2 := by
        rw [← Nat.add_div_of_dvd_left]
        · ring_nf
        · -- show that 2 divides k + k^2
          have h : k + k^2 = k * (k + 1) := by ring
          rw [h]
          apply Nat.dvd_of_mod_eq_zero
          have h : k % 2 = 0 ∨ k % 2 = 1 := by omega
          rcases h with (h | h) <;> simp [h, Nat.mul_mod, Nat.add_mod, Nat.mod_eq_of_lt]
      _ = (k + 1) * (k + 2) / 2 := by ring_nf
      _ = (k + 1) * ((k + 1) + 1) / 2 := by ring




section end -- ex20240829b

/- ex20240829c -/
/- Complete the proof.

   Requirement:
   * use the Tactic `induction'`
-/
theorem ex20240829c1 (n : ℕ) (h : n ≥ 3) : 2 ^ n > n + 2 := by
  induction' h with n h IH
  -- Base case: when `n = 3`, we need to show `2^3 > 3 + 2`
  norm_num
  -- Inductive step: assume the statement holds for `n`, i.e., `2^n > n + 2`
  -- We need to show it holds for `n + 1`, i.e., `2^(n+1) > (n + 1) + 2`
  cases n with
  | zero => contradiction  -- If `n` is zero, it contradicts `n ≥ 3`
  | succ n =>
    cases n with
    | zero => contradiction  -- If `n` is one, it contradicts `n ≥ 3`
    | succ n =>
      -- Simplify the expressions using `pow_succ` and `mul_add`
      simp_all [pow_succ, mul_add]
      -- Use `linarith` to handle the linear arithmetic and complete the proof
      linarith

/- Complete the proof.

   Requirement:
   * use the Tactic `induction'`
-/
theorem ex20240829c2 (x : ℝ) (hx : x > -1) (n : ℕ) :
    (1 + x) ^ n ≥ 1 + n * x := by
  induction n with
  | zero =>
    -- Base case: when n = 0, (1 + x)^0 = 1 and 1 + 0 * x = 1, so the inequality holds
    simp
  | succ n ih =>
    -- Inductive step: assume the statement holds for n, i.e., (1 + x)^n ≥ 1 + n * x
    -- We need to show it holds for n + 1
    simp_all [pow_succ, mul_add, add_mul, mul_one, mul_assoc, mul_comm, mul_left_comm]
    -- Simplify the expression and use linear arithmetic to prove the inequality
    nlinarith [sq_nonneg x]
