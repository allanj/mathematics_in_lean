import Mathlib
import Aesop
set_option maxHeartbeats 0
set_option linter.all false
noncomputable section
open BigOperators Real Topology Rat

open Finset



theorem least_constant_inequality (n : Nat) (hn : n ≥ 2) :
  (∃ C : Real, C = 1/8 ∧
    (∀ x : Fin n → Real, (∀ i, x i ≥ 0) →
      ∑ i in Finset.univ, ∑ j in Finset.univ.filter (λ j => j > i),
        x i * x j * (x i^2 + x j^2) ≤ C * (∑ i, x i)^4) ∧
    (∀ C' : Real,
      ∀ x : Fin n → Real, (∀ i, x i ≥ 0) ∧
        ∑ i in Finset.univ, ∑ j in Finset.univ.filter (λ j => j > i),
          x i * x j * (x i^2 + x j^2) ≤ C' * (∑ i, x i)^4 → C' ≥ C) ∧
    (∀ x : Fin n → Real, (∀ i, x i ≥ 0) →
      (∑ i in Finset.univ, ∑ j in Finset.univ.filter (λ j => j > i),
        x i * x j * (x i^2 + x j^2) = C * (∑ i, x i)^4) ↔
      (∃ i j : Fin n, i ≠ j ∧ x i = x j ∧ x i > 0 ∧ ∀ k, k ≠ i → k ≠ j → x k = 0))) := by

  -- Step 1: Prove the inequality for C = 1/8
  have h_inequality : ∀ x : Fin n → Real, (∀ i, x i ≥ 0) →
    ∑ i in Finset.univ, ∑ j in Finset.univ.filter (λ j => j > i),
      x i * x j * (x i^2 + x j^2) ≤ (1/8) * (∑ i, x i)^4 := by
    intros x hx
    have h_pairwise : ∀ i j, i ≠ j →
      x i * x j * (x i^2 + x j^2) ≤ ((x i + x j)^4) / 8 := by
      intros i j hij
      have h_nonneg : x i ≥ 0 ∧ x j ≥ 0 := ⟨hx i, hx j⟩
      set a := x i with ha
      set b := x j with hb
      have h_diff : (a + b)^4 - 8 * a * b * (a^2 + b^2) = (a^2 - 2 * a * b + b^2)^2 := by ring
      have h_sq_nonneg : (a^2 - 2 * a * b + b^2)^2 ≥ 0 := by apply sq_nonneg
      linarith
    -- Sum over all pairs (i, j) with i < j
    have h_sum : ∑ i in Finset.univ, ∑ j in Finset.univ.filter (λ j => j > i),
      x i * x j * (x i^2 + x j^2) ≤ ∑ i in Finset.univ, ∑ j in Finset.univ.filter (λ j => j > i),
        ((x i + x j)^4) / 8 := by
      apply Finset.sum_le_sum
      intros i hi
      apply Finset.sum_le_sum
      intros j hj
      have hij : i ≠ j := by
        rw [Finset.mem_filter] at hj
        exact ne_of_lt hj.2
      exact h_pairwise i j hij
    -- Simplify the right-hand side
    have h_rhs : ∑ i in Finset.univ, ∑ j in Finset.univ.filter (λ j => j > i),
        ((x i + x j)^4) / 8 ≤ ((∑ i, x i)^4) / 8 := by
      -- we first expand the left hand side
      have expand_lhs :
        ∑ i in Finset.univ, ∑ j in Finset.univ.filter (λ j => j > i),
          ((x i + x j)^4) / 8
          = ∑ i in Finset.univ, ∑ j in Finset.univ.filter (λ j => j > i),
            (x i^4 + 4 * x i^3 * x j + 6 * x i^2 * x j^2 + 4 * x i * x j^3 + x j^4) / 8 := by
        -- This tells Lean that to prove the equality of two sums over the same index set,
        -- it suffices to show that the summands are equal for each index
        apply Finset.sum_congr rfl
        intros i hi
        apply Finset.sum_congr rfl
        intros j hj
        have h_eq : (x i + x j) ^ 4 = x i ^ 4 + 4 * x i ^ 3 * x j + 6 * x i ^ 2 * x j ^ 2 + 4 * x i * x j ^ 3 + x j ^ 4 := by
          ring
        rw [h_eq]
      have expand_rhs_simple : ((∑ i, x i)^4) / 8 =
          (∑ i in Finset.univ,
             ∑ j in Finset.univ,
                ∑ k in Finset.univ,
                  ∑ l in Finset.univ, x i * x j * x k * x l) / 8 := by
        have expand_sum_pow : (∑ i : Fin n, x i) ^ 4 =
           ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n, x i * x j * x k * x l := by
          have h_lhs : (∑ i, x i) ^ 4 = ((∑ i, x i) * (∑ i, x i)) * ((∑ i, x i) * (∑ i, x i)) := by
            calc
              (∑ i, x i) ^ 4 = (∑ i, x i)^2 * (∑ i, x i)^2 := by
                ring
              _ = ((∑ i, x i) * (∑ i, x i) * (∑ i, x i) * (∑ i, x i)) := by
                rw [pow_two]
                ring
            ring
          rw [h_lhs]
          have h1 : (∑ i, x i) * (∑ i, x i) = ∑ i, ∑ j, x i * x j := by
            rw [sum_mul_sum]
          rw [h1]
          #check sum_mul
          #check mul_sum
          #check mul_assoc
          have h2 : (∑ i, ∑ j, x i * x j) * (∑ k, ∑ l, x k * x l) = ∑ i, ∑ j, ∑ k, ∑ l, x i * x j * x k * x l := by
            rw [sum_mul_sum]
            simp_rw [sum_mul]
            simp [mul_sum]
            ring_nf
            have h_comm : ∀ x₁ x₂ x₃ x₄, x x₁ * x x₃ * x x₂ * x x₄ = x x₁ * x x₂ * x x₃ * x x₄ := by
              intros x₁ x₂ x₃ x₄
              rw [mul_assoc (x x₁) (x x₃) (x x₂), mul_comm (x x₃) (x x₂), ← mul_assoc]
            -- current goal: ⊢ ∑ x_1 : Fin n, ∑ x_2 : Fin n, ∑ x_3 : Fin n, ∑ x_4 : Fin n, x x_1 * x x_3 * x x_2 * x x_4 =
            -- ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n, x i * x j * x k * x l
            apply Finset.sum_congr rfl
            intros x₁ _
            apply Finset.sum_congr rfl
            intros x₂ _
            apply Finset.sum_congr rfl
            intros x₃ _
            apply Finset.sum_congr rfl
            intros x₄ _
            exact h_comm x₁ x₂ x₃ x₄
          rw [h2]
        rw [expand_sum_pow]


      have expand_rhs :
        (∑ i in univ, x i) ^ 4 / 8 =
          (∑ i in univ, x i ^ 4 +
          4 * ∑ i in univ, ∑ j in univ.filter (λ j => j ≠ i), x i ^ 3 * x j +
          6 * ∑ i in univ, ∑ j in univ, x i ^ 2 * x j ^ 2 +
          12 * ∑ i in univ, ∑ j in univ.filter (λ j => j ≠ i),
                    ∑ k in univ.filter (λ k => k ≠ i ∧ k ≠ j), x i ^ 2 * x j * x k +
          24 * ∑ i in univ, ∑ j in univ.filter (λ j => j ≠ i),
                      ∑ k in univ.filter (λ k => k ≠ i ∧ k ≠ j),
                        ∑ l in univ.filter (λ l => l ≠ i ∧ l ≠ j ∧ l ≠ k), x i * x j * x k * x l) / 8 := by
        rw [expand_rhs_simple]
        -- ring
        sorry

      -- rw [expand_lhs, expand_rhs]
      calc
        ∑ i in Finset.univ, ∑ j in Finset.univ.filter (λ j => j > i) ,
          ((x i + x j)^4) / 8 = ∑ i in Finset.univ, ∑ j in Finset.univ.filter (λ j => j > i),
            (x i^4 + 4 * x i^3 * x j + 6 * x i^2 * x j^2 + 4 * x i * x j^3 + x j^4) / 8 := by
          apply expand_lhs
        _ ≤ ((∑ i, x i)^4) / 8 := by
          sorry
      -- sorry
      -- calc
      --   ∑ i in Finset.univ, ∑ j in Finset.univ.filter (λ j => j > i),
      --     ((x i + x j)^4) / 8 ≤ ((∑ i, x i)^4) / 8 := by sorry

    -- Now, use the fact that ∑ x_i^4 ≥ 0
    have h_nonneg_sum : ∑ i, x i^4 ≥ 0 := by
      apply Finset.sum_nonneg
      intros i hi
      -- use hx : ∀ (i : Fin n), x i ≥ 0, to show that x i^4 ≥ 0
      -- use pow_nonneg: ∀ {α : Type u} [inst : OrderedSemiring α] {a : α}, 0 ≤ a → ∀ (n : ℕ), 0 ≤ a ^ n
      specialize hx i
      exact pow_nonneg hx 4

    calc
      ∑ i in Finset.univ, ∑ j in Finset.univ.filter (λ j => j > i), x i * x j * (x i^2 + x j^2)
        ≤ ∑ i in Finset.univ, ∑ j in Finset.univ.filter (λ j => j > i),
            ((x i + x j)^4) / 8 := by apply h_sum
      _ ≤ ((∑ i, x i)^4) / 8 := by
        apply h_rhs
      _ ≤ (∑ i, x i)^4 / 8 := by
        linarith
      _ = (1/8) * (∑ i, x i)^4 := by
        ring


  -- Step 2: Prove that 1/8 is the smallest constant
  have h_smallest : ∀ C' : Real,
      ∀ x : Fin n → Real, (∀ i, x i ≥ 0) ∧
        ∑ i in Finset.univ, ∑ j in Finset.univ.filter (λ j => j > i),
          x i * x j * (x i^2 + x j^2) ≤ C' * (∑ i, x i)^4 → C' ≥ 1/8 := by
    -- Construct a specific x that violates the inequality for C' < 1/8
    -- Hint: Consider x where only two elements are non-zero and equal
    sorry

  -- Step 3: Prove the equality condition
  have h_equality : ∀ x : Fin n → Real, (∀ i, x i ≥ 0) →
    (∑ i in Finset.univ, ∑ j in Finset.univ.filter (λ j => j > i),
      x i * x j * (x i^2 + x j^2) = (1/8) * (∑ i, x i)^4) ↔
    (∃ i j : Fin n, i ≠ j ∧ x i = x j ∧ x i > 0 ∧ ∀ k, k ≠ i → k ≠ j → x k = 0) := by
    -- Use the equality condition in Cauchy-Schwarz
    -- Show that equality holds iff x has exactly two non-zero equal elements
    sorry

  -- Combine the above steps to complete the proof
  exact ⟨1/8, rfl, h_inequality, h_smallest, h_equality⟩
