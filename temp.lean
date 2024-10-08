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
          x i * x j * (x i^2 + x j^2) = (1/8) * (∑ i, x i)^4) →
        (∃ i j : Fin n, i ≠ j ∧ x i = x j ∧ x i > 0 ∧ ∀ k, k ≠ i → k ≠ j → x k = 0)) ∧
    (∀ x : Fin n → Real, (∀ i, x i ≥ 0) →
         (∃ i j : Fin n, i ≠ j ∧ x i = x j ∧ x i > 0 ∧ ∀ k, k ≠ i → k ≠ j → x k = 0)  →
         (∑ i in Finset.univ, ∑ j in Finset.univ.filter (λ j => j > i),
          x i * x j * (x i^2 + x j^2) = (1/8) * (∑ i, x i)^4)) ) := by
  -- Step 1: Prove the inequality for C = 1/8
  have h_inequality : ∀ x : Fin n → Real, (∀ i, x i ≥ 0) →
    ∑ i in Finset.univ, ∑ j in Finset.univ.filter (λ j => j > i),
      x i * x j * (x i^2 + x j^2) ≤ (1/8) * (∑ i, x i)^4 := by
    sorry

  -- Step 2: Prove that 1/8 is the smallest constant
  have h_smallest : ∀ C' : Real,
      ∀ x : Fin n → Real, (∀ i, x i ≥ 0) ∧
        ∑ i in Finset.univ, ∑ j in Finset.univ.filter (λ j => j > i),
          x i * x j * (x i^2 + x j^2) ≤ C' * (∑ i, x i)^4 → C' ≥ 1/8 := by
    -- Construct a specific x that violates the inequality for C' < 1/8
    -- Hint: Consider x where only two elements are non-zero and equal
    sorry

  -- Step 3: Prove the equality condition
  have forward_dir : ∀ x : Fin n → Real, (∀ i, x i ≥ 0) →
    (∑ i in Finset.univ, ∑ j in Finset.univ.filter (λ j => j > i),
      x i * x j * (x i^2 + x j^2) = (1/8) * (∑ i, x i)^4) →
    (∃ i j : Fin n, i ≠ j ∧ x i = x j ∧ x i > 0 ∧ ∀ k, k ≠ i → k ≠ j → x k = 0) := by
    -- Show that equality holds iff x has exactly two non-zero equal elements
    intros x h_nonneg
    sorry

  have backward_dir : ∀ x : Fin n → Real, (∀ i, x i ≥ 0) →
         (∃ i j : Fin n, i ≠ j ∧ x i = x j ∧ x i > 0 ∧ ∀ k, k ≠ i → k ≠ j → x k = 0)  →
         (∑ i in Finset.univ, ∑ j in Finset.univ.filter (λ j => j > i),
          x i * x j * (x i^2 + x j^2) = (1/8) * (∑ i, x i)^4) := by
    intros x h_nonneg
    intro h_exist
    rcases h_exist with ⟨i, j, h_ij_ne, h_x_eq, h_xi_pos, h_zeros⟩
    let s := x i
    have h_sum : ∑ k, x k = 2 * s := by
      have h_sub_sum : ∑ k : Fin n, x k = x i + x j + ∑ k in univ.filter (λ k =>  k ≠ i ∧ k ≠ j), x k := by

        have i_in_set: i ∈ univ := by
          simp_all
        have j_in_set: j ∈ univ := by
          simp_all

        #check sum_eq_add_sum_diff_singleton
        rw [sum_eq_add_sum_diff_singleton i_in_set]
        let new_s := univ \ {i}
        have j_in_sub_set: j ∈ new_s := by
          rw [mem_sdiff]
          constructor
          {
            exact j_in_set
          }
          {
            intro curr_h
            #check mem_singleton
            rw [mem_singleton] at curr_h
            have switch_currh : i = j := by
              rw [curr_h]
            exact h_ij_ne switch_currh
          }
        have except_j_sum : ∑ x_1 ∈ new_s, x x_1 =  x j + ∑ k ∈ new_s \ {j}, x k := by
          rw [sum_eq_add_sum_diff_singleton j_in_sub_set]
        rw [except_j_sum]
        rw [← add_assoc]
        simp_all
        sorry

      simp_all [h_zeros, h_x_eq, Finset.sum_eq_add]
      -- simp_all [h_zeros, h_x_eq]
      -- rw [Finset.sum_eq_add]
      #check add_eq_add_iff_eq_and_eq
      sorry
      -- Now simplify the double sum (sum over i, sum over j > i)
    have h_simplify : ∑ i, ∑ j in filter (λ j => j > i) univ, x i * x j * (x i ^ 2 + x j ^ 2) =
      s * s * (s^2 + s^2) := by
      simp [h_zeros]
      -- rw [h_x_eq]
      sorry
    rw [h_simplify, h_sum]
    simp
    rw [mul_pow]
    ring
  -- Combine the above steps to complete the proof
  exact ⟨1/8, rfl, h_inequality, h_smallest, forward_dir, backward_dir⟩
