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
    intros x h_nonneg
    let P2 := ∑ i, (x i) ^ 2
    let S2 := ∑ i in Finset.univ, ∑ j in Finset.univ.filter (λ j => j > i), x i * x j
    have h1 : ∑ i in Finset.univ, ∑ j in Finset.univ.filter (λ j => j > i), x i * x j * (x i ^ 2 + x j ^ 2)
           ≤ ∑ i in Finset.univ, ∑ j in Finset.univ.filter (λ j => j > i), x i * x j * P2 := by
      apply sum_le_sum
      intros i _
      apply sum_le_sum
      intros j hji
      apply mul_le_mul_of_nonneg_left
      {
        have i_not_equal_j : i ≠ j := by
          by_contra h
          have hii : i ∈ filter (fun j => j > i) univ := by
            rw [← h] at hji
            exact hji
          -- #check mem_filter.mp
          have hi_gt_i : i > i := by
            apply (Finset.mem_filter.mp hii).2
          exact lt_irrefl i hi_gt_i
        calc
          x i ^ 2 + x j ^ 2 = (∑ k in {i, j}, x k ^ 2) := by
            rw [Finset.sum_pair]
            · apply i_not_equal_j
          _ ≤ (∑ k : Fin n, x k ^ 2) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            intros k hk
            exact Finset.mem_univ k
            intro k _
            #check pow_nonneg
            #check h_nonneg
            -- show k is non negative
            have k_nonneg: x k ≥ 0 := by
              apply h_nonneg
            intro h_not_in
            exact pow_nonneg k_nonneg 2
      }
      {
        exact mul_nonneg (h_nonneg i) (h_nonneg j)
      }

    -- Step 2: Use the AM-GM (or Cauchy-Schwarz) inequality to bound P2 * S2
    have h2 : ∑ i in Finset.univ, ∑ j in Finset.univ.filter (λ j => j > i), x i * x j * P2 ≤ P2 * S2 := by
      have h21 : ∑ i : Fin n, ∑ j ∈ filter (fun j => j > i) univ, x i * x j * P2 =
                P2 * ∑ i : Fin n, ∑ j ∈ filter (fun j => j > i) univ, x i * x j := by
        simp_rw [mul_sum]
        apply Finset.sum_congr rfl
        intros x₁ _
        apply Finset.sum_congr rfl
        intros x₂ _
        rw[← mul_assoc]
        ring
      have h22 : ∑ i : Fin n, ∑ j ∈ filter (fun j => j > i) univ, x i * x j = S2 := by
        rfl
      calc
        ∑ i : Fin n, ∑ j ∈ filter (fun j => j > i) univ, x i * x j * P2 = P2 * ∑ i : Fin n, ∑ j ∈ filter (fun j => j > i) univ, x i * x j := by
          rw [h21]
        _ = P2 * S2 := by
          rw [h22]
        _ ≤ P2 * S2 := by
          linarith

    have h_am_gm : P2 * S2 ≤ (1 / 8) * (P2 + 2 * S2) ^ 2 := by
      have h_amgm : 2 * Real.sqrt (P2 * 2 * S2) ≤ P2 + 2 * S2 := by
        have square_non_neg : ∀ (i : Fin n), x i ^2 ≥ 0 := by
          intros i
          have i_nonneg: x i ≥ 0 := by
            apply h_nonneg
          exact pow_nonneg i_nonneg 2
        have p2_ge_zero : P2 ≥ 0 := by
          apply sum_nonneg
          intro i _
          exact square_non_neg i
        have s2_ge_zero : S2 ≥ 0 := by
          apply sum_nonneg
          intros i hi
          apply sum_nonneg
          intro j hj
          exact (mul_nonneg (h_nonneg i) (h_nonneg j))
        let a := P2
        let b := 2 * S2
        have h : (Real.sqrt a - Real.sqrt b) ^ 2 ≥ 0 := by nlinarith
        have expanded : (Real.sqrt a - Real.sqrt b) ^ 2 = a - 2 * Real.sqrt (a * b) + b := by
          calc
            (Real.sqrt a - Real.sqrt b) ^ 2 = Real.sqrt a ^ 2 - 2 * Real.sqrt a * Real.sqrt b + Real.sqrt b ^ 2 := by ring
            _ = a - 2 * Real.sqrt a * Real.sqrt b + Real.sqrt b ^ 2 := by
              rw [Real.sq_sqrt]
              linarith
            _ = a - 2 * Real.sqrt a * Real.sqrt b + b := by
              rw [Real.sq_sqrt]
              have b_ge_zero : b ≥ 0 := by
                ring_nf
                linarith
              linarith
            _ = a - 2 * Real.sqrt (a * b) + b := by
              rw [Real.sqrt_mul p2_ge_zero]
              linarith
        have key_ineq : 2 * Real.sqrt (a * b) ≤ a + b := by linarith
        -- rw [← key_ineq]
        -- exact key_ineq
        calc
           2 * Real.sqrt (P2 * 2 * S2) = 2 * Real.sqrt (a * b) := by
            ring_nf
           _ ≤ a + b := by
            apply key_ineq
      have h_squared : (2 * Real.sqrt (P2 * 2 * S2))^2 ≤ (P2 + 2 * S2)^2 := by
        apply pow_le_pow_left
        · exact mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
        · exact h_amgm
      #check sum_nonneg
      have h_simplify : (2 * Real.sqrt (P2 * 2 * S2))^2 = 4 * (P2 * 2 * S2) := by
        rw [pow_two]
        rw [mul_mul_mul_comm]
        rw [← pow_two]
        rw [← pow_two]
        rw [Real.sq_sqrt]
        rw [pow_two]
        ring
        #check sq_nonneg
        have square_non_neg : ∀ (i : Fin n), x i ^2 ≥ 0 := by
          intros i
          have i_nonneg: x i ≥ 0 := by
            apply h_nonneg
          exact pow_nonneg i_nonneg 2
        have p2_ge_zero : P2 ≥ 0 := by
          apply sum_nonneg
          intro i _
          exact square_non_neg i
        have s2_ge_zero : S2 ≥ 0 := by
          apply sum_nonneg
          intros i hi
          apply sum_nonneg
          intro j hj
          exact (mul_nonneg (h_nonneg i) (h_nonneg j))
        apply mul_nonneg
        apply mul_nonneg
        exact p2_ge_zero
        norm_num
        exact s2_ge_zero
        -- exact (mul_nonneg p2_ge_zero  s2_ge_zero)
      have h_simplify_add :  1/8 * (2 * Real.sqrt (P2 * 2 * S2))^2 = 1/8 * 4 * (P2 * 2 * S2) := by
        rw [h_simplify]
        ring
      calc
        P2 * S2 = 1/8 * 8 * (P2 * S2) := by
          field_simp
        _ = 1/8 * 4 * 2 * (P2 * S2) := by
          ring
        _ = 1/8 * 4 * 2 * P2 * S2 := by
          ring
        _ = 1/8 * 4 * P2 * 2 * S2 := by
          ring
        _ = 1/8 * 4 * (P2 * 2 * S2) := by
          ring
        _ = 1/8 * (2 * Real.sqrt (P2 * 2 * S2))^2 := by
          rw [← h_simplify_add]
        _ ≤ 1/8 * (P2 + 2 * S2)^2 := by
          #check mul_le_mul_of_nonneg_left
          apply mul_le_mul_of_nonneg_left h_squared
          positivity
    have h_sum_sq : P2 + 2 * S2 = (∑ i, x i) ^ 2 := by
      rw [pow_two]
      rw [Finset.sum_mul_sum]
      have h_lhs : P2 + 2 * S2 = ∑ i : Fin n, (x i ^ 2 + 2 * ∑ j ∈ filter (fun j => j > i) univ, x i * x j) := by
        #check add_mul
        #check sum_mul
        simp [P2, S2]
        rw [sum_add_distrib]
        ring_nf
        rw [Finset.sum_mul]
      rw [h_lhs]
      -- Rewrite the right-hand side
      have h_rhs : ∑ i : Fin n, ∑ j : Fin n, x i * x j =
                  ∑ i : Fin n, (x i * x i + ∑ j ∈ filter (fun j => j ≠ i) univ, x i * x j) := by
        #check sum_product
        apply sum_congr rfl
        intro i hi
        -- #check Finset.sum_eq_add_sum_erase
        have sum_split : ∑ j : Fin n, x i * x j =
          (x i * x i) + ∑ j in filter (fun j => j ≠ i) univ, x i * x j := by
          have hsum : ∑ j in univ, x i * x j = x i * x i + ∑ j in univ.erase i, x i * x j := by
            have hi : i ∈ univ := mem_univ i
            #check insert_erase
            have h_univ : univ = insert i (univ.erase i) := by
              rw [Finset.insert_erase hi]
            rw [h_univ, sum_insert]
            simp
            rw [Finset.mem_erase]
            intro h  -- h : i ≠ i ∧ i ∈ univ
            exact h.1 rfl
          rw [hsum]
          congr
          have : univ.erase i = filter (λ j => j ≠ i) univ := by
            ext
            simp only [mem_erase, mem_filter, mem_univ, true_and]
            tauto
          rw [this]
        exact sum_split
      rw [h_rhs]
      have h_diff : ∑ i : Fin n, (x i ^ 2 + 2 * ∑ j ∈ filter (fun j => j > i) univ, x i * x j) -
                ∑ i : Fin n, (x i * x i + ∑ j ∈ filter (fun j => j ≠ i) univ, x i * x j) = 0 := by

        have h_diff1 : ∑ i : Fin n, (x i ^ 2 + 2 * ∑ j ∈ filter (fun j => j > i) univ, x i * x j) -
            ∑ i : Fin n, (x i * x i + ∑ j ∈ filter (fun j => j ≠ i) univ, x i * x j) =
            ∑ i, (2 * ∑ j ∈ filter (fun j=> j > i) univ, x i * x j) -
            ∑ i, ∑ j ∈ filter (fun j=> j ≠ i) univ, x i * x j := by
          #check Finset.sum_add_distrib
          have hxx : ∑ i : Fin n, (x i ^ 2 + 2 * ∑ j ∈ filter (fun j => j > i) univ, x i * x j) -
                    ∑ i : Fin n, (x i * x i + ∑ j ∈ filter (fun j => j ≠ i) univ, x i * x j) =
                     ∑ i : Fin n, (2 * ∑ j ∈ filter (fun j => j > i) univ, x i * x j -
                    ∑ j ∈ filter (fun j => j ≠ i) univ, x i * x j) := by
            rw [← Finset.sum_sub_distrib]
            apply sum_congr rfl
            intro i _
            rw [pow_two]
            let term_1 := x i * x i + 2 * ∑ j ∈ filter (fun j => j > i) univ, x i * x j
            #check sub_self
            ring
          rw [hxx]
          rw [← Finset.sum_sub_distrib]
        rw [h_diff1]
        have h_diff2 : ∑ i : Fin n, ∑ j ∈ filter (λ j => j ≠ i) univ, x i * x j =
              ∑ i : Fin n, ∑ j ∈ filter (λ j => j < i) univ, x i * x j +
              ∑ i : Fin n, ∑ j ∈ filter (λ j => j > i) univ, x i * x j := by
          #check Finset.sum_congr
          rw [← sum_add_distrib]
          apply sum_congr rfl
          intro i _
          have h_split : ∑ j ∈ filter (fun j => j ≠ i) univ, x i * x j =
                          ∑ j ∈ filter (fun j => j < i) univ, x i * x j +
                          ∑ j ∈ filter (fun j => j > i) univ, x i * x j := by
            have h_union : univ.filter (λ j => j ≠ i) =
                (univ.filter (λ j => j < i)) ∪ (univ.filter (λ j => i < j)) := by
              ext j
              simp only [mem_filter, mem_union, mem_univ, true_and]
              constructor
              {
                intro h
                #check Fin.val_injective.ne
                have h_neq : (j : ℕ) ≠ (i : ℕ) := by
                  apply Fin.val_injective.ne h
                have h_order := lt_or_gt_of_ne h_neq
                have h' : j < i ∨ i < j :=
                  h_order.elim
                    (λ h_lt => Or.inl h_lt)
                    (λ h_gt => Or.inr h_gt)
                exact h'
              }
              {
                intro h
                by_contra hij
                rw [hij] at h
                #check lt_irrefl
                exact Or.elim h (λ h1 => lt_irrefl i h1) (λ h2 => lt_irrefl i h2)
              }
            have h_disjoint : Disjoint (univ.filter (λ j => j < i)) (univ.filter (λ j => i < j)) := by
              rw [Finset.disjoint_filter]
              intro j hj1 hj2
              apply lt_asymm hj2
            rw [h_union, sum_union h_disjoint]
          rw [h_split]
        rw [h_diff2]
        rw [sub_add_eq_sub_sub]
        #check sub_self
        have h_diff3 : ∑ i : Fin n, 2 * ∑ j ∈ filter (fun j => j > i) univ, x i * x j =
                  ∑ i : Fin n, ∑ j ∈ filter (fun j => j > i) univ, x i * x j +
                  ∑ i : Fin n, ∑ j ∈ filter (fun j => j > i) univ, x i * x j := by
          #check sum_mul
          #check mul_sum
          rw [← mul_sum]
          rw [two_mul]
        rw [h_diff3]
        have h_diff4 : ∑ i : Fin n, ∑ j ∈ filter (fun j => j > i) univ, x i * x j +
                        ∑ i : Fin n, ∑ j ∈ filter (fun j => j > i) univ, x i * x j -
                        ∑ i : Fin n, ∑ j ∈ filter (fun j => j < i) univ, x i * x j -
                      ∑ i : Fin n, ∑ j ∈ filter (fun j => j > i) univ, x i * x j =
                      ∑ i : Fin n, ∑ j ∈ filter (fun j => j > i) univ, x i * x j -
                        ∑ i : Fin n, ∑ j ∈ filter (fun j => j < i) univ, x i * x j := by
          ring
        #check add_comm
        rw [h_diff4]
        have h_diff5 : ∑ i : Fin n, ∑ j ∈ filter (fun j => j > i) univ, x i * x j =
                        ∑ i : Fin n, ∑ j ∈ filter (fun j => j < i) univ, x j * x i := by
          have h_right : ∑ i : Fin n, ∑ j in Finset.filter (λ j => j < i) Finset.univ, x j * x i =
                ∑ i : Fin n, ∑ j in Finset.filter (λ j => j < i) Finset.univ, x i * x j := by
            apply Finset.sum_congr rfl
            intros i _
            apply Finset.sum_congr rfl
            intros j _
            rw [mul_comm]
          have h_swap : ∑ i : Fin n, ∑ j in Finset.filter (λ j =>  j < i) Finset.univ, x i * x j =
                ∑ j : Fin n, ∑ i in Finset.filter (λ i => j < i) Finset.univ, x i * x j := by
            #check sum_comm
            -- rw [sum_comm]
              -- Define the function f(i, j) = x_i * x_j if j < i, else 0.
            let f : Fin n × Fin n → ℝ := λ p => if p.2 < p.1 then x p.1 * x p.2 else 0
            have h_left : ∑ i in univ, ∑ j in filter (λ j => j < i) univ, x i * x j =
                ∑ i in univ, ∑ j in univ, f (i, j) := by
              apply Finset.sum_congr rfl
              intros i hi
              rw [←Finset.sum_filter]
            have h_right : ∑ j in univ, ∑ i in filter (λ i => j < i) univ, x i * x j =
                 ∑ j in univ, ∑ i in univ, f (i, j) := by
              apply Finset.sum_congr rfl
              intros j hj
              rw [←Finset.sum_filter]
            rw [h_left, h_right]
            exact Finset.sum_comm
          rw [h_right, h_swap]
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          rw [mul_comm]
        rw [h_diff5]
        #check mul_comm
        have h_diff6 : ∑ i : Fin n, ∑ j ∈ filter (fun j => j < i) univ, x j * x i =
                    ∑ i : Fin n, ∑ j ∈ filter (fun j => j < i) univ, x i * x j := by
          apply sum_congr rfl
          intro i hi
          apply sum_congr rfl
          intro j hj
          rw [mul_comm]
        rw [h_diff6]
        ring
      exact sub_eq_zero.mp h_diff


    calc
      ∑ i in Finset.univ, ∑ j in Finset.univ.filter (λ j => j > i), x i * x j * (x i^2 + x j^2) ≤
        ∑ i in Finset.univ, ∑ j in Finset.univ.filter (λ j => j > i), x i * x j * P2 := by
        apply h1
      _ ≤ P2 * S2 := by
        apply h2
      _ ≤ (1 / 8) * (P2 + 2 * S2) ^ 2 := by
        apply h_am_gm
      _ = (1 / 8) * ((∑ i, x i) ^ 2) ^ 2 := by
        rw [h_sum_sq]
      _ = (1 / 8) * (∑ i, x i) ^ 4 := by
        linarith

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
