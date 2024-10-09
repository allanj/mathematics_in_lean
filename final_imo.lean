import Mathlib
import Aesop
set_option maxHeartbeats 0
set_option linter.all false
noncomputable section
open BigOperators Real Topology Rat

open Finset



theorem constant_inequality (n : Nat) (hn : n ≥ 2) :
  (∃ C : Real, C = 1/8 ∧
    (∀ x : Fin n → Real, (∀ i, x i ≥ 0) →
      ∑ i in Finset.univ, ∑ j in Finset.univ.filter (λ j => j > i),
        x i * x j * (x i^2 + x j^2) ≤ C * (∑ i, x i)^4) ∧
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
        have j_in_sub_set: j ∈ univ \ {i} := by
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
        congr
        -- #check sdiff_singleton_eq_filter
        -- rw [← sdiff_singleton_eq_filter]
        have univ_exclude: new_s \ {j} = univ \ {i,j} := by
          simp [new_s]
          ext k
          simp only [mem_sdiff, mem_univ, true_and, mem_insert, mem_singleton]
          tauto
        rw [univ_exclude]
        ext k
        simp only [mem_sdiff, mem_filter, mem_univ, true_and, mem_singleton]
        constructor
        {
          intro h
          constructor
          {
            intro h_eq
            apply h
            simp_all
          }
          {
            intro h_eq
            apply h
            simp_all
          }
        }
        {
          rintro ⟨h_ki, h_kj⟩
          intro h_mem
          simp_all
        }
      rw [h_sub_sum]
      calc
        x i + x j + ∑ k ∈ filter (fun k => k ≠ i ∧ k ≠ j) univ, x k =
           x i + x i + ∑ k ∈ filter (fun k => k ≠ i ∧ k ≠ j) univ, x k := by
          rw [h_x_eq]
        _ = 2 * x i  + ∑ k ∈ filter (fun k => k ≠ i ∧ k ≠ j) univ, x k := by
          ring
        _ = 2 * x i + 0 := by
          have other_zero: ∑ k ∈ filter (fun k => k ≠ i ∧ k ≠ j) univ, x k = 0 := by
            apply Finset.sum_eq_zero
            intros k hk
            simp only [mem_filter, mem_univ, true_and] at hk
            exact h_zeros k hk.1 hk.2
          rw [other_zero]
        _ = 2 * x i := by
          ring

    have h_simplify : ∑ i, ∑ j in filter (λ j => j > i) univ, x i * x j * (x i ^ 2 + x j ^ 2) =
      s * s * (s^2 + s^2) := by
      -- #check Finset.sum_eq_single
      -- apply Finset.sum_eq_single h_zeros
      have h_sum : ∑ i, ∑ j in filter (λ j => j > i) univ, x i * x j * (x i ^ 2 + x j ^ 2)
                = x i * x j * (x i ^ 2 + x j ^ 2):= by
        have h_zero : ∀ a b : Fin n, (a ≠ i ∧ a ≠ j) ∨ (b ≠ i ∧ b ≠ j) → x a * x b * (x a ^ 2 + x b ^ 2) = 0 := by
          intros a b hab
          cases hab
          case inl h₁ =>
            have xa_zero : x a = 0 := h_zeros a h₁.left h₁.right
            rw [xa_zero, zero_mul, zero_mul]
          case inr h₂ =>
            have xb_zero : x b = 0 := h_zeros b h₂.left h₂.right
            rw [xb_zero, mul_zero, zero_mul]
        have h_sum_eq_lt (h_lt : i < j) : ∑ a : Fin n, ∑ b in univ.filter (fun b => b > a), x a * x b * (x a ^ 2 + x b ^ 2) =
              x i * x j * (x i ^ 2 + x j ^ 2) := by
          rw [sum_eq_single i _ _]
          · rw [sum_eq_single j _ _]
            -- Show that for a = i and b = j, we have b > a
            · intro b hib hbj
              have xb_zero: x b = 0 := by
                have b_not_equal_i: b ≠ i := by
                  have h_b_gt_i : b > i := (mem_filter.mp hib).2
                  exact ne_of_gt h_b_gt_i
                apply h_zeros b b_not_equal_i hbj
              rw [xb_zero]
              ring
            · intro h_contra
              exfalso
              apply h_contra
              simp [mem_filter, h_lt]
          · intros a ha ha_ne
            rw [sum_eq_zero]
            intros b hb
            #check ne_of_mem_of_not_mem
            have ha_ne_i : a ≠ i := ha_ne
            by_cases ha_eq_j : a = j
            case pos =>
              -- Then a = j
              rw [ha_eq_j] at hb
              -- Now, b ∈ filter (fun b => b > a) univ
              -- So b > a = j
              have h_b_gt_j : b > j := (mem_filter.mp hb).2
              -- Since i < j < b, b ≠ i
              have h_b_ne_i : b ≠ i := ne_of_gt (lt_trans h_lt h_b_gt_j)
              -- Since b > j, b ≠ j
              have h_b_ne_j : b ≠ j := ne_of_gt h_b_gt_j
              -- Therefore, x b = 0
              have h_xb_zero : x b = 0 := h_zeros b h_b_ne_i h_b_ne_j
              rw [h_xb_zero]
              simp
            case neg =>
              -- Then a ≠ i and a ≠ j, so x a = 0
              have h_xa_zero : x a = 0 := h_zeros a ha_ne_i ha_eq_j
              rw [h_xa_zero]
              simp
          · intro h_contra
            exfalso
            have h_i_in_univ : i ∈ univ := Finset.mem_univ i
            exact h_contra h_i_in_univ
        have h_sum_eq_gt (h_gt : i > j) : ∑ a : Fin n, ∑ b in univ.filter (fun b => b > a), x a * x b * (x a ^ 2 + x b ^ 2) =
            x i * x j * (x i ^ 2 + x j ^ 2) := by
          rw [sum_eq_single j _ _]
          -- Handle the inner sum over b when a = j
          · rw [sum_eq_single i _ _]
            -- For a = j and b = i, b > a holds because i > j
            · rw [h_x_eq]
            -- For other b ≠ i, the terms are zero
            · intros b hb hb_ne
              have h_b_ne_i : b ≠ i := hb_ne
              have h_b_gt_j : b > j := by
                apply (mem_filter.mp hb).2
              have h_b_ne_j : b ≠ j := ne_of_gt h_b_gt_j
              -- Since b ≠ i and b ≠ j, x b = 0
              have h_xb_zero : x b = 0 := h_zeros b h_b_ne_i h_b_ne_j
              rw [h_xb_zero]
              simp
            -- Ensure i is in the filtered set
            · intro h_contra
              exfalso
              have h_i_mem : i ∈ univ.filter (λ b => b > j) := by
                apply mem_filter.mpr
                exact ⟨mem_univ i, h_gt⟩
              exact h_contra h_i_mem
          -- For a ≠ j, the outer sum terms are zero
          · intros a ha ha_ne
            rw [sum_eq_zero]
            intros b hb
            -- Since a ≠ j, consider cases
            by_cases ha_eq_i : a = i
            -- Case when a = i
            case pos =>
              -- b > a implies b > i
              #check mem_filter.mp hb
              have h_b_gt_i : b > i := by
                rw [← ha_eq_i]
                apply (mem_filter.mp hb).2
              -- Since b > i and x b ≠ 0 only when b = i or b = j, and b ≠ i
              have h_b_ne_i : b ≠ i := ne_of_gt h_b_gt_i
              by_cases hb_eq_j : b = j
              -- Subcase when b = j
              case pos =>
                -- b = j, a = i, but b > a requires j > i, which contradicts h_gt
                exfalso
                have contra_j_gt_i : i < j := by
                  rw [← hb_eq_j]
                  rw [← gt_iff_lt]
                  exact h_b_gt_i
                exact lt_asymm contra_j_gt_i h_gt
              case neg =>
                -- Subcase when b ≠ j Then x b = 0
                have h_xb_zero : x b = 0 := h_zeros b h_b_ne_i hb_eq_j
                rw [h_xb_zero]
                simp
            case neg =>
              have h_xa_zero : x a = 0 := h_zeros a ha_eq_i ha_ne
              rw [h_xa_zero]
              simp
          · intro h_contra
            exfalso
            have h_j_in_univ : j ∈ univ := mem_univ j
            exact h_contra h_j_in_univ
        have h_lt_or_gt : i < j ∨ i > j := lt_or_gt_of_ne h_ij_ne
        by_cases hij_ineq : i < j
        #check h_sum_eq_lt
        case pos =>
          exact h_sum_eq_lt hij_ineq
        case neg =>
          have i_gt_j: i > j := by
            rw [gt_iff_lt]
            have j_lteq_i: j ≤ i := by
              rw [← not_lt]
              exact hij_ineq
            #check lt_of_le_of_ne
            apply lt_of_le_of_ne j_lteq_i h_ij_ne.symm
          exact h_sum_eq_gt i_gt_j
      rw [h_sum]
      calc
        x i * x j * (x i ^ 2 + x j ^ 2) = s * x j * (s^2 + x j ^ 2):= by
          ring
        _ = s * x i * (s^2 + x i ^ 2) := by
          rw [h_x_eq]
        _ = s * s * (s^2 + s ^ 2) := by
          ring
    rw [h_simplify, h_sum]
    simp
    rw [mul_pow]
    ring
  -- Combine the above steps to complete the proof
  exact ⟨1/8, rfl, h_inequality, backward_dir⟩


theorem complete_least_constant_inequality (n : Nat) (hn : n ≥ 2) :
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
  sorry
