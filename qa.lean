import Mathlib
open Finset
open BigOperators

#check sum_add_distrib
theorem sum_split {n : ℕ} (hn : n ≥ 2) (x : Fin n → ℝ) (h_nonneg : ∀ i : Fin n, x i ≥ 0) :
  ∑ i : Fin n, ∑ j ∈ filter (fun j => j ≠ i) univ, x i * x j =
  ∑ i : Fin n, ∑ j ∈ filter (fun j => j < i) univ, x i * x j +
    ∑ i : Fin n, ∑ j ∈ filter (fun j => i < j) univ, x i * x j := by
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
