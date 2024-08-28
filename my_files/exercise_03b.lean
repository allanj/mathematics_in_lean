import Mathlib
import Mathlib.Tactic
import Mathlib.Util.Delaborators
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Card

open Real

/-
The natural language description for ex20240822b is:
```text
The set of all prime numbers that is greater than 2 is a subset of all odd numbers.
```

Translate the problem to Lean code starting with
```Lean4
theorem ex20240822b ...
```
and then complete the proof.

Requirements:
* You have to use the set-builder {x | SomePredicate x} in the problem statement.
  - Note there are other set builders as given here: https://github.com/leanprover-community/mathlib4/blob/22e3994a32b5b88e8d81124b3e4ee1accbd00bd6/Mathlib/Data/Set/Defs.lean#L17-L24
* You are free to use any theorem that is built-in or from mathlib4.

-/

-- example : { n | Nat.Prime n } ∩ { n | n > 2 } ⊆ { n | ¬Even n } := by
#check Nat.Prime.odd_of_ne_two
#check Nat.lt_irrefl
theorem ex20240822b : {p : ℕ | Nat.Prime p ∧ p > 2} ⊆ {n : ℕ | Odd n} := by
  -- We start by introducing an arbitrary element of the left-hand set
  intro p
  intro hp

  -- We now have p : ℕ and hp : Nat.Prime p ∧ p > 2
  -- Let's break down the conjunction
  have prime_p : Nat.Prime p := hp.left
  have p_gt_2 : p > 2 := hp.right

  -- Now we need to show that p is in the right-hand set, i.e., p is odd
  -- We can use the fact that all primes greater than 2 are odd
  have p_odd : Odd p := by
    -- We can use Nat.Prime.odd_of_ne_two
    apply Nat.Prime.odd_of_ne_two prime_p
    -- Now we need to show p ≠ 2
    intro p_eq_2
    -- If p were 2, it would contradict p > 2
    rw [p_eq_2] at p_gt_2
    -- 2 > 2 is false
    exact Nat.lt_irrefl 2 p_gt_2

  -- Now we have shown that p is odd, so it's in the right-hand set
  exact p_odd
