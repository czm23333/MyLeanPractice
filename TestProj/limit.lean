import Mathlib.Data.Real.Basic
open Classical

/-
Rigorous definition of a limit
For a sequence x_n, we say that \lim_{n \to \infty} x_n = l if
∀ ε > 0, ∃ N, n ≥ N → |x_n - l| < ε
-/

def lim_to_inf (x : ℕ → ℝ) (l : ℝ) := ∀ ε > 0, ∃ N, ∀ n ≥ N, |x n - l| < ε

-- Suppose \lim_{n\to\infty} x_n = l.
-- Then \lim_{n\to\infty} |x_n| = |l|.
def SUBMISSION := ∀ x l, lim_to_inf x l → lim_to_inf (λ n => |x n|) |l|

theorem lim_to_lim_abs : SUBMISSION := by
  intros x l lim ε εgz
  let tmp := lim ε εgz
  let N := Classical.choose tmp
  let Np := Classical.choose_spec tmp
  apply Exists.intro N
  simp
  simp at Np
  intro n np
  let Npn := Np n np
  let tmp2 := abs_abs_sub_abs_le (x n) l
  exact lt_of_le_of_lt tmp2 Npn

