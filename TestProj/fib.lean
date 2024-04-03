import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic.Ring.Basic

noncomputable def phi : ℝ := (1 + Real.sqrt 5) / 2

noncomputable def psi : ℝ := (1 - Real.sqrt 5) / 2

def SUBMISSION := ∀ n : ℕ, (Nat.fib n : ℝ) = (phi^n - psi^n) / Real.sqrt 5

def fib_calc : SUBMISSION := by
  intro n
  match n with
  | 0 => simp
  | 1 => simp
         unfold phi
         unfold psi
         rw [div_sub_div_same]
         simp
  | k@(m+2) => simp
               rw [Nat.fib_add_two]
               simp
               repeat rw [fib_calc]
               rw [div_add_div_same]
               apply congrArg (λ x => x / (Real.sqrt 5))
               repeat rw [pow_succ]
               generalize phi^m = a
               generalize psi^m = b
               unfold phi
               unfold psi
               repeat rw [← mul_assoc]
               repeat rw [div_mul_div_comm]
               repeat rw [left_distrib, mul_sub_left_distrib]
               repeat rw [right_distrib, mul_sub_right_distrib]
               simp
               ring
