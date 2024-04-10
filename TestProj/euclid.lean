import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic.Basic

def gcd_steps (a y : Nat) : Nat :=
  if a = 0 then 0
  else 1 + gcd_steps (y % a) a
termination_by a
decreasing_by
  simp_wf
  rename_i h
  exact @Nat.mod_lt y a (Nat.ne_zero_iff_zero_lt.mp h)

theorem fib_euclid_step : ∀ n > 0, gcd_steps (Nat.fib (n + 1)) (Nat.fib (n + 2)) = n := by
  intros n np
  match n with
  | 0 => simp at np
  | 1 => decide
  | 2 => decide
  | tp + 2 => conv => lhs; arg 2; rw [Nat.fib_add_two]
              unfold gcd_steps; simp
              let tpptgt : 2 ≤ tp + 2 := by simp
              let tmp := Nat.mod_eq_of_lt $ Nat.fib_lt_fib_succ tpptgt
              rw [tmp]
              rw [fib_euclid_step]
              rw [← add_assoc, add_comm 1 tp, add_assoc]
              simp

theorem euclid_not_constant : ∀ n, ∃ a b, gcd_steps a b = n := by
  intro n
  match n with
  | 0 => apply Exists.intro 0
         apply Exists.intro 0
         decide
  | k@(Nat.succ x) => apply Exists.intro $ Nat.fib (k + 1)
                      apply Exists.intro $ Nat.fib (k + 2)
                      rename_i h
                      let tmp : k > 0 := by rw [h]; simp
                      simp
                      rw [fib_euclid_step k tmp]
                      assumption
