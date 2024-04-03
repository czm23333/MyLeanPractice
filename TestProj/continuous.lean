import Mathlib.Data.Real.Basic
import Mathlib.Init.Set

/-
Continuous function
A function f(x) is said to be continuous at x = a if, for any ε > 0,
there is δ > 0 s.t. |f(x) - f(a)| < ε whenever |x - a| < δ
-/

def continuous_at (f : ℝ → ℝ) (a : ℝ) :=
∀ ε > 0, ∃ δ > 0, ∀ x, abs (x - a) < δ → abs (f x - f a) < ε

-- Suppose f(x) is continuous at x = a and f(a) > 0. Then there is an
-- open interval containing a s.t. f(x) > 0 over the whole interval
def SUBMISSION := ∀ f a, continuous_at f a → f a > 0 → ∃ b c : ℝ, a ∈ Set.Ioo b c ∧ ∀ x ∈ Set.Ioo b c, f x > 0

theorem continuous_function_about_an_open_interval : SUBMISSION := by
  intros f x fC gZ
  let y := f x
  let exNei := fC y gZ
  let δ := Classical.choose exNei
  let δp := Classical.choose_spec exNei
  apply Exists.intro (x - δ)
  apply Exists.intro (x + δ)
  apply And.intro
  . simp
    exact δp.left
  . intro x₁ x₁p
    simp at x₁p
    conv at x₁p =>
      congr
      . rw [sub_lt_iff_lt_add, add_comm, ← sub_lt_iff_lt_add]
      . rw [add_comm, ← sub_lt_iff_lt_add]
    rw [And.comm] at x₁p
    rw [← abs_sub_lt_iff] at x₁p
    let δpr := δp.right x₁ x₁p
    rw [abs_sub_lt_iff] at δpr
    let δprr := δpr.right
    simp at δprr
    simp
    assumption
