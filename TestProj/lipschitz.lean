import Mathlib.Data.Real.Basic
import Mathlib.Tactic
open Classical

/-
  Uniform continuity
  A function f(x) is said to be uniform continuous if it is continuous
  with the additional condition that the choice of δ depends on ε only
-/
def uniform_continuous (f : ℝ → ℝ) :=
  ∀ ε > 0, ∃ δ > 0, ∀ x y, |x - y| < δ → |f x - f y| < ε

/-
  Lipschitz functions
  A function f(x) is said to be Lipschitz if there is L s.t.
  |f(x) - f(y)| ≤ L|x - y| for any x, y.
-/
def lipschitz (f : ℝ → ℝ) :=
  ∃ L > 0, ∀ x y, |f x - f y| ≤ L * |x - y|

-- All Lipschitz functions are uniform continuous
def SUBMISSION := ∀ f, lipschitz f → uniform_continuous f

theorem uniform_continuous_of_lipschitz {f} (hf : lipschitz f) :
  uniform_continuous f := by
  let L := choose hf
  have Lspec := choose_spec hf
  intro ε εg
  use ε / L
  constructor
  simp [εg, L, Lspec.left]
  intro x y dl
  apply lt_of_lt_of_le'
  have : L * |x - y| < ε := by
    have : ε = L * (ε / L) := by
      field_simp
      rw [div_self]
      simp [L, ne_of_gt Lspec.left]
    rw [this]
    apply mul_lt_mul'
    trivial
    assumption
    simp [abs_nonneg]
    exact Lspec.left
  assumption
  exact Lspec.right x y
