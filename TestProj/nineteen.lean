import Init.Data.Nat.Dvd
import Mathlib.Data.Nat.Prime
import Mathlib.Logic.Basic
import Mathlib.Tactic.FinCases

theorem nineteen_dvd (a : Nat) : 19 ∣ a ↔ 19 ∣ 4 * a := by
  apply Iff.intro
  . let tmp := Nat.dvd_mul_left a 4
    intro ntd
    exact Nat.dvd_trans ntd tmp
  . intro ntfd
    let tmp : Nat.Prime 19 := by decide
    let tmp2 := (Prime.dvd_mul (Nat.Prime.prime tmp)).mp ntfd
    match tmp2 with
    | Or.inl fp => exfalso
                   norm_num at fp
    | Or.inr ap => assumption

theorem nineteen_dvd' (a b : Nat) : 19 ∣ 100 * a + b ↔ 19 ∣ a + 4 * b := by
  apply Iff.intro
  all_goals intro dvd1
  all_goals rw [Nat.dvd_iff_mod_eq_zero] at dvd1
  all_goals rw [Nat.add_mod, Nat.mul_mod] at dvd1
  all_goals simp at dvd1
  all_goals rw [Nat.dvd_iff_mod_eq_zero]
  all_goals rw [Nat.add_mod, Nat.mul_mod] at dvd1
  all_goals rw [Nat.add_mod, Nat.mul_mod]
  all_goals let ntgez : 19 > 0 := by simp
  all_goals let αlt := @Nat.mod_lt a 19 ntgez
  all_goals let βlt := @Nat.mod_lt b 19 ntgez
  all_goals generalize αh : a % 19 = α at dvd1
  all_goals generalize βh : b % 19 = β at dvd1
  all_goals simp; simp at dvd1
  all_goals rw [αh] at αlt; rw [βh] at βlt
  all_goals let αin := (@Finset.mem_range 19 α).mpr αlt
  all_goals let βin := (@Finset.mem_range 19 β).mpr βlt
  all_goals fin_cases αin
  all_goals fin_cases βin
  all_goals simp at dvd1
  all_goals simp
