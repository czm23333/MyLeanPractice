import Mathlib.Algebra.Group.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Fintype.Card

open Classical

universe lv
variable {G : Type lv}
variable [Group G]

theorem g_e_unique : ∀ e₁ : G, e₁ ≠ 1 → ¬ (∀ x : G, (e₁ * x = x ∧ x * e₁ = x)) := by
  intros e₁ neq idp
  have eq₁ := And.left (idp 1)
  have eq₂ := mul_one e₁
  rewrite [eq₁] at eq₂
  apply Ne.elim; exact neq
  apply Eq.symm; exact eq₂

theorem g_inv_l_unique : ∀ x : G, ∀ inv₁ : G, inv₁ ≠ x⁻¹ → ¬ (inv₁ * x = 1) := by
  intros x inv₁ neq invp
  apply Ne.elim; exact neq
  have eq₂ := congrArg (· * x⁻¹) invp; simp at eq₂; exact eq₂

theorem g_inv_r_unique : ∀ x : G, ∀ inv₁ : G, inv₁ ≠ x⁻¹ → ¬ (x * inv₁ = 1) := by
  intros x inv₁ neq invp
  apply Ne.elim; exact neq
  have eq₂ := congrArg (x⁻¹ * ·) invp; simp at eq₂; exact eq₂

theorem add_le_cases : ∀ n m p q : Nat, n + m ≤ p + q → n ≤ p ∨ m ≤ q := by
  intros n m p q pr
  apply byContradiction
  intro npr
  rw [not_or, Nat.not_le, Nat.not_le] at npr
  have neq := Nat.add_lt_add npr.left npr.right
  rw [← Nat.not_lt] at pr
  exact pr neq

theorem g_finite_element_order_mul_index : [Fintype G] → (x : G) → (Nat.card G) % (orderOf x) = 0 := by
  intros fin x
  have fo := isOfFinOrder_of_finite x
  let ps := Submonoid.powers x
  let sg : Subgroup G := {
    carrier := ps.carrier
    mul_mem' := ps.mul_mem
    one_mem' := ps.one_mem
    inv_mem' := by
      intro y; simp; intro inps
      rw [Submonoid.mem_powers_iff] at inps; rw [isOfFinOrder_iff_pow_eq_one] at fo
      have np := choose_spec inps
      let n2 := choose fo; have n2p := choose_spec fo; simp [Nat.lt_iff_add_one_le] at n2p
      have eq₁ : y ^ n2 = 1 := by rw [← np, ← pow_mul', pow_mul, n2p.right, one_pow]
      let inv := y ^ (n2 - 1)
      have eq₂ : inv * y = 1 := by
        conv => lhs; arg 2; rw [← pow_one y]
        rw [← pow_add _ _ _, Nat.sub_add_cancel, eq₁]
        exact n2p.left
      have pf₃ : inv ∈ ps := by
        rw [Submonoid.mem_powers_iff]; unfold inv; rw [← np, ← pow_mul]; simp
      have pf₄ : inv = y⁻¹ := by
        apply byContradiction; intro neq; exact @g_inv_l_unique G _ y inv neq eq₂
      rw [← pf₄]; exact pf₃
  }
  have sizeEq : Nat.card ps = Nat.card sg := by
    rw [Finite.card_eq]
    let equ : Equiv ↥ps ↥sg := { toFun := id, invFun := id, left_inv := Eq.refl, right_inv := Eq.refl }
    apply Nonempty.intro; exact equ
  rw [← Subgroup.index_mul_card sg, ← sizeEq, ← Nat.card_submonoidPowers]
  unfold ps
  simp

example : {T : Type} → {P : T → Prop} → {Q : T → Prop} → (∀ x, ¬ P x → Q x) → (∀ x, ¬ Q x) → (∀ x, P x) := by
  intros _ P _ h₁ h₂ x
  apply byContradiction
  intro nh
  apply h₂ x
  apply h₁ x
  exact nh
