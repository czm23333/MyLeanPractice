import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.OrderOfElement

open Classical

variable {T : Type}

theorem P1 : [Semigroup T] → (A : Set T) → (B : Set T) → (∀ x : T, (x ∈ A ∨ x ∈ B) ∧ ¬(x ∈ A ∧ x ∈ B)) → (∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, a * b * c ∈ A) → (∀ a ∈ B, ∀ b ∈ B, ∀ c ∈ B, a * b * c ∈ B) → (∀ a ∈ A, ∀ b ∈ A, a * b ∈ A) ∨ (∀ a ∈ B, ∀ b ∈ B, a * b ∈ B) := by
  intros _ A B parp amulp bmulp
  by_contra con
  rw [not_or] at con
  repeat rw [not_forall] at con
  simp at con

  let conl := con.left
  let a₁ := choose conl
  let a₁p := choose_spec conl
  let b₁ := choose a₁p.right
  let b₁p := choose_spec a₁p.right
  let c₁ := a₁ * b₁
  let c₁p : c₁ ∉ A := b₁p.right
  let conr := con.right
  let a₂ := choose conr
  let a₂p := choose_spec conr
  let b₂ := choose a₂p.right
  let b₂p := choose_spec a₂p.right
  let c₂ := a₂ * b₂
  let c₂p : c₂ ∉ B := b₂p.right

  let c₁b : c₁ ∈ B := by
    apply Or.resolve_left (parp c₁).left
    exact c₁p
  let c₂a : c₂ ∈ A := by
    apply Or.resolve_right (parp c₂).left
    exact c₂p

  let mulb : c₁ * a₂ * b₂ ∈ B := bmulp c₁ c₁b a₂ a₂p.left b₂ b₂p.left
  let mula : c₁ * a₂ * b₂ ∈ A := by
    rw [mul_assoc]
    apply amulp
    exact a₁p.left
    exact b₁p.left
    exact c₂a

  apply (parp (c₁ * a₂ * b₂)).right
  apply And.intro
  exact mula
  exact mulb

theorem P9 : [Group T] → (∀ x : T, orderOf x ≠ 2) → (∀ x : T, ∀ y : T, (x * y)^2 = (y * x)^2) → ∀ x : T, ∀ y : T, x * y = y * x := by
  intros _ n2order commsq x y
  have sqcomm : ∀ x : T, ∀ a : T, x^2 * a = a * x^2 := by
    intros x a
    let b := a⁻¹ * x
    let abx : a * b = x := by unfold b; simp
    let tmp := commsq a b
    simp [abx, pow_two, mul_assoc] at tmp
    simp [pow_two, mul_assoc]
    let tmp2 := congrArg (λ x => a * x) tmp
    unfold b at tmp2
    simp [mul_assoc] at tmp2
    apply Eq.symm
    exact tmp2
  let a := x * y
  let b := y * x
  let tmp3 : a * a * b⁻¹ * a = a * b := by
    simp [← pow_two]
    rw [sqcomm]
    rw [pow_two]
    simp [mul_assoc]
    unfold a; unfold b; simp
    apply_fun (λ H => y * x * H); dsimp
    simp [mul_assoc]; simp [← mul_assoc]
    rw [mul_assoc y x x, ← pow_two, ← sqcomm, pow_two]
    rw [mul_assoc _ y y, ← pow_two y, mul_assoc _ (y ^ 2) x, sqcomm, pow_two]; simp [← mul_assoc]
    rw [mul_assoc x x y]
    conv => rhs; rw [mul_assoc _ x y, mul_assoc, ← pow_two, ← sqcomm, pow_two]; simp [← mul_assoc]
    intro α β feq
    simp at feq
    assumption
  let tmp2 : (a * b⁻¹)^2 = 1 := by
    rw [pow_two]
    let eq1 : a⁻¹ * (a * a * b⁻¹ * a) * b⁻¹ = a⁻¹ * (a * b) * b⁻¹ := congrArg (λ hr => a⁻¹ * hr * b⁻¹) tmp3
    repeat rw [← mul_assoc a⁻¹] at eq1
    repeat rw [mul_assoc] at eq1
    simp at eq1
    repeat rw [← mul_assoc] at eq1
    simp [← mul_assoc]
    unfold a
    conv at eq1 => rhs; unfold b; simp [mul_assoc]
    simp [← mul_assoc]
    assumption
  let tmp : a * b⁻¹ = 1 := by
    by_contra con
    let oeq : orderOf (a * b⁻¹) = 2 := by
      apply orderOf_eq_prime
      exact tmp2
      exact con
    apply n2order (a * b⁻¹)
    exact oeq
  let res : a * b⁻¹ * b = 1 * b := congrArg (λ hr => hr * b) tmp
  simp at res
  assumption
