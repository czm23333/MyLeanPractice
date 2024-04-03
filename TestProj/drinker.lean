import Mathlib.Logic.Basic

universe u

theorem drinker {α : Type u} (r : α → Prop) {ne : Nonempty α} : ∃ x, (r x → ∀ y, r y) := by
  let forall_tf := Classical.em (∀ x, r x)
  match forall_tf with
  | Or.inl tall => let a := Classical.choice ne
                   let imp := λ _ : r a => tall
                   exact Exists.intro a imp
  | Or.inr fall => rw [not_forall] at fall
                   let a := Classical.choose fall
                   let nra := Classical.choose_spec fall
                   let imp : r a → ∀ (y : α), r y := by
                     intro ra
                     exfalso
                     exact nra ra
                   exact Exists.intro a imp
