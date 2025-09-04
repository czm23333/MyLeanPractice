import Mathlib.Logic.Basic

inductive formula : Type
| atom (n : Nat) | true_f | false_f | or_f (α β : formula) | and_f (α β : formula) | not_f (α : formula)

open formula

def eval : (Nat → Bool) → formula → Bool
| m, (atom v)    => m v
| _, true_f      => true
| _, false_f     => false
| m, (or_f α β)  => eval m α || eval m β
| m, (and_f α β) => eval m α && eval m β
| m, (not_f α)   => ! (eval m α)

def dual : formula → formula
| (atom v)    => atom v
| true_f      => false_f
| false_f     => true_f
| (or_f α β)  => and_f (dual α) (dual β)
| (and_f α β) => or_f (dual α) (dual β)
| (not_f α)   => not_f (dual α)

def SUBMISSION : Prop := ∀ (f : formula), (∀ m, eval m f = true) → ∀ n, eval n (dual f) = false

def fneg (f : Nat → Bool) : Nat → Bool := λ x => ! f x

theorem neg_neg_eq_id : fneg (fneg f) = f := by
  unfold fneg
  simp

theorem dual_neg_eq_neg : eval (fneg m) (dual f) = ! eval m f := by
  unfold dual
  unfold eval
  match f with
  | atom n => simp
              unfold fneg
              simp
  | true_f => simp
  | false_f => simp
  | not_f α => simp
               rw [dual_neg_eq_neg]
  | or_f α β => simp
                repeat rw [dual_neg_eq_neg]
  | and_f α β => simp
                 repeat rw [dual_neg_eq_neg]

theorem tt_dual_ff : SUBMISSION := by
  intros f tt
  match f with
  | atom n => unfold dual
              unfold eval
              unfold eval at tt
              exfalso
              let tmp : ¬(∀ (m : Nat → Bool), m n = true) := by
                rw [not_forall]
                simp
                apply Exists.intro (λ _ => false)
                simp
              exact tmp tt
  | true_f => unfold dual
              unfold eval
              simp
  | false_f => unfold eval at tt
               exfalso
               simp at tt
  | or_f α β => unfold dual
                unfold eval
                unfold eval at tt
                intro n
                let ttp := tt (fneg n)
                rw [← @neg_neg_eq_id n]
                repeat rw [dual_neg_eq_neg]
                rw [← Bool.not_or]
                simp
                simp at ttp
                have ttpr := ttp.resolve_left
                simp at ttpr
                assumption

  | and_f α β => unfold dual
                 unfold eval
                 unfold eval at tt
                 intro n
                 let ttp := tt (fneg n)
                 rw [← @neg_neg_eq_id n]
                 repeat rw [dual_neg_eq_neg]
                 rw [← Bool.not_and]
                 simp
                 simp at ttp
                 assumption
  | not_f α => unfold dual
               unfold eval
               unfold eval at tt
               intro n
               let ttp := tt (fneg n)
               rw [← @neg_neg_eq_id n]
               rw [dual_neg_eq_neg]
               simp
               simp at ttp
               assumption
