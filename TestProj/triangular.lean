import Mathlib.Tactic

def fsum : (Nat → Nat) → Nat → Nat
| _, 0 => 0
| f, Nat.succ n => f (Nat.succ n) + fsum f n

def cb : Nat → Nat := λ n => n ^ 3

def SUBMISSION := ∀ n, (fsum id n) ^ 2 = fsum cb n

theorem id_sum_lemma : ∀ n, 2 * fsum id n = n * (n + 1) := by
  intros n
  match n with
  | 0 => simp
         unfold fsum
         rfl
  | Nat.succ k => unfold fsum
                  rw [Nat.left_distrib]
                  rw [id_sum_lemma]
                  simp
                  ring

theorem nicomachus : SUBMISSION := by
  intros n
  cases n
  . unfold fsum
    simp
  . unfold fsum
    simp
    rw [← nicomachus]
    unfold cb
    ring_nf
    simp
    rw [mul_assoc]
    simp [mul_comm _ 2]
    rw [id_sum_lemma]
    ring
