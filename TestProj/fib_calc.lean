import Mathlib.Logic.Function.Iterate

def fib : Nat → Nat
| 0 => 0
| 1 => 1
| (n + 2) => fib (n + 1) + fib n

def fib_aux : Nat → Nat → Nat → Nat
| a, _, 0 => a
| a, b, (n + 1) => fib_aux b (a + b) n

def fib2 (n : Nat) : Nat := fib_aux 0 1 n

def fib_aux_2 (a : Nat) (b : Nat) (n : Nat) : Nat := ((fun p : Nat × Nat => (p.snd, p.fst + p.snd))^[n] (a, b)).fst

theorem fib_aux_eq : fib_aux a b n = fib_aux_2 a b n := by
  cases n
  . unfold fib_aux
    unfold fib_aux_2
    simp
  . unfold fib_aux
    unfold fib_aux_2
    rw [Function.iterate_succ_apply, fib_aux_eq]
    unfold fib_aux_2
    rfl

theorem fib_aux_2_add_two : fib_aux_2 0 1 (n + 2) = fib_aux_2 0 1 (n + 1) + fib_aux_2 0 1 n := by
  unfold fib_aux_2
  simp [Function.iterate_succ_apply']
  rw [Nat.add_comm]

theorem fib2_add_two : fib2 (n + 2) = fib2 (n + 1) + fib2 n := by
  unfold fib2
  simp [fib_aux_eq]
  exact fib_aux_2_add_two

theorem fib_eq (n : Nat) : fib2 n = fib n := by
  match n with
  | 0 => decide
  | 1 => decide
  | x + 2 => unfold fib
             simp [← fib_eq]
             exact fib2_add_two
