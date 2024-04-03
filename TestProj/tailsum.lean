def sum_simple (f : Nat → Nat) : Nat → Nat
| 0              => f 0
| n@(Nat.succ m) => f n + sum_simple f m

def sum_aux : Nat → (Nat → Nat) → Nat → Nat
| a, f, 0              => f 0 + a
| a, f, n@(Nat.succ m) => sum_aux (f n + a) f m

def sum_tail := sum_aux 0

theorem sum_aux_expand : sum_aux m f n = m + sum_tail f n := by
  cases n
  . unfold sum_tail
    unfold sum_aux
    simp
    rw [Nat.add_comm]
  . unfold sum_tail
    unfold sum_aux
    simp
    repeat rw [sum_aux_expand]
    conv =>
      rhs
      rw [← Nat.add_assoc]
      rw [Nat.add_comm m]

theorem sum_eq (f n) : sum_tail f n = sum_simple f n := by
  cases n
  . unfold sum_tail
    unfold sum_aux
    unfold sum_simple
    simp
  . unfold sum_tail
    unfold sum_aux
    unfold sum_simple
    simp
    rw [sum_aux_expand]
    rw [sum_eq]
