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
                  conv =>
                    rhs
                    rw [Nat.succ_mul, Nat.mul_succ]
                    rw [← Nat.add_one]
                    repeat rw [← Nat.add_assoc]
                    rw [Nat.add_assoc]
                    simp
                    repeat rw [Nat.add_assoc]
                    rw [← Nat.add_assoc _ _ 2]
                    rw [Nat.add_comm]
                    conv =>
                      repeat arg 1
                      rw [← Nat.mul_one k]
                    rw [← Nat.mul_succ _ 1]
                    simp
                    rw [← Nat.mul_comm]
                    conv =>
                      arg 1
                      arg 2
                      rw [← Nat.mul_one 2]
                    rw [← Nat.left_distrib]
                    rw [← Nat.right_distrib]
                  rw [← Nat.add_one]
                  rw [← Nat.right_distrib]

theorem nicomachus : SUBMISSION := by
  intros n
  cases n
  . simp
    unfold fsum
    simp
  . unfold fsum
    simp
    rw [← nicomachus]
    conv =>
      lhs
      repeat rw [Nat.pow_succ]
      rw [Nat.pow_zero]
      simp
      repeat rw [Nat.left_distrib, Nat.right_distrib]
      rw [Nat.right_distrib]
      rw [← Nat.add_assoc]
      rw [Nat.mul_comm (Nat.succ _) (fsum id _)]
    conv =>
      lhs
      arg 2
      conv =>
        arg 1
        rw [← Nat.one_mul (fsum id _)]
      rw [← Nat.pow_zero]
      repeat rw [← Nat.pow_succ]
      simp
    conv =>
      congr
      . rw [Nat.add_comm _ (fsum id _ ^ 2)]
      . rw [Nat.add_comm _ (fsum id _ ^ 2)]
    apply congrArg (Nat.add (fsum id _ ^2))
    unfold cb
    rw [Nat.add_assoc]
    conv =>
      lhs
      arg 2
      arg 1
      rw [← Nat.one_mul (fsum id _ * Nat.succ _)]
    rw [← Nat.succ_mul]
    simp
    rw [← Nat.mul_assoc]
    rw [id_sum_lemma]
    rw [← Nat.right_distrib]
    rw [Nat.pow_succ]
    conv =>
      congr
      . rw [Nat.mul_comm]
      . rw [Nat.mul_comm]
    apply congrArg (Nat.mul _)
    rw [Nat.add_one]
    repeat rw [Nat.pow_succ]
    rw [Nat.pow_zero, Nat.one_mul]
    rw [Nat.succ_mul]
    rw [Nat.add_comm]
