def eval_poly (x : Nat) : List Nat → Nat
| []       => 0
| (an::cf) => eval_poly x cf + an * x ^ cf.length

def horner_loop : Nat → Nat → List Nat → Nat
| acc, _, []       => acc
| acc, x, (an::cf) => horner_loop (acc * x + an) x cf

def horner (x : Nat) (cf : List Nat) := horner_loop 0 x cf

def SUBMISSION : Prop := ∀ x cf, eval_poly x cf = horner x cf

theorem horner_expand : horner_loop 0 x tail + head * x ^ List.length tail = horner_loop head x tail := by
  intros
  cases tail
  . simp
    unfold horner_loop
    simp
  . simp
    unfold horner_loop
    simp
    rw [← horner_expand]
    conv =>
      rhs
      rw [← horner_expand]
    rw [Nat.add_assoc]
    congr
    simp [Nat.right_distrib, Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm, Nat.add_comm]

theorem horner_eq : SUBMISSION := by
  intros x cf
  cases cf
  . rfl
  . unfold eval_poly
    unfold horner
    unfold horner_loop
    simp
    rw [horner_eq]
    unfold horner
    exact horner_expand
