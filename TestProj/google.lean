universe u

inductive mytree (A : Type u) : Type u where
| leaf : A → mytree A
| branch : A → mytree A → mytree A → mytree A

def flip_mytree {A : Type u} : mytree A → mytree A
| t@(mytree.leaf _)     => t
| (mytree.branch a l r) => mytree.branch a (flip_mytree r) (flip_mytree l)

theorem flip_flip {A : Type u} {t : mytree A} : flip_mytree (flip_mytree t) = t := by
  cases t
  . unfold flip_mytree
    unfold flip_mytree
    simp
  . conv =>
      lhs
      arg 1
      unfold flip_mytree
    unfold flip_mytree
    repeat rw [flip_flip]
