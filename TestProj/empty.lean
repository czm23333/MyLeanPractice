inductive BTree : Type
| Leaf        : BTree
| Single_Son  : BTree -> BTree
| Binary_Sons : BTree -> BTree -> BTree

open BTree

def node : BTree → Nat
| Leaf                => 1
| (Single_Son t')     => 1 + node t'
| (Binary_Sons t1 t2) => 1 + node t1 + node t2

def empty_place : BTree → Nat
| Leaf                => 2
| (Single_Son t')     => 1 + empty_place t'
| (Binary_Sons t1 t2) => empty_place t1 + empty_place t2

theorem l (t n) (H : node t = n) : empty_place t = n + 1 := by
  cases t
  . unfold empty_place
    simp
    rw [← H]
    unfold node
    simp
  . unfold empty_place
    rw [l _ (node _) (Eq.refl _)]
    unfold node at H
    rw [Nat.add_comm n 1, Nat.add_comm _ 1, H]
  . unfold empty_place
    repeat rw [l _ (node _) (Eq.refl _)]
    unfold node at H
    rw [← Nat.add_assoc, Nat.add_comm (node _) 1, H]
