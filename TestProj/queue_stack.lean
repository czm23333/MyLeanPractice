import Mathlib.Tactic

universe u

def Stack (α: Type u) := List α

structure Costly (α: Type u) where
  mk ::
  content: α
  cost: Nat

instance : Monad Costly where
  pure v := Costly.mk v 0
  bind res next :=
    let nextRes := next res.content
    Costly.mk nextRes.content (res.cost + nextRes.cost)

def Stack.try_pop (stk: Stack α) : Costly (Stack α × Option α) :=
  match stk with
  | [] => Costly.mk (stk, none) 1
  | top::left => Costly.mk (left, top) 1

def Stack.push (stk: Stack α) (elem: α) : Costly (Stack α) :=
  Costly.mk (elem::stk) 1

structure Queue (α: Type u) where
  mk ::
  stk1: Stack α
  stk2: Stack α

def Queue.push (queue: Queue α) (elem: α) : Costly (Queue α) :=
  let push1 := queue.stk1.push elem
  Costly.mk (Queue.mk push1.content queue.stk2) push1.cost

def swap_aux (stk1 stk2: Stack α) : Costly (Queue α) :=
  let pop1 := stk1.try_pop
  match h : pop1.content.snd with
  | some top =>
    let push2 := stk2.push top
    let res := swap_aux pop1.content.fst push2.content
    Costly.mk res.content (pop1.cost + push2.cost + res.cost)
  | none => Costly.mk (Queue.mk stk1 stk2) pop1.cost
termination_by stk1.length
decreasing_by
  match hs : stk1 with
  | [] =>
      exfalso
      simp [pop1, hs, Stack.try_pop] at h
  | _::left =>
      simp [Stack.try_pop]

def Queue.swap (queue: Queue α) : Costly (Queue α) :=
  swap_aux queue.stk1 queue.stk2

def Queue.try_pop (queue: Queue α) : Costly (Queue α × Option α) :=
do
  let pop2 <- queue.stk2.try_pop
  match pop2.snd with
  | some front => return (Queue.mk queue.stk1 pop2.fst, front)
  | none =>
    let queue' <- queue.swap
    let pop2' <- queue'.stk2.try_pop
    return (Queue.mk queue'.stk1 pop2'.fst, pop2'.snd)


-- Single op costs
theorem stack_push_const_cost : ∀ s: Stack α, ∀ e: α, (s.push e).cost = 1 :=
by
  intros
  unfold Stack.push; simp

theorem queue_push_const_cost : ∀ q: Queue α, ∀ e: α, (q.push e).cost = 1 :=
by
  intros
  unfold Queue.push; simp
  apply stack_push_const_cost

theorem swap_aux_size_cost : ∀ s1 s2: Stack α, (swap_aux s1 s2).cost = s1.length * 2 + 1 :=
by
  intro s1 _
  unfold swap_aux Stack.try_pop; simp
  cases s1
  all_goals simp
  rw [swap_aux_size_cost, stack_push_const_cost]
  linarith

theorem swap_aux_empty_s1 : ∀ s1 s2: Stack α, (swap_aux s1 s2).content.stk1 = [] :=
by
  intros s1 _
  unfold swap_aux Stack.try_pop; simp
  cases s1
  all_goals simp
  rw [swap_aux_empty_s1]

theorem queue_swap_size_cost : ∀ q: Queue α, q.swap.cost = q.stk1.length * 2 + 1 :=
by
  intros
  unfold Queue.swap
  apply swap_aux_size_cost

theorem queue_swap_empty_s1 : ∀ q: Queue α, q.swap.content.stk1 = [] :=
by
  intros
  unfold Queue.swap
  apply swap_aux_empty_s1

theorem queue_pop_size_or_const_cost : ∀ q: Queue α,
  let { content := (q', _), cost := cost } := q.try_pop
  (q'.stk1 = q.stk1 ∧ cost = 1) ∨ (q'.stk1 = [] ∧ cost = q.stk1.length * 2 + 3)
:= by
  intro q
  simp [Queue.try_pop]
  cases q.stk2
  all_goals simp [bind, pure, Stack.try_pop]
  . right
    constructor
    . apply queue_swap_empty_s1
    . rw [queue_swap_size_cost]
      split
      all_goals simp; linarith


theorem queue_pop_overall_cost : ∀ q: Queue α,
  let { content := (q', _), cost := cost } := q.try_pop
  q'.stk1.length * 2 + cost ≤ q.stk1.length * 2 + 3
:= by
  intro q
  let h := queue_pop_size_or_const_cost q
  simp at h
  cases h
  all_goals rename_i sh
            simp [sh.left, sh.right]


-- Batch op
inductive QueueOp (α: Type u) where
| Push : (v: α) → QueueOp α
| Pop : QueueOp α


def QueueOp.apply {α: Type u} (op: QueueOp α) (q: Queue α) : Costly (Queue α) :=
  match op with
  | Push v => q.push v
  | Pop => Prod.fst <$> q.try_pop

def batch_apply (ops: List (QueueOp α)) (q: Queue α) : Costly (Queue α) :=
do
  match ops with
  | [] => return q
  | op::left =>
    let q' <- op.apply q
    batch_apply left q'

def batch_cost_empty (ops: List (QueueOp α)) : Nat :=
  (batch_apply ops (Queue.mk [] [])).cost


-- Batch op cost
theorem apply_overall_cost : ∀ op: QueueOp α, ∀ q: Queue α,
  let {content := q', cost := cost } := op.apply q
  q'.stk1.length * 2 + cost ≤ q.stk1.length * 2 + 3
:= by
  intro op _
  simp
  cases op
  all_goals simp [QueueOp.apply]
  . rw [queue_push_const_cost]
    simp [Queue.push, Stack.push]
    linarith
  . simp [Functor.map]
    apply queue_pop_overall_cost

theorem batch_apply_overall_cost : ∀ ops: List (QueueOp α), ∀ q: Queue α,
  let {content := q', cost := cost } := batch_apply ops q
  q'.stk1.length * 2 + cost ≤ q.stk1.length * 2 + ops.length * 3
:= by
  intro ops q
  cases ops
  . simp [batch_apply, pure]
  . rename_i op left
    let op_app := op.apply q
    have op_app_eq : op_app = op.apply q := rfl
    have cur := apply_overall_cost op q
    have sub := batch_apply_overall_cost left op_app.content
    simp [← op_app_eq] at cur
    simp at sub
    have overall := add_le_add sub cur

    simp [batch_apply, bind, ← op_app_eq]
    linarith [overall]

-- Amortized O(1)
theorem batch_cost_empty_linear : ∀ ops: List (QueueOp α), batch_cost_empty ops ≤ ops.length * 3 :=
by
  intro ops
  unfold batch_cost_empty
  have := batch_apply_overall_cost ops (Queue.mk [] [])
  simp at this
  linarith [this]
