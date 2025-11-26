open Std

variable {α : Type} [LE α] [DecidableLE α]

def stalinSort (l : List α) : List α :=
  match l with
  | [] => []
  | [x] => [x]
  | x :: y :: xs =>
    if x ≤ y then
      x :: stalinSort (y :: xs)
    else
      stalinSort (x :: xs)

theorem starlinSort_cons (x : α) (xs : List α) : ∃ xs', stalinSort (x :: xs) = x :: xs' := by
  generalize h : x :: xs = l
  fun_induction stalinSort l generalizing x xs <;> simp_all

theorem starlinSort_cons' {x : α} {xs : List α} : stalinSort (x :: xs) = x :: (starlinSort_cons x xs).choose :=
  (starlinSort_cons x xs).choose_spec

theorem stalinSort_sorted [IsPreorder α] (l : List α) : (stalinSort l).Pairwise (· ≤ ·) := by
  fun_induction stalinSort l
  next => simp
  next => simp
  next x y xs le ih =>
    simp only [List.pairwise_cons, ih, and_true]
    intro x' h
    rw [starlinSort_cons'] at h ih
    simp only [List.mem_cons] at h
    cases h with
    | inl eq => exact eq ▸ le
    | inr mem => exact IsPreorder.le_trans _ _ _ le (List.rel_of_pairwise_cons ih mem)
  next x y xs nle ih => exact ih
