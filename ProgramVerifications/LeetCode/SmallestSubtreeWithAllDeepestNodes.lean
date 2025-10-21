-- https://leetcode.com/problems/smallest-subtree-with-all-the-deepest-nodes/submissions/1807477914/
import Mathlib

variable {α : Type*}

instance [Repr α] : ToString (Tree α) where
  toString v := reprStr v

def Tree.ofArray (array : Array (Option α)) : Tree α :=
  go array 0
where
  go (array : Array (Option α)) (index : Nat) : Tree α :=
    match h : array[index]? with
    | .none => .nil
    | .some .none => .nil
    | .some (.some value) =>
      have : index < array.size := by grind
      have : array.size - (index * 2 + 1) < array.size - index := by grind
      .node value (go array (index * 2 + 1)) (go array (index * 2 + 2))
  termination_by array.size - index

def smallestSubtreeWithAllDeepestNodes (root : Tree α) : Tree α :=
  match root with
  | .nil => root
  | .node _value left right =>
    match Ord.compare (Tree.height left) (Tree.height right) with
    | .lt => smallestSubtreeWithAllDeepestNodes right
    | .eq => root
    | .gt => smallestSubtreeWithAllDeepestNodes left

def smallestSubtreeWithAllDeepestNodes' (root : Tree α) : Tree α :=
  (go root).1
where
  go (root : Tree α) : Tree α × Nat :=
    match root with
    | .nil => (.nil, 0)
    | .node _value left right =>
      let (left', leftHeight) := go left
      let (right', rightHeight) := go right
      match Ord.compare leftHeight rightHeight with
      | .lt => (right', rightHeight + 1)
      | .eq => (root, leftHeight + 1)
      | .gt => (left', leftHeight + 1)

namespace Tree

inductive TreeAccess where
  | left
  | right

def get' (as : List TreeAccess) (tree : Tree α) : Tree α :=
  match as with
  | [] => tree
  | .left :: as => get' as tree.left
  | .right :: as => get' as tree.right

@[simp, grind]
theorem get'_nil (tree : Tree α) : get' [] tree = tree := rfl

@[simp, grind]
theorem get'_cons_left (as : List TreeAccess) (tree : Tree α) : get' (.left :: as) tree = get' as tree.left := rfl

@[simp, grind]
theorem get'_cons_right (as : List TreeAccess) (tree : Tree α) : get' (.right :: as) tree = get' as tree.right := rfl

@[simp, grind]
theorem get'_nil_tree (as : List TreeAccess) : get' as (.nil : Tree α) = .nil := by
  induction as with
  | nil => rfl
  | cons a as ih => cases a <;> simp [get', ih]

@[simp, grind]
theorem get'_append (as₁ as₂ : List TreeAccess) (tree : Tree α) : get' (as₁ ++ as₂) tree = get' as₂ (get' as₁ tree) := by
  induction as₁ generalizing tree with
  | nil => simp
  | cons a as₁ ih =>
    cases a with
    | left => simp [ih]
    | right => simp [ih]

@[grind]
def IsDeepestAccess (root : Tree α) (as : List TreeAccess) : Prop :=
  root.get' as ≠ .nil ∧ ∀ as', root.get' as' ≠ .nil → as'.length ≤ as.length

theorem length_eq_of_IsDeepestAccess {root : Tree α} {as₁ as₂ : List TreeAccess}
  (h₁ : root.IsDeepestAccess as₁) (h₂ : root.IsDeepestAccess as₂) :
  as₁.length = as₂.length := by
  grind

@[grind]
def IsAncestorOfDeepestAccesses (root : Tree α) (as : List TreeAccess) : Prop :=
  ∀ as', root.IsDeepestAccess as' → as <+: as'

@[grind]
def IsLongestAncestorOfDeepestAccesses (root : Tree α) (as : List TreeAccess) : Prop :=
  ∀ as', root.IsAncestorOfDeepestAccesses as' → as'.length ≤ as.length

end Tree
