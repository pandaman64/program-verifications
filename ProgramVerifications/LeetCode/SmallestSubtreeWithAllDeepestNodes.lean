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

-- inductive IsSubtreeOf (tree : Tree α) : Tree α → Prop where
--   | refl : IsSubtreeOf tree tree
--   | left {value left right} (h : IsSubtreeOf tree left) : IsSubtreeOf tree (.node value left right)
--   | right {value left right} (h : IsSubtreeOf tree right) : IsSubtreeOf tree (.node value left right)

namespace Tree

inductive SubtreeAt (root : Tree α) : Tree α → Nat → Prop where
  | refl : Tree.SubtreeAt root root 0
  | left {value left right depth} (h : Tree.SubtreeAt root (.node value left right) depth) : Tree.SubtreeAt root left (depth + 1)
  | right {value left right depth} (h : Tree.SubtreeAt root (.node value left right) depth) : Tree.SubtreeAt root right (depth + 1)

@[grind]
theorem SubtreeAt.ofLeft {value : α} {left right tree depth} (h : Tree.SubtreeAt left tree depth) : Tree.SubtreeAt (Tree.node value left right) tree (depth + 1) := by
  induction h with
  | refl => exact .left .refl
  | left _ ih => exact .left ih
  | right _ ih => exact .right ih

@[grind]
theorem SubtreeAt.ofRight {value : α} {left right tree depth} (h : Tree.SubtreeAt right tree depth) : Tree.SubtreeAt (Tree.node value left right) tree (depth + 1) := by
  induction h with
  | refl => exact .right .refl
  | left _ ih => exact .left ih
  | right _ ih => exact .right ih

theorem height_plus_depth_le_total_height (h : Tree.SubtreeAt root tree depth) :
  tree.height + depth ≤ root.height := by
  induction h <;> grind [Tree.height]

@[grind]
def IsDeepestSubtreeOf (tree : Tree α) (root : Tree α) : Prop :=
  ∃ depth, root.SubtreeAt tree depth ∧ ∀ tree' depth', root.SubtreeAt tree' depth' → depth' ≤ depth

@[simp, grind]
theorem left_nil_of_isDeepestSubtreeOf {tree root : Tree α} (h : tree.IsDeepestSubtreeOf root) : tree.left = .nil := by
  cases tree with
  | nil => grind [Tree.left]
  | node value left right =>
    obtain ⟨depth, hd, hmax⟩ := h
    cases hd with
    | refl =>
      have := hmax left 1 (.left .refl)
      grind
    | @left value' _ right' depth' hd =>
      have := hmax left (depth' + 2) (.left (.left hd))
      grind
    | @right value' _ left' depth' hd =>
      have := hmax left (depth' + 2) (.left (.right hd))
      grind

@[simp, grind]
theorem right_nil_of_isDeepestSubtreeOf {tree root : Tree α} (h : tree.IsDeepestSubtreeOf root) : tree.right = .nil := by
  cases tree with
  | nil => grind [Tree.right]
  | node value left right =>
    obtain ⟨depth, hd, hmax⟩ := h
    cases hd with
    | refl =>
      have := hmax right 1 (.right .refl)
      grind
    | @left value' _ right' depth' hd =>
      have := hmax right (depth' + 2) (.right (.left hd))
      grind
    | @right value' _ left' depth' hd =>
      have := hmax right (depth' + 2) (.right (.right hd))
      grind

@[grind]
theorem eq_nil_or_singleton_of_isDeepestSubtreeOf {tree root : Tree α} (h : tree.IsDeepestSubtreeOf root) :
  tree = .nil ∨ ∃ value, tree = .node value .nil .nil := by
  match eq : tree with
  | .nil => exact .inl rfl
  | .node value left right =>
    have : tree.left = left := by simp [Tree.left, eq]
    have : tree.right = right := by simp [Tree.right, eq]
    grind

@[grind]
def deepestSubtree (root : Tree α) : Tree α :=
  match root with
  | .nil => .nil
  | .node _value left right =>
    if left.height ≤ right.height then
      deepestSubtree right
    else
      deepestSubtree left

theorem subtreeAt_deepestSubtree_height (root : Tree α) : root.SubtreeAt (deepestSubtree root) root.height := by
  induction root with
  | nil => exact .refl
  | node _value left right ihLeft ihRight =>
    if h : left.height ≤ right.height then
      simpa [deepestSubtree, h] using .ofRight ihRight
    else
      have h' : right.height ≤ left.height := by grind
      simpa [deepestSubtree, h, h'] using .ofLeft ihLeft

theorem isDeepestSubtreeOf_deepestSubtree (root : Tree α) : (deepestSubtree root).IsDeepestSubtreeOf root := by
  refine ⟨root.height, subtreeAt_deepestSubtree_height root, ?_⟩
  intro tree depth h
  exact Nat.le_trans (by grind) (height_plus_depth_le_total_height h)

theorem subtreeAt_height_of_isDeepestSubtreeOf {tree root : Tree α} (h : tree.IsDeepestSubtreeOf root) :
  root.SubtreeAt tree root.height := by
  obtain ⟨depth, hd, hmax⟩ := h
  have ge : root.height ≤ depth := hmax (deepestSubtree root) root.height (subtreeAt_deepestSubtree_height root)
  have le : depth ≤ root.height := Nat.le_trans (by grind) (height_plus_depth_le_total_height hd)
  grind

theorem isDeepestSubtreeOf_of_subtreeAt_height {tree root : Tree α} (h : root.SubtreeAt tree root.height) :
  tree.IsDeepestSubtreeOf root := by
  refine ⟨root.height, h, ?_⟩
  intro tree depth h
  exact Nat.le_trans (by grind) (height_plus_depth_le_total_height h)

@[simp, grind]
theorem isDeepestSubtreeOf_iff_subtreeAt_height {tree root : Tree α} :
  tree.IsDeepestSubtreeOf root ↔ root.SubtreeAt tree root.height := ⟨subtreeAt_height_of_isDeepestSubtreeOf, isDeepestSubtreeOf_of_subtreeAt_height⟩

end Tree
