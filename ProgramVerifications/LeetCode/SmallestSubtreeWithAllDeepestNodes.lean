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

theorem smallestSubtreeWithAllDeepestNodes'.go.eq_height {root : Tree α} :
  (smallestSubtreeWithAllDeepestNodes'.go root).2 = root.height := by
  fun_induction smallestSubtreeWithAllDeepestNodes'.go root
  next => simp
  next _value left right left' leftHeight eql right' rightHeight eqr cmp ihLeft ihRight =>
    rw [Nat.compare_eq_lt] at cmp
    simp
    grind
  next _value left right left' leftHeight eql right' rightHeight eqr cmp ihLeft ihRight =>
    rw [Nat.compare_eq_eq] at cmp
    simp
    grind
  next _value left right left' leftHeight eql right' rightHeight eqr cmp ihLeft ihRight =>
    rw [Nat.compare_eq_gt] at cmp
    simp
    grind

theorem smallestSubtreeWithAllDeepestNodes'.go.eq_smallestSubtreeWithAllDeepestNodes {root : Tree α} :
  (smallestSubtreeWithAllDeepestNodes'.go root).1 = smallestSubtreeWithAllDeepestNodes root := by
  fun_induction smallestSubtreeWithAllDeepestNodes'.go root
  next => rfl
  next _value left right left' leftHeight eql right' rightHeight eqr cmp ihLeft ihRight =>
    unfold smallestSubtreeWithAllDeepestNodes
    have eql' : leftHeight = left.height := by simpa [eql] using smallestSubtreeWithAllDeepestNodes'.go.eq_height (root := left)
    have eqr' : rightHeight = right.height := by simpa [eqr] using smallestSubtreeWithAllDeepestNodes'.go.eq_height (root := right)
    grind
  next _value left right left' leftHeight eql right' rightHeight eqr cmp ihLeft ihRight =>
    unfold smallestSubtreeWithAllDeepestNodes
    have eql' : leftHeight = left.height := by simpa [eql] using smallestSubtreeWithAllDeepestNodes'.go.eq_height (root := left)
    have eqr' : rightHeight = right.height := by simpa [eqr] using smallestSubtreeWithAllDeepestNodes'.go.eq_height (root := right)
    grind
  next _value left right left' leftHeight eql right' rightHeight eqr cmp ihLeft ihRight =>
    unfold smallestSubtreeWithAllDeepestNodes
    have eql' : leftHeight = left.height := by simpa [eql] using smallestSubtreeWithAllDeepestNodes'.go.eq_height (root := left)
    have eqr' : rightHeight = right.height := by simpa [eqr] using smallestSubtreeWithAllDeepestNodes'.go.eq_height (root := right)
    grind

namespace Tree

/-
We identify a subtree as a path from the root to a node, represented as a list of `TreeAccess`s.

This is because there may be "identical" subtrees (in terms of value equality) at a different postition in the tree,
while the problem talks about the "referential equality" when identifying subtrees.
-/
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
theorem get'_ne_nil_of_get'_append_ne_nil {as₁ as₂ : List TreeAccess} {tree : Tree α} (h : tree.get' (as₁ ++ as₂) ≠ .nil) :
  tree.get' as₁ ≠ .nil := by
  by_cases eq : tree.get' as₁ = .nil <;> grind

@[grind]
theorem length_lt_height_of_get'_ne_nil {as : List TreeAccess} {tree : Tree α} (h : tree.get' as ≠ .nil) :
  as.length < tree.height := by
  induction as generalizing tree with
  | nil => cases tree <;> grind [height]
  | cons a as ih =>
    cases tree with
    | nil => grind
    | node _value left right =>
      simp only [List.length_cons, height, add_lt_add_iff_right, lt_sup_iff]
      cases a with
      | left => exact .inl (ih h)
      | right => exact .inr (ih h)

@[grind]
theorem eq_nil_of_get'_leaf_ne_nil {as : List TreeAccess} {value : α} (ne : get' as (.node value .nil .nil) ≠ .nil) :
  as = [] := by
  match as with
  | [] => rfl
  | .left :: as => simp at ne
  | .right :: as => simp at ne

@[grind]
def IsDeepestAccess (root : Tree α) (as : List TreeAccess) : Prop :=
  root.get' as ≠ .nil ∧ ∀ as', root.get' as' ≠ .nil → as'.length ≤ as.length

@[grind]
theorem ne_nil_of_IsDeepestAccess {root : Tree α} {as : List TreeAccess} (h : root.IsDeepestAccess as) : root ≠ .nil := by
  grind

def deepestAccess (root : Tree α) : List TreeAccess :=
  match root with
  | .nil => []
  | .node _value .nil .nil => []
  | .node _value .nil right => .right :: right.deepestAccess
  | .node _value left .nil => .left :: left.deepestAccess
  | .node _value left right =>
    let asLeft := left.deepestAccess
    let asRight := right.deepestAccess
    if asLeft.length ≤ asRight.length then
      .right :: asRight
    else
      .left :: asLeft

theorem isDeepestAccess_deepestAccess_of_ne_nil {root : Tree α} (ne : root ≠ .nil) : root.IsDeepestAccess (deepestAccess root) := by
  fun_induction deepestAccess root
  next => grind
  next => grind
  next _value right ne' ihRight =>
    have ihRight := ihRight ne'
    refine ⟨?_, ?_⟩
    . exact ihRight.1
    . intro as' h
      match as' with
      | [] => simp
      | .left :: as' => simp at h
      | .right :: as' =>
        simp only [get'_cons_right, Tree.right, ne_eq] at h
        grind
  next _value left ne' ihLeft =>
    have ihLeft := ihLeft ne'
    refine ⟨?_, ?_⟩
    . exact ihLeft.1
    . intro as' h
      match as' with
      | [] => simp
      | .left :: as' =>
        simp only [get'_cons_left, Tree.left, ne_eq] at h
        grind
      | .right :: as' => simp at h
  next _value left right _ neLeft neRight asLeft asRight le ihLeft ihRight =>
    have ihLeft := ihLeft neLeft
    have ihRight := ihRight neRight
    refine ⟨?_, ?_⟩
    . exact ihRight.1
    . intro as' h
      match as' with
      | [] => simp
      | .left :: as' =>
        simp only [get'_cons_left, Tree.left, ne_eq] at h
        simp only [List.length_cons, add_le_add_iff_right, ge_iff_le]
        exact Nat.le_trans (ihLeft.2 as' h) le
      | .right :: as' =>
        simp only [get'_cons_right, Tree.right, ne_eq] at h
        simp only [List.length_cons, add_le_add_iff_right, ge_iff_le]
        exact ihRight.2 as' h
  next _value left right _ neLeft neRight asLeft asRight nle ihLeft ihRight =>
    have ihLeft := ihLeft neLeft
    have ihRight := ihRight neRight
    refine ⟨?_, ?_⟩
    . exact ihLeft.1
    . intro as' h
      match as' with
      | [] => simp
      | .left :: as' =>
        simp only [get'_cons_left, Tree.left, ne_eq] at h
        simp only [List.length_cons, add_le_add_iff_right, ge_iff_le]
        exact ihLeft.2 as' h
      | .right :: as' =>
        simp only [get'_cons_right, Tree.right, ne_eq] at h
        simp only [List.length_cons, add_le_add_iff_right, ge_iff_le]
        exact Nat.le_trans (ihRight.2 as' h) (by grind)

theorem deepestAccess_length_add_one_eq_height_of_ne_nil {root : Tree α} (ne : root ≠ .nil) : root.deepestAccess.length + 1 = root.height := by
  fun_induction deepestAccess root <;> grind [Tree.height]

theorem length_eq_of_IsDeepestAccess {root : Tree α} {as₁ as₂ : List TreeAccess}
  (h₁ : root.IsDeepestAccess as₁) (h₂ : root.IsDeepestAccess as₂) :
  as₁.length = as₂.length := by
  grind

@[grind, simp]
theorem length_add_one_eq_height_of_IsDeepestAccess {root : Tree α} {as : List TreeAccess} (h : root.IsDeepestAccess as) :
  as.length + 1 = root.height := by
  have ne := ne_nil_of_IsDeepestAccess h
  rw [length_eq_of_IsDeepestAccess h (isDeepestAccess_deepestAccess_of_ne_nil ne), deepestAccess_length_add_one_eq_height_of_ne_nil ne]

theorem isDeepestAccess_of_length_add_one_eq_height_of_ne_nil {root : Tree α} {as : List TreeAccess}
  (eq : as.length + 1 = root.height) (ne : root.get' as ≠ .nil) :
  root.IsDeepestAccess as := by
  refine ⟨ne, ?_⟩
  intro as' ne'
  have := length_lt_height_of_get'_ne_nil ne'
  grind

@[grind]
theorem isDeepestAccess_get_of_isDeepestAccess_append {root : Tree α} {as₁ as₂ : List TreeAccess}
  (h : root.IsDeepestAccess (as₁ ++ as₂)) :
  (root.get' as₁).IsDeepestAccess as₂ := by
  induction as₁ generalizing as₂ root with
  | nil => grind
  | cons a as₁ ih =>
    cases root with
    | nil => grind
    | node _value left right =>
      cases a with
      | left =>
        have h' : left.IsDeepestAccess (as₁ ++ as₂) := by
          refine ⟨?_, ?_⟩
          . exact h.1
          . intro as' h'
            have := h.2 (.left :: as') h'
            grind
        exact ih h'
      | right =>
        have h' : right.IsDeepestAccess (as₁ ++ as₂) := by
          refine ⟨?_, ?_⟩
          . exact h.1
          . intro as' h'
            have := h.2 (.right :: as') h'
            grind
        exact ih h'

@[grind, simp]
theorem height_eq_zero_iff_eq_nil {root : Tree α} : root.height = 0 ↔ root = .nil := by
  induction root <;> grind [height]

theorem leaf_of_isDeepestAccess_nil {root : Tree α} (h : root.IsDeepestAccess []) :
  ∃ value, root = .node value .nil .nil := by
  have heightEq : root.height = 1 := (length_add_one_eq_height_of_IsDeepestAccess h).symm
  match root with
  | .nil => grind
  | .node value left right =>
    simp only [height, Nat.add_eq_right, Nat.max_eq_zero_iff, height_eq_zero_iff_eq_nil] at heightEq
    simpa using heightEq

@[grind]
theorem height_ge_of_isDeepestAccess_cons_left {root : Tree α} {as : List TreeAccess} (h : root.IsDeepestAccess (.left :: as)) :
  root.left.height ≥ root.right.height := by
  have h' : root.left.IsDeepestAccess as := isDeepestAccess_get_of_isDeepestAccess_append (as₁ := [.left]) (as₂ := as) h
  have eqLeft : root.left.height = as.length + 1 := by grind
  have eq : root.height = as.length + 2 := by grind
  match root with
  | .nil => grind
  | .node _value left right => simp_all

@[grind]
theorem height_le_of_isDeepestAccess_cons_right {root : Tree α} {as : List TreeAccess} (h : root.IsDeepestAccess (.right :: as)) :
  root.left.height ≤ root.right.height := by
  have h' : root.right.IsDeepestAccess as := isDeepestAccess_get_of_isDeepestAccess_append (as₁ := [.right]) (as₂ := as) h
  have eqRight : root.right.height = as.length + 1 := by grind
  have eq : root.height = as.length + 2 := by grind
  match root with
  | .nil => grind
  | .node _value left right => simp_all

@[grind]
def IsAncestorOfDeepestAccesses (root : Tree α) (as : List TreeAccess) : Prop :=
  ∀ as', root.IsDeepestAccess as' → as <+: as'

@[grind]
theorem height_eq_length_add_get_height_of_isAncestorOfDeepestAccesses_of_ne_nil {root : Tree α} {as : List TreeAccess}
  (iada : root.IsAncestorOfDeepestAccesses as) (ne : root ≠ .nil) :
  root.height = as.length + (root.get' as).height := by
  have ida : root.IsDeepestAccess root.deepestAccess := isDeepestAccess_deepestAccess_of_ne_nil ne
  have eq := length_add_one_eq_height_of_IsDeepestAccess ida
  obtain ⟨as', eq'⟩ := iada root.deepestAccess ida
  grind

theorem isAncestorOfDeepestAccesses_snoc_left_of_isAncestorOfDeepestAccesses_of_gt_height {root : Tree α} {as : List TreeAccess}
  (iada : root.IsAncestorOfDeepestAccesses as) (gt : (root.get' as).left.height > (root.get' as).right.height) :
  root.IsAncestorOfDeepestAccesses (as ++ [.left]) := by
  intro as' ida
  obtain ⟨as'', eq⟩ := iada as' ida
  match as'' with
  | [] => grind
  | .left :: as'' => exact ⟨as'', by grind⟩
  | .right :: as'' => grind

theorem isAncestorOfDeepestAccesses_snoc_right_of_isAncestorOfDeepestAccesses_of_lt_height {root : Tree α} {as : List TreeAccess}
  (iada : root.IsAncestorOfDeepestAccesses as) (lt : (root.get' as).left.height < (root.get' as).right.height) :
  root.IsAncestorOfDeepestAccesses (as ++ [.right]) := by
  intro as' ida
  obtain ⟨as'', eq⟩ := iada as' ida
  match as'' with
  | [] => grind
  | .left :: as'' => grind
  | .right :: as'' => exact ⟨as'', by grind⟩

theorem not_isAncestorOfDeepestAccesses_snoc_of_isAncestorOfDeepestAccesses_of_eq_height_of_ne_nil {root : Tree α} {as : List TreeAccess} {a : TreeAccess}
  (iada : root.IsAncestorOfDeepestAccesses as) (eq : (root.get' as).left.height = (root.get' as).right.height) (ne : (root.get' as) ≠ .nil) :
  ¬root.IsAncestorOfDeepestAccesses (as ++ [a]) := by
  intro iada'
  match h : root.get' as with
  | .nil => grind
  | .node _value .nil .nil =>
    have ida : root.IsDeepestAccess root.deepestAccess := isDeepestAccess_deepestAccess_of_ne_nil (by grind)
    obtain ⟨as', eq'⟩ := iada' root.deepestAccess ida
    grind
  | .node _value (.node valueL leftL rightL) (.node valueR leftR rightR) =>
    cases a with
    | left =>
      have idaR : IsDeepestAccess (.node valueR leftR rightR) (deepestAccess (.node valueR leftR rightR)) :=
        isDeepestAccess_deepestAccess_of_ne_nil (by grind)
      have ida : root.IsDeepestAccess (as ++ .right :: (deepestAccess (.node valueR leftR rightR))) := by
        refine isDeepestAccess_of_length_add_one_eq_height_of_ne_nil ?_ (by simpa [get'_append, h] using idaR.1)
        have eqR := length_add_one_eq_height_of_IsDeepestAccess idaR
        have eqR' := height_eq_length_add_get_height_of_isAncestorOfDeepestAccesses_of_ne_nil iada (by grind)
        simp [h] at eq
        simp [eqR', eqR, h, eq, Nat.add_assoc]
      obtain ⟨as', eq'⟩ := iada' _ ida
      simp at eq'
    | right =>
      have idaL : IsDeepestAccess (.node valueL leftL rightL) (deepestAccess (.node valueL leftL rightL)) :=
        isDeepestAccess_deepestAccess_of_ne_nil (by grind)
      have ida : root.IsDeepestAccess (as ++ .left :: (deepestAccess (.node valueL leftL rightL))) := by
        refine isDeepestAccess_of_length_add_one_eq_height_of_ne_nil ?_ (by simpa [get'_append, h] using idaL.1)
        have eqL := length_add_one_eq_height_of_IsDeepestAccess idaL
        have eqL' := height_eq_length_add_get_height_of_isAncestorOfDeepestAccesses_of_ne_nil iada (by grind)
        simp [h] at eq
        simp [eqL', eqL, h, eq, Nat.add_assoc]
      obtain ⟨as', eq'⟩ := iada' _ ida
      simp at eq'
  | .node _value (.node _valueL leftL rightL) .nil => simp [h, height] at eq
  | .node _value .nil (.node _valueR leftR rightR) => simp [h, height] at eq

@[grind]
theorem isAncestorOfDeepestAccesses_of_isAncestorOfDeepestAccesses_append {root : Tree α} {as₁ as₂ : List TreeAccess}
  (iada : root.IsAncestorOfDeepestAccesses (as₁ ++ as₂)) :
  root.IsAncestorOfDeepestAccesses as₁ := by
  intro as' ida
  obtain ⟨as'', eq⟩ := iada as' ida
  grind

@[grind]
theorem get'_ne_nil_of_isAncestorOfDeepestAccesses_ne_nil {root : Tree α} {as : List TreeAccess}
  (iada : root.IsAncestorOfDeepestAccesses as) (ne : root ≠ .nil) :
  root.get' as ≠ .nil := by
  intro h
  have ida : root.IsDeepestAccess root.deepestAccess := isDeepestAccess_deepestAccess_of_ne_nil ne
  obtain ⟨as', eq⟩ := iada root.deepestAccess ida
  grind

theorem _root_.List.isPrefix_of_append_eq_append {xs₁ xs₂ xs₃ xs₄ : List α} (eq : xs₁ ++ xs₂ = xs₃ ++ xs₄) :
  xs₁ <+: xs₃ ∨ xs₃ <+: xs₁ := by
  induction xs₁ generalizing xs₃ with
  | nil => grind
  | cons x xs₁ ih =>
    match xs₃ with
    | [] => grind
    | x' :: xs₃ =>
      simp only [List.cons_append, List.cons.injEq] at eq
      simpa [eq] using ih eq.2

theorem isPrefix_of_isAncestorOfDeepestAccesses_of_ne_nil {root : Tree α} {as₁ as₂ : List TreeAccess}
  (iada₁ : root.IsAncestorOfDeepestAccesses as₁) (iada₂ : root.IsAncestorOfDeepestAccesses as₂) (ne : root ≠ .nil) :
  as₁ <+: as₂ ∨ as₂ <+: as₁ := by
  have ida : root.IsDeepestAccess root.deepestAccess := isDeepestAccess_deepestAccess_of_ne_nil ne
  obtain ⟨asL, eqL⟩ := iada₁ root.deepestAccess ida
  obtain ⟨asR, eqR⟩ := iada₂ root.deepestAccess ida
  exact List.isPrefix_of_append_eq_append (eqR ▸ eqL)

@[grind]
def IsLongestAncestorOfDeepestAccesses (root : Tree α) (as : List TreeAccess) : Prop :=
  root.IsAncestorOfDeepestAccesses as ∧ ∀ as', root.IsAncestorOfDeepestAccesses as' → as'.length ≤ as.length

theorem isAncestorOfDeepestAccesses_eq_height_of_isLongestAncestorOfDeepestAccesses {root : Tree α} {as : List TreeAccess}
  (ilada : root.IsLongestAncestorOfDeepestAccesses as) :
  root.IsAncestorOfDeepestAccesses as ∧ (root.get' as).left.height = (root.get' as).right.height := by
  refine ⟨ilada.1, ?_⟩
  match Nat.lt_trichotomy (root.get' as).left.height (root.get' as).right.height with
  | .inl lt =>
    have := isAncestorOfDeepestAccesses_snoc_right_of_isAncestorOfDeepestAccesses_of_lt_height ilada.1 lt
    grind
  | .inr (.inl eq) => exact eq
  | .inr (.inr gt) =>
    have := isAncestorOfDeepestAccesses_snoc_left_of_isAncestorOfDeepestAccesses_of_gt_height ilada.1 gt
    grind

theorem isLongestAncestorOfDeepestAccesses_of_isAncestorOfDeepestAccesses_of_eq_height_of_ne_nil {root : Tree α} {as : List TreeAccess}
  (iada : root.IsAncestorOfDeepestAccesses as) (eq : (root.get' as).left.height = (root.get' as).right.height) (ne : root.get' as ≠ .nil) :
  root.IsLongestAncestorOfDeepestAccesses as := by
  refine ⟨iada, ?_⟩
  intro as' iada'
  cases isPrefix_of_isAncestorOfDeepestAccesses_of_ne_nil iada iada' (by grind) with
  | inl h =>
    have ⟨as'', eq'⟩ := h
    match as'' with
    | [] => grind
    | a :: as'' =>
      have eq'' : as' = (as ++ [a]) ++ as'' := by grind
      have iada'' : root.IsAncestorOfDeepestAccesses (as ++ [a]) :=
        isAncestorOfDeepestAccesses_of_isAncestorOfDeepestAccesses_append (eq'' ▸ iada')
      have := not_isAncestorOfDeepestAccesses_snoc_of_isAncestorOfDeepestAccesses_of_eq_height_of_ne_nil iada eq ne iada''
      grind
  | inr h => grind

end Tree

theorem smallestSubtreeWithAllDeepestNodes_eq_get_longestAncestorOfDeepestAccesses_of_isAncestorOfDeepestAccesses_of_ne_nil
  {root : Tree α} {as : List Tree.TreeAccess} (iada : root.IsAncestorOfDeepestAccesses as) (ne : root.get' as ≠ .nil) :
  ∃ as', root.IsLongestAncestorOfDeepestAccesses as' ∧ smallestSubtreeWithAllDeepestNodes (root.get' as) = root.get' as' := by
  match h : root.get' as with
  | .nil => grind
  | .node _value left right =>
    have : as.length < root.height := by grind
    unfold smallestSubtreeWithAllDeepestNodes
    split
    next lt =>
      rw [Nat.compare_eq_lt] at lt
      have iadaR := Tree.isAncestorOfDeepestAccesses_snoc_right_of_isAncestorOfDeepestAccesses_of_lt_height iada (h ▸ lt)
      have neR : root.get' (as ++ [.right]) ≠ .nil := by grind
      have := smallestSubtreeWithAllDeepestNodes_eq_get_longestAncestorOfDeepestAccesses_of_isAncestorOfDeepestAccesses_of_ne_nil iadaR neR
      simpa [h]
    next eq =>
      rw [Nat.compare_eq_eq] at eq
      have ilada := Tree.isLongestAncestorOfDeepestAccesses_of_isAncestorOfDeepestAccesses_of_eq_height_of_ne_nil iada (h ▸ eq) ne
      exact ⟨as, ilada, h.symm⟩
    next gt =>
      rw [Nat.compare_eq_gt] at gt
      have iadaL := Tree.isAncestorOfDeepestAccesses_snoc_left_of_isAncestorOfDeepestAccesses_of_gt_height iada (h ▸ gt)
      have neL : root.get' (as ++ [.left]) ≠ .nil := by grind
      have := smallestSubtreeWithAllDeepestNodes_eq_get_longestAncestorOfDeepestAccesses_of_isAncestorOfDeepestAccesses_of_ne_nil iadaL neL
      simpa [h]
termination_by root.height - as.length
