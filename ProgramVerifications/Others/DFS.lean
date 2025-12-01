import Mathlib

open Relation (ReflTransGen)
open Std (HashSet)

namespace DFS

structure Graph (V : Type*) where
  adjList : V → List V

def Graph.ofList {V} [DecidableEq V] (edges : List (V × V)) : Graph V :=
  { adjList := fun v => edges.filterMap fun (u, w) => if u = v then some w else none }

variable {V : Type*} [DecidableEq V] [Fintype V]

def dfs [Fintype V] (G : Graph V) (visited : Finset V) (stack : List V) : Finset V :=
  match stack with
  | [] => visited
  | v :: stack =>
    if _ : v ∈ visited then
      dfs G visited stack
    else
      dfs G (insert v visited) (G.adjList v ++ stack)
termination_by (Fintype.card V - visited.card, stack)
decreasing_by
  . simp [Prod.lex_def]
  . have : visited.card < Fintype.card V := by
      rw [Finset.card_lt_iff_ne_univ]
      grind
    have : Fintype.card V - (insert v visited).card < Fintype.card V - visited.card := by
      grind
    simp [Prod.lex_def, this]

@[grind]
theorem subset_dfs {G : Graph V} {visited : Finset V} {stack : List V} : visited ⊆ dfs G visited stack := by
  fun_induction dfs G visited stack <;> grind

@[grind]
theorem mem_dfs_of_mem_stack {G : Graph V} {visited : Finset V} {v : V} {stack : List V} (h : v ∈ stack) :
  v ∈ dfs G visited stack := by
  fun_induction dfs G visited stack
  next => grind
  next visited v' stack mem ih =>
    simp only [List.mem_cons] at h
    cases h with
    | inl eq => exact Finset.mem_of_subset subset_dfs (eq ▸ mem)
    | inr mem => grind
  next visited v' stack mem ih =>
    simp only [List.mem_cons] at h
    cases h with
    | inl eq => exact Finset.mem_of_subset subset_dfs (by grind)
    | inr mem => exact ih (by grind)

theorem mem_dfs_of_mem_dfs_of_mem_adjListAux {G : Graph V} {visited : Finset V} {stack : List V}
  (inv : ∀ u ∈ visited, ∀ v ∈ G.adjList u, v ∈ visited ∨ v ∈ stack) :
  ∀ u ∈ dfs G visited stack, ∀ v ∈ G.adjList u, v ∈ dfs G visited stack := by
  fun_induction dfs G visited stack <;> grind

theorem mem_dfs_of_mem_dfs_of_mem_adjList {G : Graph V} {u : V} :
  ∀ v ∈ dfs G ∅ [u], ∀ w ∈ G.adjList v, w ∈ dfs G ∅ [u] :=
  mem_dfs_of_mem_dfs_of_mem_adjListAux (by grind)

def Graph.Reachable (G : Graph V) : V → V → Prop :=
  ReflTransGen (fun u v => v ∈ G.adjList u)

omit [DecidableEq V] [Fintype V] in
@[grind]
theorem reachable_refl {G : Graph V} {u : V} : G.Reachable u u := .refl

omit [DecidableEq V] [Fintype V] in
@[grind]
theorem reachable_tail {G : Graph V} {u v w : V} (h : G.Reachable u v) (h' : w ∈ G.adjList v) : G.Reachable u w :=
  h.tail h'

omit [DecidableEq V] [Fintype V] in
theorem mem_of_reachable_of_mem_of_mem_of_mem_adjList {G : Graph V} {S : Finset V}
  (inv : ∀ u ∈ S, ∀ v ∈ G.adjList u, v ∈ S) :
  ∀ u ∈ S, ∀ v, G.Reachable u v → v ∈ S := by
  intro u mem v h
  induction h with
  | refl => exact mem
  | @tail v w _ h ih => exact inv v ih w h

theorem mem_dfs_of_reachable {G : Graph V} {u v : V} (h : G.Reachable u v) : v ∈ dfs G ∅ [u] :=
  mem_of_reachable_of_mem_of_mem_of_mem_adjList mem_dfs_of_mem_dfs_of_mem_adjList u (by grind) v h

theorem reachable_of_mem_dfsAux {G : Graph V} {visited : Finset V} {stack : List V} {u : V}
  (inv₁ : ∀ v ∈ visited, G.Reachable u v) (inv₂ : ∀ v ∈ stack, G.Reachable u v) :
  ∀ v ∈ dfs G visited stack, G.Reachable u v := by
  fun_induction dfs G visited stack <;> grind

theorem reachable_of_mem_dfs {G : Graph V} {u v : V} (h : v ∈ dfs G ∅ [u]) : G.Reachable u v :=
  reachable_of_mem_dfsAux (by grind) (by grind) v h

@[grind]
theorem reachable_iff_mem_dfs {G : Graph V} {u v : V} : G.Reachable u v ↔ v ∈ dfs G ∅ [u] :=
  ⟨mem_dfs_of_reachable, reachable_of_mem_dfs⟩

-- partial def dfsHash [Hashable V] (G : Graph V) (visited : HashSet V) (stack : List V) : HashSet V :=
--   match stack with
--   | [] => visited
--   | v :: stack =>
--     if v ∈ visited then
--       dfsHash G visited stack
--     else
--       -- Here, we want something like `v ∉ visited → visited.size < Fintype.card V`.
--       dfsHash G (visited.insert v) (G.adjList v ++ stack)

end DFS
