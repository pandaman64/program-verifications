import Mathlib
import Std.Data.HashMap
import Std.Tactic.Do

@[grind]
def IsSolution (coins : List Nat) (amount : Nat) (exchange : Multiset Nat) : Prop :=
  amount = exchange.sum ∧ ∀ c ∈ exchange, c ∈ coins

@[simp, grind]
theorem isSolution_empty {coins : List Nat} {amount : Nat} :
  IsSolution coins amount 0 ↔ amount = 0 := by
  simp [IsSolution]

@[simp, grind]
theorem isSolution_cons {coins : List Nat} {amount : Nat} {c : Nat} {exchange : Multiset Nat} :
  IsSolution coins amount (c ::ₘ exchange) ↔ c ≤ amount ∧ c ∈ coins ∧ IsSolution coins (amount - c) exchange := by
  simp only [IsSolution, Multiset.sum_cons, Multiset.mem_cons, forall_eq_or_imp]
  grind

@[simp, grind]
theorem isSolution_empty_coins {amount : Nat} {exchange : Multiset Nat} :
  IsSolution [] amount exchange ↔ amount = 0 ∧ exchange = 0 := by
  simp only [IsSolution, List.not_mem_nil, imp_false]
  refine ⟨?_, by grind⟩
  intro ⟨h₁, h₂⟩
  have eq : exchange = 0 := by simpa [Multiset.ext'_iff] using h₂
  grind

@[grind]
theorem isSolution_cons_coins_of_isSolution {c : Nat} {coins : List Nat} {amount : Nat} {exchange : Multiset Nat}
  (h : IsSolution coins amount exchange) :
  IsSolution (c :: coins) amount exchange := by
  grind

@[simp, grind]
theorem isSolution_cons_iff_of_not_mem {c : Nat} {coins : List Nat} {amount : Nat} {exchange : Multiset Nat}
  (h : c ∉ exchange) :
  IsSolution (c :: coins) amount exchange ↔ IsSolution coins amount exchange := by
  induction exchange using Multiset.induction generalizing amount <;> grind

@[grind]
theorem le_of_mem_of_isSolution {coins : List Nat} {amount : Nat} {c : Nat} {exchange : Multiset Nat}
  (h₁ : c ∈ exchange) (h₂ : IsSolution coins amount exchange) :
  c ≤ amount := by
  induction exchange using Multiset.induction generalizing amount <;> grind

theorem exists_ne_zero_mem_of_isSolution_ne_zero {coins : List Nat} {amount : Nat} {exchange : Multiset Nat} [ne : NeZero amount]
  (h : IsSolution coins amount exchange) :
  ∃ c ∈ coins, c ≠ 0 ∧ c ∈ exchange := by
  induction exchange using Multiset.induction with
  | empty => exact absurd (by grind) ne.ne
  | cons e exchange ih => grind

/--
Induction principle for coin exchange problems.

This induction principle is useful when the user wants to induct over the list of coins given a
valid exchange. The principle has three cases:

1. **Base case (empty)**: When the amount is 0, the only valid exchange is the empty multiset (regardless of the coins).
2. **Inductive case (cons_mem)**: When a coin `c` appears in the exchange, we can reason about
   the remaining exchange after removing one occurrence of `c`, with the amount reduced by `c`.
   This case handles the situation where we use the first coin in `coins`.
3. **Inductive case (cons_not_mem)**: When a coin `c` from our available coins doesn't appear
   in the exchange, we can reason about the same exchange using only the remaining coins.
-/
theorem coinInduction {motive : (coins : List Nat) → (amount : Nat) → (exchange : Multiset Nat) → IsSolution coins amount exchange → Prop}
  (empty : ∀ coins, motive coins 0 0 (by grind))
  (cons_mem : ∀ c coins amount exchange (le : c ≤ amount) (is : IsSolution (c :: coins) (amount - c) exchange), motive (c :: coins) (amount - c) exchange is → motive (c :: coins) amount (c ::ₘ exchange) (by grind))
  (cons_not_mem : ∀ c coins amount exchange (_not_mem : c ∉ exchange) (is : IsSolution coins amount exchange), motive coins amount exchange is → motive (c :: coins) amount exchange (by grind))
  {coins amount exchange} (is : IsSolution coins amount exchange) :
  motive coins amount exchange is :=
  match coins with
  | [] => by
    simp only [isSolution_empty_coins] at is
    simpa [is] using empty []
  | c :: coins => by
    by_cases h : c ∈ exchange
    next =>
      obtain ⟨exchange', eq⟩ := Multiset.exists_cons_of_mem h
      subst exchange
      simp only [isSolution_cons, List.mem_cons, true_or, true_and] at is
      exact cons_mem c coins amount exchange' is.1 is.2 (coinInduction empty cons_mem cons_not_mem is.2)
    next =>
      have is' : IsSolution coins amount exchange := by grind
      exact cons_not_mem c coins amount exchange h is' (coinInduction empty cons_mem cons_not_mem is')
termination_by (coins, exchange.card)

def minimumExchangeCountDP (coins : List Nat) (amount : Nat) : Option Nat := Id.run do
  let mut minCounts : Std.HashMap Nat Nat := .emptyWithCapacity (amount + 1)
  minCounts := minCounts.insert 0 0
  for a in [0:amount] do
    match minCounts[a]? with
    | .none => continue
    | .some count =>
      -- mvcgen somehow introduces two `minCounts` in VCs and forgets the relationship between them.
      -- Or is it supposed to be given as a part of the second invariant?
      -- for coin in coins do
      --   minCounts := minCounts.alter (a + coin) (updateCount count)
      minCounts := updateCounts minCounts a count
  return minCounts[amount]?
where
  updateCount (minCounts : Std.HashMap Nat Nat) (target : Nat) (count : Nat) : Std.HashMap Nat Nat :=
      let newCount :=
        match minCounts[target]? with
        | .some count' => min (count + 1) count'
        | .none => count + 1
      minCounts.insert target newCount
  updateCounts (minCounts : Std.HashMap Nat Nat) (amount : Nat) (count : Nat) : Std.HashMap Nat Nat :=
    coins.foldl (init := minCounts) fun minCounts coin => updateCount minCounts (amount + coin) count

open Std.Do

set_option mvcgen.warning false

def prevCounts (coins : List Nat) (minCounts : Std.HashMap Nat Nat) (amount : Nat) : Finset Nat :=
  coins.toFinset.filter (fun c => c ≤ amount ∧ c ≠ 0 ∧ amount - c ∈ minCounts)
    |>.attach
    |>.image (fun ⟨c, h⟩ => minCounts[amount - c]'(by grind))

@[grind]
theorem mem_prevCounts_iff {coins : List Nat} {minCounts : Std.HashMap Nat Nat} {amount : Nat} {count : Nat} :
  count ∈ prevCounts coins minCounts amount ↔ ∃ c ∈ coins, c ≠ 0 ∧ c ≤ amount ∧ minCounts[amount - c]? = .some count := by
  simp only [prevCounts, ne_eq, Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists,
    Finset.mem_filter, List.mem_toFinset]
  grind

def Minimality (coins : List Nat) (minCounts : Std.HashMap Nat Nat) : Prop :=
  ∀ a, (h : a ∈ minCounts) →
    a = 0 ∨
    ∃ h' : (prevCounts coins minCounts a).Nonempty, minCounts[a] = Finset.min' (prevCounts coins minCounts a) h' + 1

theorem Minimality.zero {coins : List Nat} {amount : Nat} : Minimality coins ((Std.HashMap.emptyWithCapacity amount).insert 0 0) := by
  grind [Minimality]

theorem Minimality.updateCountsAux {coins cs : List Nat} {minCounts : Std.HashMap Nat Nat} {amount count : Nat}
  (h₁ : minCounts[amount]? = .some count) (h₂ : ∀ c ∈ cs, c ∈ coins) (inv : Minimality coins minCounts) :
  Minimality coins (cs.foldl (init := minCounts) fun minCounts coin => minimumExchangeCountDP.updateCount minCounts (amount + coin) count) := by
  induction cs generalizing minCounts with
  | nil => grind
  | cons c cs ih =>
    have h₁' : (minimumExchangeCountDP.updateCount minCounts (amount + c) count)[amount]? = some count := by
      match c with
      | 0 => simp [minimumExchangeCountDP.updateCount, h₁]
      | c + 1 => grind [minimumExchangeCountDP.updateCount]
    have inv' : Minimality coins (minimumExchangeCountDP.updateCount minCounts (amount + c) count) := by
      intro a mem
      if eq : amount + c = a then
        right
        refine ⟨?_, ?_⟩
        . simp [Finset.nonempty_def, mem_prevCounts_iff]
          sorry
        . sorry
      else
        sorry
    simp only [List.foldl_cons]
    simp only [List.mem_cons, forall_eq_or_imp] at h₂
    exact ih h₁' h₂.2 inv'

theorem Minimality.updateCounts {coins : List Nat} {minCounts : Std.HashMap Nat Nat} {amount count : Nat}
  (h : minCounts[amount]? = .some count) (inv : Minimality coins minCounts) :
  Minimality coins (minimumExchangeCountDP.updateCounts coins minCounts amount count) := by
  sorry

@[grind]
def Reachable (coins : List Nat) (minCounts : Std.HashMap Nat Nat) (curAmount : Nat) : Prop :=
  ∀ a < curAmount, (h : a ∈ minCounts) → ∀ c ∈ coins, a + c ∈ minCounts

theorem Reachable.zero {coins : List Nat} {amount : Nat} : Reachable coins ((Std.HashMap.emptyWithCapacity amount).insert 0 0) 0 := by
  grind [Reachable]

@[grind]
theorem Reachable.updateCounts {coins : List Nat} {minCounts : Std.HashMap Nat Nat} {amount count : Nat}
  (h : minCounts[amount]? = .some count) (inv : Reachable coins minCounts amount) :
  Reachable coins (minimumExchangeCountDP.updateCounts coins minCounts amount count) (amount + 1) := by
  sorry

theorem minimumExchangeCountDP_none_iff_no_solution' {coins : List Nat} {amount : Nat} {count : Option Nat}
  (h : minimumExchangeCountDP coins amount = count) :
  count = .none ↔ ∀ exchange, ¬IsSolution coins amount exchange := by
  apply Id.of_wp_run_eq h; clear h
  mvcgen
  invariants
  -- It's ugly to represent "the current index" as `amountCursor.prefix.length`
  . ⇓⟨amountCursor, minCounts⟩ => ⌜Minimality coins minCounts ∧ Reachable coins minCounts amountCursor.prefix.length⌝ --∀ a : Nat, a ≤ amountCursor.prefix.length → (a ∈ minCounts ↔ ∃ exchange, IsSolution coins a exchange)⌝
  case vc1.step.h_1 prefAmount curAmount suffAmount hamount minCounts eqnone inv =>
    refine ⟨inv.1, ?_⟩
    simp only [List.length_append, List.length_cons, List.length_nil, zero_add]
    grind
  case vc2.step.h_2 prefAmount curAmount suffAmount hamount minCounts count eqsome inv =>
    exact ⟨inv.1.updateCounts eqsome, by grind⟩
  case vc3.a.pre => exact ⟨.zero, .zero⟩
  case vc4.a.post.success minCounts inv =>
    -- Think about how to derive the final result from the invariants later
    sorry


/-
直感: もっと根本的な不変条件として
∀ a ∈ minCounts,
  (a = 0) ∨
  (∃ c ∈ coins, c ≠ 0 ∧ c ≤ a ∧ a - c ∈ minCounts ∧ minCounts[a] = minCounts[a - c] + 1)
がありそう。アルゴリズムの動き的な不変条件

これをIsSolutionに繋げるのは後付けでできるか？それともそれも不変条件に盛り込んで

∀ a ∈ minCounts,
  (a = 0 ∧ minCounts[a] = 0) ∨ -- represents the `IsSolution coins 0 0` case
  (∃ c ∈ coins, c ≠ 0 ∧ c ≤ a ∧ a - c ∈ minCounts ∧ minCounts[a] = minCounts[a - c] + 1 ∧ ∃ exchange, IsSolution coins a exchange ∧ exchange.card = minCounts[a])
-/
