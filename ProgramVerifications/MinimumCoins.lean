import Mathlib

-- @[grind]
-- def shortestOpt (a : Option (List Nat)) (b : Option (List Nat)) : Option (List Nat) :=
--   match a, b with
--   | .some a, .some b => if a.length < b.length then .some a else .some b
--   | .some a, .none => .some a
--   | .none, .some b => .some b
--   | .none, .none => .none

-- def minimumCoins (coins : List Nat) (amount : Nat) : Option (List Nat) :=
--   match coins with
--   | [] => if amount = 0 then .some [] else .none
--   | coin :: coins =>
--     if h : coin = 0 || coin > amount then
--       minimumCoins coins amount
--     else
--       have : amount - coin < amount := by grind
--       let resultWith := minimumCoins (coin :: coins) (amount - coin) |>.map (coin :: ·)
--       let resultWithout := minimumCoins coins amount
--       shortestOpt resultWith resultWithout
-- termination_by (coins, amount)

-- @[grind]
-- def IsSolution (coins : List Nat) (amount : Nat) (result : List Nat) : Prop :=
--   amount = result.sum ∧ ∀ c ∈ result, c ∈ coins

-- @[simp, grind]
-- theorem isSolution_nil {coins : List Nat} {amount : Nat} :
--   IsSolution coins amount [] ↔ amount = 0 := by
--   simp [IsSolution]

-- @[simp, grind]
-- theorem isSolution_cons {coins : List Nat} {amount : Nat} {c : Nat} {result : List Nat} :
--   IsSolution coins amount (c :: result) ↔ c ≤ amount ∧ c ∈ coins ∧ IsSolution coins (amount - c) result := by
--   grind

-- @[simp, grind]
-- theorem isSolution_empty {amount : Nat} {result : List Nat} :
--   IsSolution [] amount result ↔ result = [] ∧ amount = 0 := by
--   induction result with
--   | nil => simp
--   | cons c result ih => simp

-- theorem isSolution_of_minimumCoins_some {coins : List Nat} {amount : Nat} {result : List Nat} :
--   minimumCoins coins amount = .some result → IsSolution coins amount result := by
--   fun_induction minimumCoins coins amount generalizing result
--   next => grind
--   next => grind
--   next => grind
--   next amount coin coins h _ resultWith resultWithout ihWith ihWithout =>
--     match hw : resultWith, hwo : resultWithout with
--     | .some rw, .some rwo => grind [Option.map_eq_some_iff]
--     | .some rw, .none => grind [Option.map_eq_some_iff]
--     | .none, .some rwo => grind
--     | .none, .none => grind

-- @[grind]
-- def IsMinimalSolution (coins : List Nat) (amount : Nat) (result : List Nat) : Prop :=
--   IsSolution coins amount result ∧ ∀ result', IsSolution coins amount result' → result.length ≤ result'.length

-- @[simp, grind]
-- theorem isMinimalSolution_nil {coins : List Nat} {amount : Nat} :
--   IsMinimalSolution coins amount [] ↔ amount = 0 := by
--   simp [IsMinimalSolution]

-- def dropFirstMatch {α} [DecidableEq α] (x : α) (xs : List α) : List α :=
--   match xs with
--   | [] => []
--   | x' :: xs => if x = x' then xs else x' :: dropFirstMatch x xs

-- @[simp, grind]
-- theorem dropFirstMatch_length_of_mem {α} [DecidableEq α] {x : α} {xs : List α} (h : x ∈ xs) :
--   (dropFirstMatch x xs).length = xs.length - 1 := by
--   fun_induction dropFirstMatch x xs <;> grind

-- @[simp, grind]
-- theorem dropFirstMatch_length_of_not_mem {α} [DecidableEq α] {x : α} {xs : List α} (h : x ∉ xs) :
--   (dropFirstMatch x xs).length = xs.length := by
--   fun_induction dropFirstMatch x xs <;> grind

-- @[simp, grind]
-- theorem dropFirstMatch_sum_of_mem {x : Nat} {xs : List Nat} (h : x ∈ xs) :
--   (dropFirstMatch x xs).sum + x = xs.sum := by
--   fun_induction dropFirstMatch x xs <;> grind

-- @[simp, grind]
-- theorem dropFirstMatch_sum_of_not_mem {x : Nat} {xs : List Nat} (h : x ∉ xs) :
--   (dropFirstMatch x xs).sum = xs.sum := by
--   fun_induction dropFirstMatch x xs <;> grind

-- @[simp, grind]
-- theorem mem_of_mem_dropFirstMatch {α} [DecidableEq α] {x x' : α} {xs : List α} (h : x' ∈ dropFirstMatch x xs) :
--   x' ∈ xs := by
--   fun_induction dropFirstMatch x xs <;> grind

-- def dropMatches {α} [DecidableEq α] (x : α) (xs : List α) : List α :=
--   match xs with
--   | [] => []
--   | x' :: xs => if x = x' then dropMatches x xs else x' :: dropMatches x xs

-- @[grind]
-- theorem not_mem_dropMatches {α} [DecidableEq α] {x : α} {xs : List α} :
--   x ∉ dropMatches x xs := by
--   fun_induction dropMatches x xs <;> grind

-- @[simp, grind]
-- theorem dropMatches_length_of_not_mem {α} [DecidableEq α] {x : α} {xs : List α} (h : x ∉ xs) :
--   (dropMatches x xs).length = xs.length := by
--   fun_induction dropMatches x xs <;> grind

-- @[grind]
-- theorem dropMatches_length_of_mem {α} [DecidableEq α] {x : α} {xs : List α} (h : x ∈ xs) :
--   (dropMatches x xs).length < xs.length := by
--   fun_induction dropMatches x xs <;> grind

-- @[grind]
-- theorem le_dropMatches_length {α} [DecidableEq α] {x : α} {xs : List α} :
--   (dropMatches x xs).length ≤ xs.length := by
--   by_cases h : x ∈ xs
--   · exact Nat.le_of_lt (dropMatches_length_of_mem h)
--   · grind

-- @[simp, grind]
-- theorem dropMatches_sum_of_not_mem {x : Nat} {xs : List Nat} (h : x ∉ xs) :
--   (dropMatches x xs).sum = xs.sum := by
--   fun_induction dropMatches x xs <;> grind

-- @[grind]
-- theorem dropMatches_sum_of_mem {x : Nat} {xs : List Nat} (h : x ∈ xs) :
--   ∃ n, (dropMatches x xs).sum + n * x = xs.sum := by
--   fun_induction dropMatches x xs
--   next => grind
--   next xs ih =>
--     by_cases h' : x ∈ xs
--     · obtain ⟨n, hn⟩ := ih h'
--       exists n + 1
--       grind
--     · exists 1
--       grind
--   next => grind

-- @[simp, grind]
-- theorem mem_dropMatches_iff {α} [DecidableEq α] {x x' : α} {xs : List α} :
--   x' ∈ dropMatches x xs ↔ x' ∈ xs ∧ x' ≠ x := by
--   fun_induction dropMatches x xs <;> grind

-- @[grind]
-- theorem le_of_mem_of_isSolution {coins : List Nat} {amount : Nat} {c : Nat} {result : List Nat}
--   (h₁ : c ∈ result) (h₂ : IsSolution coins amount result) :
--   c ≤ amount := by
--   induction result generalizing amount <;> grind

-- @[simp, grind]
-- theorem isSolution_cons_iff_of_not_mem {c : Nat} {coins : List Nat} {amount : Nat} {result : List Nat}
--   (h : c ∉ result) :
--   IsSolution (c :: coins) amount result ↔ IsSolution coins amount result := by
--   grind

-- @[grind]
-- theorem ne_zero_of_mem_of_isMinimalSolution {coins : List Nat} {amount : Nat} {result : List Nat}
--   (h : IsMinimalSolution coins amount result) :
--   ∀c ∈ result, c ≠ 0 := by
--   intro c h' eq
--   subst c
--   let result' := dropFirstMatch 0 result
--   have isSolution : IsSolution coins amount result' := by grind
--   have lt_length : result'.length < result.length := by grind
--   grind

-- @[simp, grind]
-- theorem isMinimalSolution_cons_zero {coins : List Nat} {amount : Nat} {result : List Nat} :
--   IsMinimalSolution (0 :: coins) amount result ↔ IsMinimalSolution coins amount result := by
--   refine ⟨?_, ?_⟩
--   · intro ims
--     grind [-isSolution_cons_iff_of_not_mem]
--   · intro ims
--     have zero_not_mem : 0 ∉ result := by grind
--     unfold IsMinimalSolution
--     refine ⟨by grind, ?_⟩
--     intro result' isSolution
--     by_cases mem : 0 ∈ result'
--     · let result'' := dropMatches 0 result'
--       have not_mem : 0 ∉ result'' := by grind
--       have isSolution' : IsSolution coins amount result'' := by grind
--       grind
--     · grind

-- theorem isMinimalSolution_of_minimumCoins_some {coins : List Nat} {amount : Nat} {result : List Nat}
--   (h : minimumCoins coins amount = .some result) :
--   IsMinimalSolution coins amount result := by
--   induction amount using Nat.strongRec generalizing coins result with
--   | ind amount ih =>
--     revert h
--     fun_cases minimumCoins coins amount
--     next => grind
--     next => grind
--     next coin coins h =>
--       simp only [gt_iff_lt, Bool.or_eq_true, decide_eq_true_eq] at h
--       cases h with
--       | inl h =>
--         simp [h]
--         sorry
--       | inr h => sorry
--     next coin coins h _ resultWith resultWithout =>
--       match hw : resultWith, hwo : resultWithout with
--       | .some rw, .some rwo => sorry
--       | .some rw, .none => sorry
--       | .none, .some rwo => sorry
--       | .none, .none => grind

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

def coinExchanges (coins : List Nat) (amount : Nat) : Finset (Multiset Nat) :=
  match coins with
  | [] => if amount = 0 then {∅} else {}
  | coin :: coins =>
    if h : coin = 0 || coin > amount then
      coinExchanges coins amount
    else
      have : amount - coin < amount := by grind
      let exchangesWith := coinExchanges (coin :: coins) (amount - coin) |>.image (coin ::ₘ ·)
      let exchangesWithout := coinExchanges coins amount
      exchangesWith ∪ exchangesWithout
termination_by (coins, amount)

@[simp, grind]
theorem coinExchanges_zero {coins : List Nat} {amount : Nat} (eq : amount = 0) : coinExchanges coins amount = {0} := by
  fun_induction coinExchanges coins amount <;> grind

@[simp, grind]
theorem coinExchanges_zero' {coins : List Nat} : coinExchanges coins 0 = {0} := coinExchanges_zero rfl

@[simp, grind]
theorem coinExchanges_cons_gt {coin : Nat} {coins : List Nat} {amount : Nat} (gt : coin > amount) :
  coinExchanges (coin :: coins) amount = coinExchanges coins amount := by
  conv =>
    lhs
    unfold coinExchanges
    simp [gt]

theorem coinExchanges_cons_of_not_zero_of_le {coin : Nat} {coins : List Nat} {amount : Nat}
  (hz : coin ≠ 0) (le : coin ≤ amount) :
  coinExchanges (coin :: coins) amount = ((coinExchanges (coin :: coins) (amount - coin) |>.image (coin ::ₘ ·)) ∪ coinExchanges coins amount) := by
  have h : (coin = 0 || coin > amount) = false := by grind
  conv =>
    lhs
    unfold coinExchanges
    simp [h]

theorem isSolution_of_mem_coinExchanges {coins : List Nat} {amount : Nat} {exchange : Multiset Nat}
  (hz : ∀ c ∈ coins, c ≠ 0) (mem : exchange ∈ coinExchanges coins amount) :
  IsSolution coins amount exchange := by
  revert mem
  fun_induction coinExchanges coins amount generalizing exchange
  next => simp
  next => grind
  next amount coin coins h ih =>
    simp only [gt_iff_lt, Bool.or_eq_true, decide_eq_true_eq] at h
    cases h with
    | inl h => simp [h] at hz
    | inr h => grind
  next amount coin coins h _ exchangesWith exchangesWithout ihWith ihWithout =>
    intro mem
    simp only [gt_iff_lt, Bool.or_eq_true, decide_eq_true_eq, not_or, not_lt] at h
    grind

theorem mem_coinExchanges_of_isSolution {coins : List Nat} {amount : Nat} {exchange : Multiset Nat}
  (hz : ∀ c ∈ coins, c ≠ 0) (isSolution : IsSolution coins amount exchange) :
  exchange ∈ coinExchanges coins amount := by
  induction isSolution using coinInduction with
  | empty coins => grind
  | cons_mem coin coins amount exchange le is ih =>
    have ih := ih hz
    simp only [List.mem_cons, ne_eq, forall_eq_or_imp] at hz
    rw [coinExchanges_cons_of_not_zero_of_le hz.1 le]
    simpa only [Finset.mem_union, Finset.mem_image, Multiset.cons_inj_right, exists_eq_right] using .inl ih
  | cons_not_mem coin coins amount exchange not_mem is ih =>
    have ih := ih (by grind)
    cases Nat.lt_or_ge amount coin with
    | inl lt => simpa [coinExchanges_cons_gt lt] using ih
    | inr ge =>
      simp only [List.mem_cons, ne_eq, forall_eq_or_imp] at hz
      rw [coinExchanges_cons_of_not_zero_of_le hz.1 ge]
      simpa only [Finset.mem_union, Finset.mem_image, Multiset.cons_inj_right, exists_eq_right] using .inr ih

@[grind]
theorem mem_coinExchanges_iff_isSolution {coins : List Nat} {amount : Nat} {exchange : Multiset Nat}
  (hz : ∀ c ∈ coins, c ≠ 0) :
  exchange ∈ coinExchanges coins amount ↔ IsSolution coins amount exchange :=
  ⟨isSolution_of_mem_coinExchanges hz, mem_coinExchanges_of_isSolution hz⟩
