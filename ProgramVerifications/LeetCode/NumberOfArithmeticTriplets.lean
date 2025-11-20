-- https://leetcode.com/problems/number-of-arithmetic-triplets/description/
import Mathlib
import Std.Do

open Std.Do
set_option mvcgen.warning false

def numberOfArithmeticTriplets (nums : Array Nat) (diff : Nat) : Nat := Id.run do
  let mut count : Nat := 0
  for h₁ : i in [0:nums.size] do
    for h₂ : j in [i + 1:nums.size] do
      for h₃ : k in [j + 1:nums.size] do
        if nums[i] + diff = nums[j] ∧ nums[j] + diff = nums[k] then
          count := count + 1
  return count

def NumberOfArithmeticTriplets (nums : Array Nat) (diff : Nat) : Nat :=
  (Finset.range nums.size ×ˢ Finset.range nums.size ×ˢ Finset.range nums.size)
  |>.filter (fun (i, j, k) => i < j ∧ j < k ∧ nums[i]! + diff = nums[j]! ∧ nums[j]! + diff = nums[k]!)
  |>.card

theorem NumberOfArithmeticTriplets_def (nums : Array Nat) (diff : Nat) :
  NumberOfArithmeticTriplets nums diff =
  ∑ i ∈ Finset.range nums.size, ∑ j ∈ Finset.range nums.size, ∑ k ∈ Finset.range nums.size,
    if i < j ∧ j < k ∧ nums[i]! + diff = nums[j]! ∧ nums[j]! + diff = nums[k]! then 1 else 0 := by
  unfold NumberOfArithmeticTriplets
  rw [Finset.card_filter, ←Finset.sum_product', ←Finset.sum_product']
  apply Finset.sum_equiv (Equiv.prodAssoc _ _ _).symm (by grind)
  intro (i, j, k) h
  simp

theorem NumberOfArithmeticTriplets_def' (nums : Array Nat) (diff : Nat) :
  NumberOfArithmeticTriplets nums diff =
  ∑ i ∈ Finset.range nums.size, ∑ j ∈ Finset.Ico (i + 1) nums.size, ∑ k ∈ Finset.Ico (j + 1) nums.size,
    if nums[i]! + diff = nums[j]! ∧ nums[j]! + diff = nums[k]! then 1 else 0 := by
  rw [NumberOfArithmeticTriplets_def]
  apply Finset.sum_congr rfl
  intro i hi
  rw [←Finset.sum_range_add_sum_Ico (h := (by grind : i + 1 ≤ nums.size))]
  have : (∑ j ∈ Finset.range (i + 1), ∑ k ∈ Finset.range nums.size,
    if i < j ∧ j < k ∧ nums[i]! + diff = nums[j]! ∧ nums[j]! + diff = nums[k]! then 1 else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    apply Finset.sum_eq_zero
    intro k hk
    grind
  rw [this, Nat.zero_add]
  apply Finset.sum_congr rfl
  intro j hj
  rw [←Finset.sum_range_add_sum_Ico (h := (by grind [Finset.mem_Ico] : j + 1 ≤ nums.size))]
  have : (∑ k ∈ Finset.range (j + 1),
    if i < j ∧ j < k ∧ nums[i]! + diff = nums[j]! ∧ nums[j]! + diff = nums[k]! then 1 else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    grind
  rw [this, Nat.zero_add]
  apply Finset.sum_congr rfl
  intro k hk
  grind [Finset.mem_Ico]

def summand (nums : Array Nat) (diff : Nat) (i j k : Nat) : Nat :=
  if nums[i]! + diff = nums[j]! ∧ nums[j]! + diff = nums[k]! then 1 else 0

theorem numberOfArithmeticTriplets_spec {count : Nat} (nums : Array Nat) (diff : Nat)
  (h : numberOfArithmeticTriplets nums diff = count) :
  count = NumberOfArithmeticTriplets nums diff := by
  apply Id.of_wp_run_eq h; clear h
  mvcgen
  invariants
  · ⇓⟨ic, currentCount⟩ =>
    ⌜currentCount = ∑ i ∈ Finset.range ic.prefix.length, ∑ j ∈ Finset.Ico (i + 1) nums.size, ∑ k ∈ Finset.Ico (j + 1) nums.size, summand nums diff i j k⌝
  · ⇓⟨jc, currentCount⟩ => by
    rename_i iCurrent _ _ _ _ _
    exact ⌜currentCount = ∑ i ∈ Finset.range iCurrent, ∑ j ∈ Finset.Ico (i + 1) nums.size, ∑ k ∈ Finset.Ico (j + 1) nums.size, summand nums diff i j k +
      ∑ j ∈ Finset.Ico (iCurrent + 1) (iCurrent + 1 + jc.prefix.length), ∑ k ∈ Finset.Ico (j + 1) nums.size, summand nums diff iCurrent j k⌝
  · ⇓⟨kc, currentCount⟩ => by
    rename_i iCurrent _ _ _ _ _ jCurrent _ _ _ _ _
    exact  ⌜currentCount = ∑ i ∈ Finset.range iCurrent, ∑ j ∈ Finset.Ico (i + 1) nums.size, ∑ k ∈ Finset.Ico (j + 1) nums.size, summand nums diff i j k +
      ∑ j ∈ Finset.Ico (iCurrent + 1) jCurrent, ∑ k ∈ Finset.Ico (j + 1) nums.size, summand nums diff iCurrent j k +
      ∑ k ∈ Finset.Ico (jCurrent + 1) (jCurrent + 1 + kc.prefix.length), summand nums diff iCurrent jCurrent k⌝
  case vc1.step.isTrue => sorry
  case vc2.step.isFalse => sorry
  case vc3.step.pre => sorry
  case vc4.step.post.success iPref iCurrent _ _ count invI jPref jCurrent _ _ count' invJ count'' invK =>
    sorry
  case vc5.step.pre => sorry
  case vc6.step.post.success iPref iCurrent _ _ count' invJ count'' invK =>
    have eq₁ : iPref.length = iCurrent := by grind
    have eq₂ : iCurrent + 1 + (nums.size - (iCurrent + 1)) = nums.size := by grind
    simp only [List.length_range', add_tsub_cancel_right, Nat.div_one, eq₂, List.length_append, eq₁,
      List.length_cons, List.length_nil, zero_add] at invK ⊢
    simp [Finset.sum_range_add, invK]
  case vc8.a.post.success count h =>
    simp only [h, List.length_range', tsub_zero, add_tsub_cancel_right, Nat.div_one, summand, NumberOfArithmeticTriplets_def']

