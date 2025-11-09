-- https://leetcode.com/problems/count-operations-to-obtain-zero/submissions/1825037436/
import Mathlib

def countOperationsToZero (num1 : Nat) (num2 : Nat) : Nat :=
  if _ : num1 = 0 || num2 = 0 then
    0
  else if num1 >= num2 then
    have : num1 - num2 < num1 := by
      grind
    countOperationsToZero (num1 - num2) num2 + 1
  else
    have : num2 - num1 < num2 := by
      grind
    countOperationsToZero num1 (num2 - num1) + 1
termination_by (num1, num2)

def countOperationsToZeroTC (num1 : Nat) (num2 : Nat) (accum : Nat := 0) : Nat :=
  if _ : num1 = 0 || num2 = 0 then
    accum
  else if num1 >= num2 then
    have : num1 - num2 < num1 := by
      grind
    countOperationsToZeroTC (num1 - num2) num2 (accum + 1)
  else
    have : num2 - num1 < num2 := by
      grind
    countOperationsToZeroTC num1 (num2 - num1) (accum + 1)
termination_by (num1, num2, accum)

theorem countOperationsToZero_eq_countOperationsToZeroTCAux (num1 num2 accum : Nat) :
  countOperationsToZero num1 num2 + accum = countOperationsToZeroTC num1 num2 accum := by
  fun_induction countOperationsToZero num1 num2 generalizing accum
  next => grind [countOperationsToZeroTC]
  next => grind [countOperationsToZeroTC]
  next => grind [countOperationsToZeroTC]

theorem countOperationsToZero_eq_countOperationsToZeroTC (num1 num2 : Nat) :
  countOperationsToZero num1 num2 = countOperationsToZeroTC num1 num2 :=
  countOperationsToZero_eq_countOperationsToZeroTCAux num1 num2 0

-- We don't have much to prove about this, since I don't think we have a good characterization of the function
-- not directly relevant to the implementation.
