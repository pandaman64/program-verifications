-- https://leetcode.com/problems/minimum-time-visiting-all-points/submissions/1825054177/
import Mathlib

def minTimeToVisitAllPoints (points : Array (Int × Int)) : Nat := Id.run do
  let mut time : Nat := 0
  for h : i in [0:points.size - 1] do
    have : i + 1 < points.size := by
      have : i < points.size - 1 := Membership.get_elem_helper h rfl
      grind [Membership.get_elem_helper]
    let (x1, y1) := points[i]
    let (x2, y2) := points[i + 1]
    time := time + max (x1 - x2).natAbs (y1 - y2).natAbs
  return time

section Specification

open List

@[grind]
def IsNextPoint (current next : Int × Int) : Prop :=
  -1 ≤ current.1 - next.1 ∧ current.1 - next.1 ≤ 1 ∧ -1 ≤ current.2 - next.2 ∧ current.2 - next.2 ≤ 1

@[grind]
def IsAllPointsVisited (movements points : List (Int × Int)) : Prop :=
  IsChain IsNextPoint movements ∧ points <+ movements

@[grind]
def distance (current next : Int × Int) : Nat :=
  (current.1 - next.1).natAbs + (current.2 - next.2).natAbs

@[grind]
def step (current target : Int) : Int :=
  match Ord.compare current target with
  | .lt => current + 1
  | .eq => current
  | .gt => current - 1

@[grind]
theorem natAbs_step_of_eq (current target : Int) (h : current = target) :
  ((step current target) - target).natAbs = 0 := by
  simp [step, h]

@[grind]
theorem Int.natAbs_eq_toNat_nonneg (n : Int) (h : 0 ≤ n) : n.natAbs = n.toNat := by
  grind

@[grind]
theorem Int.natAbs_eq_toNat_nonpos (n : Int) (h : n ≤ 0) : n.natAbs = (-n).toNat := by
  grind

@[grind]
theorem natAbs_step_of_lt (current target : Int) (h : current < target) :
  ((step current target) - target).natAbs + 1 = (current - target).natAbs := by
  simp only [step, Int.compare_eq_lt.mpr h]
  grind

@[grind]
theorem natAbs_step_of_gt (current target : Int) (h : target < current) :
  ((step current target) - target).natAbs + 1 = (target - current).natAbs := by
  simp only [step, Int.compare_eq_gt.mpr h]
  grind

@[grind]
theorem natAbs_step_of_ne (current target : Int) (h : current ≠ target) :
  ((step current target) - target).natAbs + 1 = (target - current).natAbs := by
  grind

@[grind]
def stepPoint (current target : Int × Int) : Int × Int :=
  if current = target then
    current
  else
    (step current.1 target.1, step current.2 target.2)

@[grind]
theorem isNextPoint_stepPoint (current target : Int × Int) : IsNextPoint current (stepPoint current target) := by
  unfold stepPoint step
  grind

@[grind]
theorem distance_lt_distance_stepPoint_of_ne (current target : Int × Int) (h : current ≠ target) :
  distance (stepPoint current target) target < distance current target := by
  simp only [distance, stepPoint, h, ↓reduceIte]
  if h' : current.1 = target.1 then
    have h'' : current.2 ≠ target.2 := by grind
    grind
  else
    if h'' : current.2 = target.2 then
      grind
    else
      grind

def minMovementsToVisitNext (current target : Int × Int) : List (Int × Int) :=
  if h : current = target then
    []
  else
    let next := stepPoint current target
    have : distance next target < distance current target := distance_lt_distance_stepPoint_of_ne current target h
    current :: minMovementsToVisitNext next target
termination_by distance current target

end Specification
