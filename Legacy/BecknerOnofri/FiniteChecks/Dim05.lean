module

public import Legacy.D10.FiniteShellList
public import Legacy.BecknerOnofri.FiniteScalarCore

@[expose] public section

/-!
# Finite scalar certificates in dimension 5

`FiniteCheck 5 n` for `1 ≤ n ≤ 21`. Each check rewrites the truncated shell polynomial
with its list form (`shellArray_eq_shellList`) and is decided by the kernel.
-/

namespace Legacy.BecknerOnofri.FiniteScalar.Dim05

open Legacy.D10.FiniteScalar

theorem check01 : FiniteCheck 5 1 := by
  unfold FiniteCheck retainedMass energyUpper
  rw [shellArray_eq_shellList]
  decide +kernel

theorem check02 : FiniteCheck 5 2 := by
  unfold FiniteCheck retainedMass energyUpper
  rw [shellArray_eq_shellList]
  decide +kernel

theorem check03 : FiniteCheck 5 3 := by
  unfold FiniteCheck retainedMass energyUpper
  rw [shellArray_eq_shellList]
  decide +kernel

theorem check04 : FiniteCheck 5 4 := by
  unfold FiniteCheck retainedMass energyUpper
  rw [shellArray_eq_shellList]
  decide +kernel

theorem check05 : FiniteCheck 5 5 := by
  unfold FiniteCheck retainedMass energyUpper
  rw [shellArray_eq_shellList]
  decide +kernel

theorem check06 : FiniteCheck 5 6 := by
  unfold FiniteCheck retainedMass energyUpper
  rw [shellArray_eq_shellList]
  decide +kernel

theorem check07 : FiniteCheck 5 7 := by
  unfold FiniteCheck retainedMass energyUpper
  rw [shellArray_eq_shellList]
  decide +kernel

theorem check08 : FiniteCheck 5 8 := by
  unfold FiniteCheck retainedMass energyUpper
  rw [shellArray_eq_shellList]
  decide +kernel

theorem check09 : FiniteCheck 5 9 := by
  unfold FiniteCheck retainedMass energyUpper
  rw [shellArray_eq_shellList]
  decide +kernel

theorem check10 : FiniteCheck 5 10 := by
  unfold FiniteCheck retainedMass energyUpper
  rw [shellArray_eq_shellList]
  decide +kernel

theorem check11 : FiniteCheck 5 11 := by
  unfold FiniteCheck retainedMass energyUpper
  rw [shellArray_eq_shellList]
  decide +kernel

theorem check12 : FiniteCheck 5 12 := by
  unfold FiniteCheck retainedMass energyUpper
  rw [shellArray_eq_shellList]
  decide +kernel

theorem check13 : FiniteCheck 5 13 := by
  unfold FiniteCheck retainedMass energyUpper
  rw [shellArray_eq_shellList]
  decide +kernel

theorem check14 : FiniteCheck 5 14 := by
  unfold FiniteCheck retainedMass energyUpper
  rw [shellArray_eq_shellList]
  decide +kernel

theorem check15 : FiniteCheck 5 15 := by
  unfold FiniteCheck retainedMass energyUpper
  rw [shellArray_eq_shellList]
  decide +kernel

theorem check16 : FiniteCheck 5 16 := by
  unfold FiniteCheck retainedMass energyUpper
  rw [shellArray_eq_shellList]
  decide +kernel

theorem check17 : FiniteCheck 5 17 := by
  unfold FiniteCheck retainedMass energyUpper
  rw [shellArray_eq_shellList]
  decide +kernel

theorem check18 : FiniteCheck 5 18 := by
  unfold FiniteCheck retainedMass energyUpper
  rw [shellArray_eq_shellList]
  decide +kernel

theorem check19 : FiniteCheck 5 19 := by
  unfold FiniteCheck retainedMass energyUpper
  rw [shellArray_eq_shellList]
  decide +kernel

theorem check20 : FiniteCheck 5 20 := by
  unfold FiniteCheck retainedMass energyUpper
  rw [shellArray_eq_shellList]
  decide +kernel

theorem check21 : FiniteCheck 5 21 := by
  unfold FiniteCheck retainedMass energyUpper
  rw [shellArray_eq_shellList]
  decide +kernel

theorem checks : ∀ j : Fin 21, FiniteCheck 5 (j.val + 1) := by
  intro j
  fin_cases j
  · exact check01
  · exact check02
  · exact check03
  · exact check04
  · exact check05
  · exact check06
  · exact check07
  · exact check08
  · exact check09
  · exact check10
  · exact check11
  · exact check12
  · exact check13
  · exact check14
  · exact check15
  · exact check16
  · exact check17
  · exact check18
  · exact check19
  · exact check20
  · exact check21

end Legacy.BecknerOnofri.FiniteScalar.Dim05
