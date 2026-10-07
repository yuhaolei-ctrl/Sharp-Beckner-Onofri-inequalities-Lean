module

public import Legacy.D10.FiniteShellList
public import Legacy.BecknerOnofri.FiniteScalarCore

@[expose] public section

/-!
# Finite scalar certificates in dimension 7

`FiniteCheck 7 n` for `1 ≤ n ≤ 21`. Each check rewrites the truncated shell polynomial
with its list form (`shellArray_eq_shellList`) and is decided by the kernel.
-/

namespace Legacy.BecknerOnofri.FiniteScalar.Dim07

open Legacy.D10.FiniteScalar

theorem check01 : FiniteCheck 7 1 := by
  unfold FiniteCheck retainedMass energyUpper
  rw [shellArray_eq_shellList]
  decide +kernel

theorem check02 : FiniteCheck 7 2 := by
  unfold FiniteCheck retainedMass energyUpper
  rw [shellArray_eq_shellList]
  decide +kernel

theorem check03 : FiniteCheck 7 3 := by
  unfold FiniteCheck retainedMass energyUpper
  rw [shellArray_eq_shellList]
  decide +kernel

theorem check04 : FiniteCheck 7 4 := by
  unfold FiniteCheck retainedMass energyUpper
  rw [shellArray_eq_shellList]
  decide +kernel

theorem check05 : FiniteCheck 7 5 := by
  unfold FiniteCheck retainedMass energyUpper
  rw [shellArray_eq_shellList]
  decide +kernel

theorem check06 : FiniteCheck 7 6 := by
  unfold FiniteCheck retainedMass energyUpper
  rw [shellArray_eq_shellList]
  decide +kernel

theorem check07 : FiniteCheck 7 7 := by
  unfold FiniteCheck retainedMass energyUpper
  rw [shellArray_eq_shellList]
  decide +kernel

theorem check08 : FiniteCheck 7 8 := by
  unfold FiniteCheck retainedMass energyUpper
  rw [shellArray_eq_shellList]
  decide +kernel

theorem check09 : FiniteCheck 7 9 := by
  unfold FiniteCheck retainedMass energyUpper
  rw [shellArray_eq_shellList]
  decide +kernel

theorem check10 : FiniteCheck 7 10 := by
  unfold FiniteCheck retainedMass energyUpper
  rw [shellArray_eq_shellList]
  decide +kernel

theorem check11 : FiniteCheck 7 11 := by
  unfold FiniteCheck retainedMass energyUpper
  rw [shellArray_eq_shellList]
  decide +kernel

theorem check12 : FiniteCheck 7 12 := by
  unfold FiniteCheck retainedMass energyUpper
  rw [shellArray_eq_shellList]
  decide +kernel

theorem check13 : FiniteCheck 7 13 := by
  unfold FiniteCheck retainedMass energyUpper
  rw [shellArray_eq_shellList]
  decide +kernel

theorem check14 : FiniteCheck 7 14 := by
  unfold FiniteCheck retainedMass energyUpper
  rw [shellArray_eq_shellList]
  decide +kernel

theorem check15 : FiniteCheck 7 15 := by
  unfold FiniteCheck retainedMass energyUpper
  rw [shellArray_eq_shellList]
  decide +kernel

theorem check16 : FiniteCheck 7 16 := by
  unfold FiniteCheck retainedMass energyUpper
  rw [shellArray_eq_shellList]
  decide +kernel

theorem check17 : FiniteCheck 7 17 := by
  unfold FiniteCheck retainedMass energyUpper
  rw [shellArray_eq_shellList]
  decide +kernel

theorem check18 : FiniteCheck 7 18 := by
  unfold FiniteCheck retainedMass energyUpper
  rw [shellArray_eq_shellList]
  decide +kernel

theorem check19 : FiniteCheck 7 19 := by
  unfold FiniteCheck retainedMass energyUpper
  rw [shellArray_eq_shellList]
  decide +kernel

theorem check20 : FiniteCheck 7 20 := by
  unfold FiniteCheck retainedMass energyUpper
  rw [shellArray_eq_shellList]
  decide +kernel

theorem check21 : FiniteCheck 7 21 := by
  unfold FiniteCheck retainedMass energyUpper
  rw [shellArray_eq_shellList]
  decide +kernel

theorem checks : ∀ j : Fin 21, FiniteCheck 7 (j.val + 1) := by
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

end Legacy.BecknerOnofri.FiniteScalar.Dim07
