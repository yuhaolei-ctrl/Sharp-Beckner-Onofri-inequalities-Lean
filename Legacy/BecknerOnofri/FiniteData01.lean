module

public import Legacy.BecknerOnofri.FiniteScalarCore

@[expose] public section
namespace Legacy.BecknerOnofri.FiniteScalar.Case01
open Legacy.D10.FiniteScalar
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def rowData : Array Nat := #[2, 2, 0, 0, 0, 0, 0, 0, 0]
theorem row_correct : rowData = radialRow 1 := by decide +kernel
def stage : Nat → Array Nat
  | 0 => initialCoefficients
  | 1 => #[2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 2 => #[4, 8, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 3 => #[8, 24, 24, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 4 => #[16, 64, 96, 64, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 5 => #[32, 160, 320, 320, 160, 32, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 6 => #[64, 384, 960, 1280, 960, 384, 64, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 7 => #[128, 896, 2688, 4480, 4480, 2688, 896, 128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 8 => #[256, 2048, 7168, 14336, 17920, 14336, 7168, 2048, 256, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 9 => #[512, 4608, 18432, 43008, 64512, 64512, 43008, 18432, 4608, 512, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 10 => #[1024, 10240, 46080, 122880, 215040, 258048, 215040, 122880, 46080, 10240, 1024, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | _ => #[]
theorem steps_correct : ∀ i : Fin 10, convolutionStep (stage i.val) rowData = stage (i.val+1) := by
  decide +kernel
theorem stage_correct (d : Nat) (hd : d ≤ 10) : shellArray 1 d = stage d := by
  induction d with
  | zero => rfl
  | succ d ih =>
      rw [shellArray_succ, ih (by omega), ← row_correct]
      exact steps_correct ⟨d, by omega⟩
theorem checked03 : FiniteCheck 3 1 := by
  unfold FiniteCheck Legacy.BecknerOnofri.FiniteScalar.retainedMass energyUpper
  rw [stage_correct 3 (by decide)]
  decide +kernel
theorem checked04 : FiniteCheck 4 1 := by
  unfold FiniteCheck Legacy.BecknerOnofri.FiniteScalar.retainedMass energyUpper
  rw [stage_correct 4 (by decide)]
  decide +kernel
theorem checked05 : FiniteCheck 5 1 := by
  unfold FiniteCheck Legacy.BecknerOnofri.FiniteScalar.retainedMass energyUpper
  rw [stage_correct 5 (by decide)]
  decide +kernel
theorem checked06 : FiniteCheck 6 1 := by
  unfold FiniteCheck Legacy.BecknerOnofri.FiniteScalar.retainedMass energyUpper
  rw [stage_correct 6 (by decide)]
  decide +kernel
theorem checked07 : FiniteCheck 7 1 := by
  unfold FiniteCheck Legacy.BecknerOnofri.FiniteScalar.retainedMass energyUpper
  rw [stage_correct 7 (by decide)]
  decide +kernel
theorem checked08 : FiniteCheck 8 1 := by
  unfold FiniteCheck Legacy.BecknerOnofri.FiniteScalar.retainedMass energyUpper
  rw [stage_correct 8 (by decide)]
  decide +kernel
theorem checked09 : FiniteCheck 9 1 := by
  unfold FiniteCheck Legacy.BecknerOnofri.FiniteScalar.retainedMass energyUpper
  rw [stage_correct 9 (by decide)]
  decide +kernel
theorem checked10 : FiniteCheck 10 1 := by
  unfold FiniteCheck Legacy.BecknerOnofri.FiniteScalar.retainedMass energyUpper
  rw [stage_correct 10 (by decide)]
  decide +kernel
theorem checked : ∀ i : Fin 8, FiniteCheck (i.val+3) 1 := by
  intro i
  fin_cases i
  · exact checked03
  · exact checked04
  · exact checked05
  · exact checked06
  · exact checked07
  · exact checked08
  · exact checked09
  · exact checked10
#print axioms checked
end Legacy.BecknerOnofri.FiniteScalar.Case01
