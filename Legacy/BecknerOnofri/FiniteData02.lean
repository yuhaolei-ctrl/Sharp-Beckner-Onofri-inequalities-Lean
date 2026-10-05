module

public import Legacy.BecknerOnofri.FiniteScalarCore

@[expose] public section
namespace Legacy.BecknerOnofri.FiniteScalar.Case02
open Legacy.D10.FiniteScalar
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def rowData : Array Nat := #[6, 8, 2, 0, 0, 0, 0, 0, 0]
theorem row_correct : rowData = radialRow 2 := by decide +kernel
def stage : Nat → Array Nat
  | 0 => initialCoefficients
  | 1 => #[6, 8, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 2 => #[36, 96, 64, 0, 24, 32, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 3 => #[216, 864, 1152, 512, 216, 576, 384, 0, 72, 96, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 4 => #[1296, 6912, 13824, 12288, 5824, 6912, 9216, 4096, 864, 2304, 1536, 0, 192, 256, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 5 => #[7776, 51840, 138240, 184320, 135840, 101888, 138240, 122880, 49600, 34560, 46080, 20480, 2880, 7680, 5120, 0, 480, 640, 0, 0, 32, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 6 => #[46656, 373248, 1244160, 2211840, 2305152, 1801728, 1921024, 2211840, 1552320, 807936, 829440, 737280, 280320, 138240, 184320, 81920, 8640, 23040, 15360, 0, 1152, 1536, 0, 0, 64, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 7 => #[279936, 2612736, 10450944, 23224320, 31618944, 29998080, 28428288, 33062912, 31618944, 20869632, 15282176, 15482880, 10684800, 4687872, 3870720, 3440640, 1267840, 483840, 645120, 286720, 24192, 64512, 43008, 0, 2688, 3584, 0, 0, 128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 8 => #[1679616, 17915904, 83607552, 222953472, 376068096, 438165504, 431456256, 472252416, 517454848, 438165504, 315506688, 281280512, 251209728, 155344896, 91291648, 82575360, 56501760, 22421504, 15482880, 13762560, 4974592, 1548288, 2064384, 917504, 64512, 172032, 114688, 0, 6144, 8192, 0, 0, 256, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 9 => #[10077696, 120932352, 644972544, 2006581248, 4043395584, 5673369600, 6261276672, 6731071488, 7634884608, 7644962816, 6261276672, 5156241408, 4792412160, 3818078208, 2421522432, 1788346368, 1502032896, 897232896, 454852608, 371589120, 252951552, 93929472, 55738368, 49545216, 17676288, 4644864, 6193152, 2752512, 165888, 442368, 294912, 0, 13824, 18432, 0, 0, 512, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 10 => #[60466176, 806215680, 4837294080, 17199267840, 40333178880, 66629246976, 84244561920, 94489804800, 107744670720, 118295592960, 111249915904, 94489804800, 85274173440, 76537692160, 57596313600, 40414740480, 32903792640, 25035816960, 14750023680, 9445048320, 7494488064, 4381655040, 1995571200, 1486356480, 1008322560, 357138432, 185794560, 165150720, 58368000, 13271040, 17694720, 7864320, 414720, 1105920, 737280, 0, 30720, 40960, 0, 0, 1024, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | _ => #[]
theorem steps_correct : ∀ i : Fin 10, convolutionStep (stage i.val) rowData = stage (i.val+1) := by
  decide +kernel
theorem stage_correct (d : Nat) (hd : d ≤ 10) : shellArray 2 d = stage d := by
  induction d with
  | zero => rfl
  | succ d ih =>
      rw [shellArray_succ, ih (by omega), ← row_correct]
      exact steps_correct ⟨d, by omega⟩
theorem checked03 : FiniteCheck 3 2 := by
  unfold FiniteCheck Legacy.BecknerOnofri.FiniteScalar.retainedMass energyUpper
  rw [stage_correct 3 (by decide)]
  decide +kernel
theorem checked04 : FiniteCheck 4 2 := by
  unfold FiniteCheck Legacy.BecknerOnofri.FiniteScalar.retainedMass energyUpper
  rw [stage_correct 4 (by decide)]
  decide +kernel
theorem checked05 : FiniteCheck 5 2 := by
  unfold FiniteCheck Legacy.BecknerOnofri.FiniteScalar.retainedMass energyUpper
  rw [stage_correct 5 (by decide)]
  decide +kernel
theorem checked06 : FiniteCheck 6 2 := by
  unfold FiniteCheck Legacy.BecknerOnofri.FiniteScalar.retainedMass energyUpper
  rw [stage_correct 6 (by decide)]
  decide +kernel
theorem checked07 : FiniteCheck 7 2 := by
  unfold FiniteCheck Legacy.BecknerOnofri.FiniteScalar.retainedMass energyUpper
  rw [stage_correct 7 (by decide)]
  decide +kernel
theorem checked08 : FiniteCheck 8 2 := by
  unfold FiniteCheck Legacy.BecknerOnofri.FiniteScalar.retainedMass energyUpper
  rw [stage_correct 8 (by decide)]
  decide +kernel
theorem checked09 : FiniteCheck 9 2 := by
  unfold FiniteCheck Legacy.BecknerOnofri.FiniteScalar.retainedMass energyUpper
  rw [stage_correct 9 (by decide)]
  decide +kernel
theorem checked10 : FiniteCheck 10 2 := by
  unfold FiniteCheck Legacy.BecknerOnofri.FiniteScalar.retainedMass energyUpper
  rw [stage_correct 10 (by decide)]
  decide +kernel
theorem checked : ∀ i : Fin 8, FiniteCheck (i.val+3) 2 := by
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
end Legacy.BecknerOnofri.FiniteScalar.Case02
