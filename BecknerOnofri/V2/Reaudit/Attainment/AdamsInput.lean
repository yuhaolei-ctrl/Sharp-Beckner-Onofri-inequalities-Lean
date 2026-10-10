module

public import BecknerOnofri.V2.Reaudit.Attainment.Adams
public import BecknerOnofri.V2.Vocab.ExternalInputs

@[expose] public section

/-! # The printed critical Adams inequality implies `CriticalAdamsAboveThreshold` (package `Attainment`)

`BecknerOnofri.V2.Vocab.CriticalAdamsInput d` is the named hypothesis for `eq:section2-critical-adams`.
This file is separate from `Adams.lean` so that the direct method itself does not import
`V2.Vocab.ExternalInputs`. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped Topology ENNReal

namespace BecknerOnofri.V2.Reaudit.Attainment
open BecknerOnofri.HighDim

variable {d : ℕ}

/-- The printed critical Adams inequality implies the consequence used in Section 2. -/
theorem criticalAdamsAboveThreshold_of_input (hd : 0 < d)
    (h : BecknerOnofri.V2.Vocab.CriticalAdamsInput d) : CriticalAdamsAboveThreshold d := by
  obtain ⟨B, hB⟩ := (BecknerOnofri.V2.Vocab.criticalAdamsInput_iff hd).mp h
  intro a ha
  refine ⟨B, fun u hu hm => ?_⟩
  have hint := exp_centered_integrable hd u hu
  rw [centered_eq_self hm] at hint
  refine ⟨hint, ?_⟩
  have h1 := hB u hu
  rw [logPartition_eq_log_integral hd u hu, centered_eq_self hm] at h1
  have h2 := EReal.coe_le_coe_iff.mp h1
  have hE : 0 ≤ potentialEnergy u := potentialEnergy_nonneg u
  nlinarith

end BecknerOnofri.V2.Reaudit.Attainment
