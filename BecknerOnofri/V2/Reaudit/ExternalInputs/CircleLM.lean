module

public import BecknerOnofri.V2.Section3.CircleBound
public import BecknerOnofri.V2.Vocab.ExternalInputs

@[expose] public section

/-! # `CircleLebedevMilinInput`: the circle Lebedev-Milin inequality as a theorem

`V2.Vocab.CircleLebedevMilinInput` is the manuscript's use of the Lebedev-Milin inequality
(`eq:intro-circle-LM`): `c_1 ‖ρ‖²_{Ḣ^{-1/2}} ≤ Ent(ρ)` for every finite-entropy density on `𝕋¹`.
The repository proves it **without** the low-dimensional endpoint chain: `Section3.circle_entropy_bound`
is the translation to the manuscript normalization of `Legacy.D10.CircleEntropy.entropy_bound`, which
proves the bound for the complete Fourier series by an Euler recurrence for the coefficients of the
exponential series (Milin's lemma).  Nothing here uses `EndpointThroughTen`, `physical_green_endpoint`
or any `d ≥ 2` result. -/

noncomputable section

namespace BecknerOnofri.V2.Reaudit.ExternalInputs
open BecknerOnofri.HighDim BecknerOnofri.V2.Vocab

/-- **`eq:intro-circle-LM` (Lebedev-Milin), as the Prop `CircleLebedevMilinInput`.** -/
theorem circleLebedevMilin : CircleLebedevMilinInput := by
  intro ρ hρ
  have h := BecknerOnofri.V2.Section3.circle_entropy_bound ρ hρ
  unfold BecknerOnofri.V2.Section3.EntropyBound at h
  simpa using h

/-- The `d = 1` case of `eq:section2-positive-threshold-input`, with `β₀ = 2`
(`β₀ c_1 / 2 = c_1`). -/
theorem positiveThreshold_one : PositiveThresholdInput 1 := by
  refine ⟨2, two_pos, fun ρ hρ => ?_⟩
  have h := circleLebedevMilin ρ hρ
  have : (2 : ℝ) * kernelConstant 1 / 2 = kernelConstant 1 := by ring
  rw [this]
  exact h

end BecknerOnofri.V2.Reaudit.ExternalInputs
