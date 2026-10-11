module

public import BecknerOnofri.V2.Reaudit.ExternalInputs.PositiveThresholdIndependent
public import BecknerOnofri.V2.Reaudit.ExternalInputs.CircleLM

@[expose] public section

/-! # `PositiveThresholdInput d` in the printed shape: Lebedev-Milin for `d = 1`, the uniform route for `d ≥ 2`

The manuscript proves `eq:section2-positive-threshold-input` for `d = 1` from the Lebedev-Milin inequality
(`β₀ = 2`, `ExternalInputs.positiveThreshold_one`) and for `d ≥ 2` from [CdCRS2025, Thm 3].  Here the
`d ≥ 2` case is `positiveThreshold_independent` (critical Adams plus elementary estimates). -/

noncomputable section

namespace BecknerOnofri.V2.Reaudit.ExternalInputs
open BecknerOnofri.V2.Vocab

/-- The printed route for `d = 1` (Lebedev-Milin, `β₀ = 2`) and the uniform route for `d ≥ 2`. -/
theorem positiveThreshold_independent_print {d : ℕ} (hd : 0 < d) : PositiveThresholdInput d := by
  by_cases h1 : d = 1
  · subst h1; exact positiveThreshold_one
  · exact positiveThreshold_independent hd

/-- Statement identity: the new theorems have exactly the type `V2.Vocab.PositiveThresholdInput d`
(the displayed `eq:section2-positive-threshold-input`), the same as `ExternalInputs.positiveThreshold`. -/
example {d : ℕ} (hd : 0 < d) :
    type_of% (positiveThreshold_independent hd) = PositiveThresholdInput d := rfl

example {d : ℕ} (hd : 0 < d) :
    type_of% (positiveThreshold_independent_print hd) = PositiveThresholdInput d := rfl

example {d : ℕ} (hd : 0 < d) :
    type_of% (globalTransition_pos_independent hd) = (0 < HighDim.VariationalCurves.globalTransition d) := rfl

#print axioms BecknerOnofri.V2.Reaudit.ExternalInputs.positiveThreshold_independent_print

end BecknerOnofri.V2.Reaudit.ExternalInputs
