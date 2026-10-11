module

public import BecknerOnofri.V2.Reaudit.Obstruction.UniversalObstructions
public import BecknerOnofri.V2.Reaudit.ExternalInputs.CriticalAdams

@[expose] public section

/-! # Row S006: `lem:section2-universal-obstructions` with the critical Adams input discharged

`Obstruction.universal_obstructions` states finiteness of `C_d(A_crit(d))` conditionally on the
named hypothesis `V2.Vocab.CriticalAdamsInput d` (the printed critical Adams inequality, cited to
Lebedev--Milin and Okikiolu).  That hypothesis is now supplied for every `d ≥ 1` by
`V2.Reaudit.ExternalInputs.criticalAdams`, which does not depend on the endpoint chain.  This file
only composes the two; the concentration and first-shell parts are unchanged. -/

noncomputable section

namespace BecknerOnofri.V2.Reaudit.Obstruction

open BecknerOnofri.HighDim

variable {d : ℕ}

/-- **Finiteness at the critical coefficient.**  `C_d(A_crit(d)) < +∞`. -/
theorem coefficientDefect_critical_ne_top' (hd : 0 < d) :
    coefficientDefect d (collapseCoefficient d) ≠ ⊤ :=
  coefficientDefect_critical_ne_top hd (ExternalInputs.criticalAdams hd)

/-- **`lem:section2-universal-obstructions`**, all five assertions, unconditional. -/
theorem universal_obstructions_unconditional (hd : 0 < d) :
    (∀ β : ℝ, 2 * (d : ℝ) < β → pressure d β = ⊤) ∧
    (∀ A : ℝ, A < collapseCoefficient d → coefficientDefect d A = ⊤) ∧
    coefficientDefect d (collapseCoefficient d) ≠ ⊤ ∧
    (∀ β : ℝ, spectralThreshold d < β → 0 < pressure d β) ∧
    (∀ A : ℝ, A < spectralCoefficient d → 0 < coefficientDefect d A) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := universal_obstructions hd
  exact ⟨h1, h2, h3 (ExternalInputs.criticalAdams hd), h4, h5⟩

#print axioms universal_obstructions_unconditional

end BecknerOnofri.V2.Reaudit.Obstruction
