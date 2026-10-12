module

public import BecknerOnofri.V2.Reaudit.ElevenBounds.EntropyBound
public import BecknerOnofri.V2.Reaudit.ElevenBounds.ShellExpansion

@[expose] public section

/-! The upper bound `β_gm(11) < 2063/100` from the printed competitor bounds: the entropy of `ρ_*`
through the lattice-label random variables and its energy through the shell expansion. -/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace BecknerOnofri.V2.Reaudit.ElevenBounds
open BecknerOnofri.HighDim BecknerOnofri.V2.Vocab

/-- The entropy bound `Ent(ρ_*) < 7305164/10⁶ + 17897/2520 + 1/600` of `d11:eq:entropy-upper`, where
the term `1/600` is the lattice-label entropy bound of `lem:section4-lattice-label-entropy`
(`condShannon_lt_printed`, random-variable form with the chain rule). -/
theorem periodized_entropy_fine_written (ρ : ProbabilityDensity 11)
    (h : ρ.value = HighDim.Eleven.periodizedProfile) :
    (torusEntropy ρ.value).toReal < 7305164 / 10 ^ 6 + 17897 / 2520 + 1 / 600 := by
  have hρ := V2.Eleven.finiteEntropy_of_value_eq ρ h
  rw [← entropy_eq_toReal_torusEntropy ρ hρ]
  obtain ⟨hid, -⟩ := entropy_bound_via_rv
    (P := V2.Eleven.JointLaw.lawEta) (X := (id : (Fin 11 → ℝ) → Fin 11 → ℝ)) ρ h
    measurable_id (V2.Eleven.JointLaw.canonical_space.1)
  have h2 := condShannon_lt_printed
    (P := V2.Eleven.JointLaw.lawEta) (X := (id : (Fin 11 → ℝ) → Fin 11 → ℝ))
    measurable_id (V2.Eleven.JointLaw.canonical_space.1)
  rw [hid]
  linarith [V2.Eleven.euclidean_entropy_fine]

/-- `β_gm(11) < 2063/100`, from the printed competitor bounds (entropy through the label random
variables, energy through the full shell expansion). -/
theorem transition_upper_written (ρ : ProbabilityDensity 11)
    (h : ρ.value = HighDim.Eleven.periodizedProfile) :
    VariationalCurves.globalTransition 11 < 2063 / 100 :=
  V2.Eleven.globalTransition_lt_of_competitor ρ (V2.Eleven.finiteEntropy_of_value_eq ρ h)
    (periodized_entropy_fine_written ρ h) (energy_bound_via_shells ρ h)

end BecknerOnofri.V2.Reaudit.ElevenBounds
