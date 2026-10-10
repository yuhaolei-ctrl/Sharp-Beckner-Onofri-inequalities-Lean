module

public import BecknerOnofri.V2.Reaudit.ElevenBounds.LabelEntropy
public import BecknerOnofri.V2.Eleven.Estimates

@[expose] public section

/-! # S025: `prop:section4-entropy-bound`, `Ent(ρ_*) < 8653/600`

The printed deduction: Lemma 4.3 (`lem:section4-periodization-entropy-identity`),
`Ent(ρ_*) = Ent_{ℝ^{11}}(η_{1/5}) + H_Sh(N|Y)`, Lemma 4.4 (`Ent_{ℝ^{11}}(η_{1/5}) < 721/50`) and Lemma 4.5
(`H_Sh(N|Y) < 1/600`), and `721/50 + 1/600 = 8653/600`.  The statement below keeps the printed constant
`8653/600`; the intermediate estimates are the existing ones (`V2.Eleven.euclidean_entropy_lt`, the
random-variable identity `JointLaw.periodization_entropy_identity`, and `condShannon_lt_printed`). -/

set_option linter.unusedSectionVars false

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace BecknerOnofri.V2.Reaudit.ElevenBounds

open BecknerOnofri.HighDim
open BecknerOnofri.V2.Eleven.JointLaw

/-- `721/50 + 1/600 = 8653/600`. -/
theorem entropy_constant_arith : (721 : ℝ) / 50 + 1 / 600 = 8653 / 600 := by norm_num

section RV

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → Fin 11 → ℝ}

/-- **`prop:section4-entropy-bound`, through the lattice-label random variables.** For any random vector `X`
with density `η_{1/5}` (such a space exists: `JointLaw.canonical_space`) and any probability density `ρ`
with value `ρ_*`:
`Ent(ρ_*) = Ent_{ℝ^{11}}(η_{1/5}) + H_Sh(N|Y) < 721/50 + 1/600 = 8653/600`. -/
theorem entropy_bound_via_rv (ρ : ProbabilityDensity 11) (hρ : ρ.value = Eleven.periodizedProfile)
    (hX : Measurable X) (hlaw : P.map X = lawEta) :
    entropy ρ = (∫ x, Eleven.etaEps (1 / 5) x * Real.log (Eleven.etaEps (1 / 5) x)) +
        condShannon P (rvN X) (rvY X) ∧
      entropy ρ < 8653 / 600 := by
  have hid := periodization_entropy_identity ρ hρ hX hlaw
  refine ⟨hid, ?_⟩
  have h1 := Eleven.euclidean_entropy_lt
  have h2 := condShannon_lt_printed hX hlaw
  rw [hid]
  linarith

end RV

/-- **Proposition `prop:section4-entropy-bound`** (printed constant): the periodized density satisfies
`Ent(ρ_*) < 8653/600`, with `Ent(ρ) = ∫ ρ log ρ dm_{11}`. -/
theorem entropy_bound_printed (ρ : ProbabilityDensity 11) (hρ : ρ.value = Eleven.periodizedProfile) :
    entropy ρ < 8653 / 600 := by
  obtain ⟨-, h⟩ := entropy_bound_via_rv (P := lawEta) (X := (id : (Fin 11 → ℝ) → Fin 11 → ℝ)) ρ hρ
    measurable_id (canonical_space.1)
  exact h

/-- The same bound, for the extended-real entropy `torusEntropy` used in the repository's statements. -/
theorem torusEntropy_bound_printed (ρ : ProbabilityDensity 11)
    (hρ : ρ.value = Eleven.periodizedProfile) :
    (Vocab.torusEntropy ρ.value).toReal < 8653 / 600 := by
  have hfin := Eleven.finiteEntropy_of_value_eq ρ hρ
  rw [← Vocab.entropy_eq_toReal_torusEntropy ρ hfin]
  exact entropy_bound_printed ρ hρ

/-- The sharper repository value `18011/1250` (a bridge, not a replacement of the printed constant). -/
theorem entropy_bound_printed_of_sharper (ρ : ProbabilityDensity 11)
    (hρ : ρ.value = Eleven.periodizedProfile) : entropy ρ < 8653 / 600 :=
  (HighDim.Eleven.competitor_entropy ρ hρ).trans (by norm_num)

end BecknerOnofri.V2.Reaudit.ElevenBounds
