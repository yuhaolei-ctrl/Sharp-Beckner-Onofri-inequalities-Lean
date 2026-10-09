module

public import BecknerOnofri.V2.Rearrangement.EnergyComparison

@[expose] public section

/-! # Lemma 2.9: the bounded-density energy comparison (written route)

Statements (valid for every coupling `β ≥ 0`, in particular `β = 2d`; no minimizer, no
subcriticality, no smoothness, no endpoint inequality):

* `coordinate_rearrangement_energy_le` — one coordinate step
  `r ↦ s` (`AECanonicalStep i r s`) of a bounded density: `‖r‖² ≤ ‖s‖²`, `s ≤ M`, `s ~ r`,
  `Ent(s) = Ent(r)` (`eq:coordinate-free-energy-comparison`, `eq:coordinate-rearrangement-invariants`);
* `successive_rearrangement_energy_le` — all coordinates in order;
* `rearranged_pressureValue_ge` — `pressureValue β r ≤ pressureValue β η`.

Proof (the written one): Lemma 2.8 per fiber pair (`Circle.circle_rearrangement`) times the nonnegative
remaining heat kernels, integrated by Fubini over the fiber coordinates (`heat_pairing_step_le`),
then the Plancherel/Tonelli representation of the energy through the heat pairing
(`spectralEnergy_le_of_heat_pairing_le`). -/

noncomputable section
open MeasureTheory Set ProbabilityTheory
open BecknerOnofri.HighDim BecknerOnofri.HighDim.CoordinateRearrangementStatement
open scoped ENNReal

namespace BecknerOnofri.V2.Rearrangement
open BecknerOnofri.V2.Vocab

variable {d : ℕ}

/-- A density bounded a.e. has finite entropy. -/
theorem finiteEntropy_of_ae_le (r : ProbabilityDensity d) {M : ℝ}
    (hM : ∀ᵐ x ∂torusMeasure d, r.value x ≤ M) : r.FiniteEntropy := by
  unfold ProbabilityDensity.FiniteEntropy
  refine Integrable.mono' (integrable_const (1 + M ^ 2)) ?_ ?_
  · exact Real.continuous_mul_log.comp_aestronglyMeasurable r.integrable.1
  · filter_upwards [hM, r.nonneg] with x h1 h2
    rw [Real.norm_eq_abs, abs_le]
    refine ⟨?_, ?_⟩
    · have := neg_mul_log_le_one h2
      nlinarith [sq_nonneg M]
    · rcases h2.eq_or_lt with h0 | hpos
      · rw [← h0]; simp; positivity
      · have hlog : Real.log (r.value x) ≤ r.value x - 1 := Real.log_le_sub_one_of_pos hpos
        have h3 : r.value x * Real.log (r.value x) ≤ r.value x * (r.value x - 1) :=
          mul_le_mul_of_nonneg_left hlog h2
        nlinarith [sq_nonneg M, mul_le_mul h1 h1 h2 (h2.trans h1)]

/-- **Lemma 2.9, one coordinate (bounded-density energy comparison).**
`r` bounded, `s` its canonical circle rearrangement in coordinate `i` (a.e. fiber). -/
theorem coordinate_rearrangement_energy_le (hd : 0 < d) (i : Fin d)
    (r s : ProbabilityDensity d) (M : ℝ) (hM : ∀ᵐ x ∂torusMeasure d, r.value x ≤ M)
    (hstep : AECanonicalStep i r.value s.value) :
    spectralEnergy r ≤ spectralEnergy s ∧
    (∀ᵐ x ∂torusMeasure d, s.value x ≤ M) ∧
    IdentDistrib s.value r.value (torusMeasure d) (torusMeasure d) ∧
    torusEntropy s.value = torusEntropy r.value := by
  have hr := finiteEntropy_of_ae_le r hM
  have hid := step_identDistrib i r.integrable r.nonneg s.integrable.1 hstep
  have hent : torusEntropy s.value = torusEntropy r.value :=
    step_homEntropy_eq i r.integrable r.nonneg s.integrable.1 hstep
  have hs : s.FiniteEntropy := by
    rw [← torusEntropy_density_ne_top_iff, hent]
    exact (torusEntropy_density_ne_top_iff r).2 hr
  refine ⟨?_, step_ae_le i r.integrable r.nonneg s.integrable.1 hstep hM, hid, hent⟩
  refine spectralEnergy_le_of_heat_pairing_le hd r s hr hs (fun τ hτ => ?_)
  exact heat_pairing_step_le hτ i r.integrable s.integrable r.nonneg hstep

/-- Successive canonical coordinate rearrangements, **with a.e. strongly measurable intermediate
stages**.  This is the repository's `AECanonicalChain` plus the measurability of every
intermediate function (needed for the intermediate stages to be densities; for the chains that
actually arise, which have continuous intermediate stages, it is automatic).  See
`MeasChain.toChain` for the forgetful map. -/
inductive MeasChain : List (Fin d) → (Torus d → ℝ) → (Torus d → ℝ) → Prop
  | nil {f g : Torus d → ℝ} : f =ᵐ[torusMeasure d] g → MeasChain [] f g
  | cons {i : Fin d} {is : List (Fin d)} {f h g : Torus d → ℝ} :
      AEStronglyMeasurable h (torusMeasure d) → AECanonicalStep i f h → MeasChain is h g →
        MeasChain (i :: is) f g

theorem MeasChain.toChain {is : List (Fin d)} {f g : Torus d → ℝ} (h : MeasChain is f g) :
    AECanonicalChain is f g := by
  induction h with
  | nil hfg => exact .nil hfg
  | cons _ hs _ ih => exact .cons hs ih

/-- The successive coordinate rearrangement `r ↦ η` in the original coordinate order. -/
def MeasSuccessive (f g : Torus d → ℝ) : Prop := MeasChain (List.finRange d) f g

theorem MeasSuccessive.toSteiner {f g : Torus d → ℝ} (h : MeasSuccessive f g) :
    AESuccessiveSteiner f g := MeasChain.toChain h

theorem fourierCoeff_congr_ae' {u v : Torus d → ℝ} (h : u =ᵐ[torusMeasure d] v) :
    BecknerOnofri.HighDim.fourierCoeff u = BecknerOnofri.HighDim.fourierCoeff v := by
  funext k
  unfold BecknerOnofri.HighDim.fourierCoeff
  apply integral_congr_ae
  filter_upwards [h] with x hx
  rw [hx]

theorem spectralEnergy_congr_ae {ρ η : ProbabilityDensity d}
    (h : ρ.value =ᵐ[torusMeasure d] η.value) : spectralEnergy ρ = spectralEnergy η := by
  unfold spectralEnergy spectralTerm
  simp only [fourierCoeff_congr_ae' h]

/-- Lemma 2.9 for an arbitrary list of coordinates. -/
theorem chain_energy_le (hd : 0 < d) (is : List (Fin d)) :
    ∀ (r η : ProbabilityDensity d) (M : ℝ), (∀ᵐ x ∂torusMeasure d, r.value x ≤ M) →
      MeasChain is r.value η.value →
      spectralEnergy r ≤ spectralEnergy η ∧
      (∀ᵐ x ∂torusMeasure d, η.value x ≤ M) ∧
      IdentDistrib η.value r.value (torusMeasure d) (torusMeasure d) ∧
      torusEntropy η.value = torusEntropy r.value := by
  induction is with
  | nil =>
    intro r η M hM h
    cases h with
    | nil he =>
      refine ⟨(spectralEnergy_congr_ae he).le, ?_, ?_, ?_⟩
      · filter_upwards [hM, he] with x h1 h2
        rwa [← h2]
      · exact IdentDistrib.of_ae_eq r.integrable.1.aemeasurable he |>.symm
      · exact homEntropy_congr_ae he.symm
  | cons i is ih =>
    intro r η M hM h
    cases h with
    | cons hmeas hstep hrest =>
      rename_i h1
      obtain ⟨hint, hnn, hmass⟩ := step_integrable i r.integrable r.nonneg hmeas hstep
      let r₁ : ProbabilityDensity d :=
        { value := h1, nonneg := hnn, integrable := hint, mass := hmass.trans r.mass }
      obtain ⟨e1, b1, d1, h1e⟩ := coordinate_rearrangement_energy_le hd i r r₁ M hM hstep
      obtain ⟨e2, b2, d2, h2e⟩ := ih r₁ η M b1 hrest
      exact ⟨e1.trans e2, b2, d2.trans d1, h2e.trans h1e⟩

/-- **Lemma 2.9 (bounded-density energy comparison).**  All coordinates, in order. -/
theorem successive_rearrangement_energy_le (hd : 0 < d)
    (r η : ProbabilityDensity d) (M : ℝ) (hM : ∀ᵐ x ∂torusMeasure d, r.value x ≤ M)
    (h : MeasSuccessive r.value η.value) :
    spectralEnergy r ≤ spectralEnergy η ∧ (∀ᵐ x ∂torusMeasure d, η.value x ≤ M) ∧
    IdentDistrib η.value r.value (torusMeasure d) (torusMeasure d) ∧
    torusEntropy η.value = torusEntropy r.value :=
  chain_energy_le hd _ r η M hM h

/-- **Free energy never decreases** (`Ε_β(η) ≤ Ε_β(r)`), for every coupling `β ≥ 0`,
in particular `β = 2d`. -/
theorem rearranged_pressureValue_ge (hd : 0 < d) (β : ℝ) (hβ : 0 ≤ β)
    (r η : ProbabilityDensity d) (M : ℝ) (hM : ∀ᵐ x ∂torusMeasure d, r.value x ≤ M)
    (h : MeasSuccessive r.value η.value) :
    pressureValue β r ≤ pressureValue β η := by
  obtain ⟨he, hb, hid, hent⟩ := successive_rearrangement_energy_le hd r η M hM h
  have hr := finiteEntropy_of_ae_le r hM
  have hη : η.FiniteEntropy := by
    rw [← torusEntropy_density_ne_top_iff, hent]
    exact (torusEntropy_density_ne_top_iff r).2 hr
  have hent' : entropy η = entropy r := by
    rw [entropy_eq_toReal_torusEntropy η hη, entropy_eq_toReal_torusEntropy r hr, hent]
  have h1 := finiteEntropy_spectralEnergy_ne_top hd r hr
  have h2 := finiteEntropy_spectralEnergy_ne_top hd η hη
  unfold pressureValue
  rw [hent', ← EReal.coe_ennreal_toReal h1, ← EReal.coe_ennreal_toReal h2, ← EReal.coe_mul,
    ← EReal.coe_mul, ← EReal.coe_sub, ← EReal.coe_sub, EReal.coe_le_coe_iff]
  have hσ : 0 < spectralThreshold d := by
    unfold spectralThreshold
    have hd' : (0 : ℝ) < d := by exact_mod_cast hd
    have := Real.Gamma_pos_of_pos (by positivity : (0 : ℝ) < (d : ℝ) / 2)
    positivity
  have := ENNReal.toReal_mono h2 he
  have hc : 0 ≤ β / (2 * spectralThreshold d) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left this hc]

end BecknerOnofri.V2.Rearrangement
