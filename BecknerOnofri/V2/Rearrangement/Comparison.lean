module

public import BecknerOnofri.V2.Rearrangement.EnergyComparison
public import BecknerOnofri.SuccessiveCoordinateRearrangement
public import BecknerOnofri.CanonicalRearrangementClasses
public import BecknerOnofri.OptimizerEulerPaper
public import BecknerOnofri.RawOptimizerCorrespondence
public import BecknerOnofri.PrescribedSelectionDefinitions
public import BecknerOnofri.OptimizerDuality
public import BecknerOnofri.SmoothTorusLipschitz

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


/-! ## Obligation O1: why the intermediate measurability is part of the hypothesis

`AESuccessiveSteiner f g` (`AECanonicalChain (List.finRange d) f g`) places **no** measurability
condition on the intermediate functions `h₁, …, h_{d-1}`; only the first and the last function are
constrained (`f`, `g` are densities).  The statement "an intermediate stage `h` with
`AECanonicalStep i f h`, `f` measurable, is a.e. strongly measurable" is **false in ZFC**:

* take `d = 2`, `f ≡ 1`, `i = 0`; then `AECanonicalStep 0 f h` says only that for a.e. `x₁` the
  function `x₀ ↦ h(x₀,x₁)` equals `1` a.e.;
* let `N ⊆ 𝕋²` meet every horizontal line in at most one point and meet every closed set of
  positive measure (transfinite recursion over the continuum many closed sets of positive measure,
  each of which has a positive-measure, hence size-continuum, projection to the `x₁`-axis);
  then `N` is not Lebesgue measurable (a measurable set meeting every closed positive-measure set
  has full measure, but all its horizontal sections are null), and `h = 1 + 1_N` satisfies the
  step condition while being a.e. equal to no measurable function.

Consequently the pair `(AEStronglyMeasurable h)` carried by `MeasChain.cons` cannot be derived from
the other data, and the replacement `MeasSuccessive ⟶ AESuccessiveSteiner` is not available by a
measure-theoretic argument.  (Whether the *conclusion* of `successive_rearrangement_energy_le`
survives for non-measurable intermediate stages is a different question, depending on how
`Circle.realRearrange` treats non-measurable fibres; I do not claim it either way.)

What is proved instead (and is all that the proof of Lemma 2.9, of Lemma 3.1 and of the existence of
minimizing mixtures needs):

* `MeasChain.congr_left`, `MeasChain.integrable_nonneg_integral`, `MeasChain.density`: the chain is
  invariant under a.e. changes of the starting function, and transports a probability density to
  a probability density (`step_integrable` at every stage);
* `exists_meas_chain`: for a Lipschitz nonnegative bounded continuous `f` the repository's
  construction of `exists_canonical_chain` produces a `MeasChain` (the intermediate stages are
  bounded continuous functions, hence measurable), which also records `SteinerAt j g` for all `j`;
* `coordinate_rearranged_minimizer`: the manuscript wrapper of Lemma 2.9. -/

theorem MeasChain.congr_left {is : List (Fin d)} {f f' g : Torus d → ℝ}
    (h : MeasChain is f g) (he : f' =ᵐ[torusMeasure d] f) : MeasChain is f' g := by
  cases h with
  | nil hh => exact .nil (he.trans hh)
  | cons hm hs ht => exact .cons hm (hs.congr_left he) ht

/-- Along a `MeasChain` the starting integrable nonnegative function keeps its integral, and the
end point is a.e. strongly measurable, integrable and nonnegative. -/
theorem MeasChain.integrable_nonneg_integral {is : List (Fin d)} {f g : Torus d → ℝ}
    (h : MeasChain is f g) (hfm : AEStronglyMeasurable f (torusMeasure d))
    (hf : Integrable f (torusMeasure d)) (hf0 : ∀ᵐ x ∂torusMeasure d, 0 ≤ f x) :
    AEStronglyMeasurable g (torusMeasure d) ∧ Integrable g (torusMeasure d) ∧
      (∀ᵐ x ∂torusMeasure d, 0 ≤ g x) ∧ ∫ x, g x ∂torusMeasure d = ∫ x, f x ∂torusMeasure d := by
  induction h with
  | nil hfg =>
    refine ⟨hfm.congr hfg, hf.congr hfg, ?_, integral_congr_ae hfg.symm⟩
    filter_upwards [hf0, hfg] with x h1 h2
    rwa [← h2]
  | cons hm hs _ ih =>
    obtain ⟨hint, hnn, hmass⟩ := step_integrable _ hf hf0 hm hs
    obtain ⟨a, b, c, e⟩ := ih hm hint hnn
    exact ⟨a, b, c, e.trans hmass⟩

/-- The probability density at the end of a `MeasChain` started at a probability density. -/
def MeasChain.density {is : List (Fin d)} {r : ProbabilityDensity d} {g : Torus d → ℝ}
    (h : MeasChain is r.value g) : ProbabilityDensity d where
  value := g
  nonneg := (h.integrable_nonneg_integral r.integrable.1 r.integrable r.nonneg).2.2.1
  integrable := (h.integrable_nonneg_integral r.integrable.1 r.integrable r.nonneg).2.1
  mass := ((h.integrable_nonneg_integral r.integrable.1 r.integrable r.nonneg).2.2.2).trans r.mass

@[simp] theorem MeasChain.density_value {is : List (Fin d)} {r : ProbabilityDensity d}
    {g : Torus d → ℝ} (h : MeasChain is r.value g) : h.density.value = g := rfl

open scoped NNReal BoundedContinuousFunction in
/-- **Existence of a measurable chain of canonical coordinate rearrangements.**  Same construction as
`exists_canonical_chain` (every intermediate stage is a Lipschitz bounded continuous function), now
recording the `MeasChain` structure, and the Steiner property in every listed coordinate. -/
theorem exists_meas_chain (is : List (Fin d)) {K : ℝ≥0} (f : Torus d →ᵇ ℝ)
    (hf : LipschitzWith K f) (hf0 : ∀ x, 0 ≤ f x) :
    ∃ g : Torus d →ᵇ ℝ, MeasChain is (f : Torus d → ℝ) g ∧ LipschitzWith K g ∧
      (∀ x, 0 ≤ g x) ∧ (∀ j ∈ is, CoordinateRearrangement.SteinerAt j g) ∧
      (∀ j, CoordinateRearrangement.SteinerAt j f → CoordinateRearrangement.SteinerAt j g) := by
  induction is generalizing f with
  | nil => exact ⟨f, .nil Filter.EventuallyEq.rfl, hf, hf0, by simp, fun _ h => h⟩
  | cons i is ih =>
    obtain ⟨h, hh, hhL, _, hhS, hhCanon⟩ :=
      CoordinateRearrangement.exists_canonical_coordinate_limit i f hf hf0
    have hh0 := CoordinateRearrangement.closure_nonneg hf0 hh
    obtain ⟨g, hgChain, hgL, hg0, hgS, hgKeep⟩ := ih h hhL hh0
    have hhi : CoordinateRearrangement.SteinerAt i h :=
      CoordinateRearrangement.steinerAt_of_fibers hhS
    have hkeep (j : Fin d) (hj : CoordinateRearrangement.SteinerAt j f) :
        CoordinateRearrangement.SteinerAt j h := by
      by_cases hji : j = i
      · simpa only [hji] using hhi
      · exact CoordinateRearrangement.closure_preserves_steinerAt hji hj hh
    refine ⟨g, .cons h.continuous.aestronglyMeasurable (Filter.Eventually.of_forall hhCanon) hgChain,
      hgL, hg0, ?_, ?_⟩
    · intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact hgKeep _ hhi
      · exact hgS j hj
    · intro j hj
      exact hgKeep j (hkeep j hj)


/-- Equal entropies and `pressureValue β η ≤ pressureValue β r` (`β > 0`) force
`spectralEnergy η ≤ spectralEnergy r`. -/
theorem spectralEnergy_le_of_pressureValue_le (hd : 0 < d) {β : ℝ} (hβ : 0 < β)
    (r η : ProbabilityDensity d) (hr : r.FiniteEntropy) (hη : η.FiniteEntropy)
    (hent : entropy η = entropy r) (h : pressureValue β η ≤ pressureValue β r) :
    spectralEnergy η ≤ spectralEnergy r := by
  have h1 := finiteEntropy_spectralEnergy_ne_top hd r hr
  have h2 := finiteEntropy_spectralEnergy_ne_top hd η hη
  unfold pressureValue at h
  rw [hent, ← EReal.coe_ennreal_toReal h1, ← EReal.coe_ennreal_toReal h2, ← EReal.coe_mul,
    ← EReal.coe_mul, ← EReal.coe_sub, ← EReal.coe_sub, EReal.coe_le_coe_iff] at h
  have hσ : 0 < spectralThreshold d := by
    unfold spectralThreshold
    have hd' : (0 : ℝ) < d := by exact_mod_cast hd
    have := Real.Gamma_pos_of_pos (by positivity : (0 : ℝ) < (d : ℝ) / 2)
    positivity
  have hc : 0 < β / (2 * spectralThreshold d) := by positivity
  have : (spectralEnergy η).toReal ≤ (spectralEnergy r).toReal := by
    by_contra hlt
    replace hlt := not_le.mp hlt
    nlinarith [mul_lt_mul_of_pos_left hlt hc]
  exact (ENNReal.toReal_le_toReal h2 h1).1 this

open scoped NNReal BoundedContinuousFunction in
/-- **Lemma 2.9 (`lem:coordinate-rearranged-minimizer`), minimizer wrapper.**

Let `ρ` be a smooth minimizer of the free energy at coupling `β > 0` (the manuscript takes
`0 < β < 2d`; the argument uses only `β > 0`, in particular it also applies at the attained
endpoint `β = 2d`).  Rearrange it successively in the coordinates `1, …, d`
(`MeasSuccessive ρ.value η.value`, the successive coordinate Steiner symmetrizations).  Then the
result `η` is a bounded minimizer with the same entropy, distribution and (by
`eq:coordinate-free-energy-comparison` and the minimality of `ρ`) the same energy; it is smooth,
strictly positive, `η = e^{u}/∫e^{u}` for the smooth mean-zero potential `u = β g ∗ η`
(Euler relation in Fourier variables), and both `η` and `u` are separately even and nonincreasing
in each coordinate on `[0,1/2]`.

Route: `eq:coordinate-free-energy-comparison` is `rearranged_pressureValue_ge` (written route);
smoothness/positivity/Gibbs form of the new minimizer is the repository's attained-extremizer
regularity (`continuous_optimizer_of_minimizer`, `raw_optimizer_euler`, Corollary 2.6), used instead
of the relative-entropy computation `eq:coordinate-minimizer-gap` (see `coordinate_minimizer_gap`
for that identity). -/
theorem coordinate_rearranged_minimizer (hd : 0 < d) {β : ℝ} (hβ : 0 < β)
    (ρ : ProbabilityDensity d) (hρ : IsGlobalMinimizer β ρ) (hρs : SmoothOnTorus ρ.value) :
    ∃ (η : ProbabilityDensity d) (u : Torus d → ℝ),
      MeasSuccessive ρ.value η.value ∧ IsGlobalMinimizer β η ∧
      spectralEnergy ρ ≤ spectralEnergy η ∧ spectralEnergy η = spectralEnergy ρ ∧
      IdentDistrib η.value ρ.value (torusMeasure d) (torusMeasure d) ∧
      torusEntropy η.value = torusEntropy ρ.value ∧ entropy η = entropy ρ ∧
      pressureValue β η = pressureValue β ρ ∧
      η.value = normalizedGibbs u ∧ SmoothOnTorus η.value ∧ (∀ x, 0 < η.value x) ∧
      SmoothOnTorus u ∧ MeanZero u ∧ InCriticalSobolev u ∧
      u =ᵐ[torusMeasure d] Gap.densityPotential β η.value ∧
      (∀ k : NonzeroFrequency d, (frequencyLength k.val ^ d : ℂ) * fourierCoeff u k.val =
        (β / spectralThreshold d : ℝ) * fourierCoeff η.value k.val) ∧
      PrescribedSelection.CoordinateSteiner η.value ∧ PrescribedSelection.CoordinateSteiner u := by
  have : (torusMeasure d).IsOpenPosMeasure := by unfold torusMeasure; infer_instance
  obtain ⟨K, hK⟩ := hρs.exists_lipschitz
  let f : Torus d →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact ⟨ρ.value, hK.continuous⟩
  have hfv : (f : Torus d → ℝ) = ρ.value := rfl
  have hf0 : ∀ x, 0 ≤ f x := by
    have he : (fun x => max (ρ.value x) 0) =ᵐ[torusMeasure d] ρ.value :=
      ρ.nonneg.mono (fun _ h => max_eq_left h)
    have hh := Measure.eq_of_ae_eq he (hK.continuous.max continuous_const) hK.continuous
    intro x
    exact (le_max_right (ρ.value x) 0).trans_eq (congrFun hh x)
  obtain ⟨g, hch, hgL, hg0, hgS, -⟩ := exists_meas_chain (List.finRange d) f hK hf0
  rw [hfv] at hch
  let η : ProbabilityDensity d := hch.density
  have hηv : η.value = g := rfl
  have hM : ∀ᵐ x ∂torusMeasure d, ρ.value x ≤ ‖f‖ :=
    Filter.Eventually.of_forall (fun x => (Real.le_norm_self _).trans (f.norm_coe_le_norm x))
  obtain ⟨he, hb, hid, hent⟩ := successive_rearrangement_energy_le hd ρ η ‖f‖ hM hch
  have hρf := hρ.1
  have hηf : η.FiniteEntropy := by
    rw [← torusEntropy_density_ne_top_iff, hent]
    exact (torusEntropy_density_ne_top_iff ρ).2 hρf
  have hent' : entropy η = entropy ρ := by
    rw [entropy_eq_toReal_torusEntropy η hηf, entropy_eq_toReal_torusEntropy ρ hρf, hent]
  have hge := rearranged_pressureValue_ge hd β hβ.le ρ η ‖f‖ hM hch
  have hηmin : IsGlobalMinimizer β η := ⟨hηf, fun σ hσ => (hρ.2 σ hσ).trans hge⟩
  have hpv : pressureValue β η = pressureValue β ρ :=
    (OptimizerDuality.minimizer_value_eq_pressure hηmin).trans
      (OptimizerDuality.minimizer_value_eq_pressure hρ).symm
  have hee : spectralEnergy η = spectralEnergy ρ :=
    le_antisymm (spectralEnergy_le_of_pressureValue_le hd hβ ρ η hρf hηf hent' hpv.le) he
  obtain ⟨u, hu, hm, hus, -, hmax, hg⟩ := OptimizerDuality.continuous_optimizer_of_minimizer hd hβ η hηmin
  have hgc : Continuous g := g.continuous
  have hnc : Continuous (normalizedGibbs u) := by
    obtain ⟨K', hK'⟩ := (OptimizerDuality.normalizedGibbs_smooth u hus).exists_lipschitz
    exact hK'.continuous
  have hgu : η.value = normalizedGibbs u := Measure.eq_of_ae_eq hg hgc hnc
  have hgpos : ∀ x, 0 < η.value x := by
    intro x
    rw [hgu]
    rw [← ContinuousGibbs.normalized_apply]
    exact ContinuousGibbs.normalized_pos u x
  have hst : PrescribedSelection.CoordinateSteiner η.value :=
    ⟨fun i x => (hgS i (List.mem_finRange i)).1 x, fun x i => (hgS i (List.mem_finRange i)).2 x⟩
  refine ⟨η, u, hch, hηmin, he, hee, hid, hent, hent', hpv, hgu, ?_, hgpos, hus, hm, hu, ?_,
    ?_, hst, ?_⟩
  · rw [hgu]; exact OptimizerDuality.normalizedGibbs_smooth u hus
  · have h := OptimizerDuality.continuous_optimizer_green hd hβ u hu hm hmax
    rw [← hgu] at h
    exact h
  · intro k
    have h := OptimizerDuality.raw_optimizer_euler hd hβ u hu hm hmax k
    rw [← hgu] at h
    exact h
  · exact Legacy.BecknerOnofri.SteinerSelection.steiner_of_normalized_exp
      (ContinuousGibbs.partition_pos u) (by
        have h := hst
        rw [hgu] at h
        change Legacy.BecknerOnofri.SteinerSelection.Steiner
          (fun x => Real.exp (u x) / (∫ y, Real.exp (u y) ∂torusMeasure d)) at h
        simpa only [ContinuousGibbs.partition, ContinuousGibbs.mean_apply,
          ContinuousGibbs.exponential_apply] using h)

#print axioms MeasChain.density
#print axioms exists_meas_chain
#print axioms coordinate_rearranged_minimizer

end BecknerOnofri.V2.Rearrangement
