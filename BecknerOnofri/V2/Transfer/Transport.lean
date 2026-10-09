module

public import BecknerOnofri.MixtureMarginalEnergyPaper
public import BecknerOnofri.CountableMixtureSubsetMarginal
public import BecknerOnofri.ContinuousMixtureMajorant
public import BecknerOnofri.EntropyShearer.PaperStatement

@[expose] public section

/-! # Transport of a coordinate marginal of a continuous cosine mixture to a density on `𝕋^r`

For the written proof of Proposition 5.7 one applies the dimension-twelve hypothesis to the
`12`-marginals `ρ_I` of a minimizing cosine mixture `ρ`.  The repository represents `ρ_I` as a function
`coordinateMarginal ρ I` on the ambient torus `𝕋^d` (independent of the coordinates outside `I`);
`exists_marginal_density` produces the actual density on `𝕋^{|I|}` carrying the same `Ḣ^{-r/2}` energy
and the same entropy.  It is proved only for continuous mixtures (all that the written proof needs: the
selected minimizer is smooth), which avoids any measurability question for the marginal.  No
dimension-lifting induction is used. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped BigOperators ENNReal

namespace BecknerOnofri.V2.Transfer
open BecknerOnofri.HighDim

/-! ## Restriction of coordinates is measure preserving -/

/-- Restricting a product configuration along an injective coordinate map preserves the product of a
fixed probability measure. -/
theorem measurePreserving_restrict_pi {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] {m d : ℕ} (e : Fin m → Fin d) (he : Function.Injective e) :
    MeasurePreserving (fun (x : Fin d → X) (j : Fin m) => x (e j))
      (Measure.pi fun _ => μ) (Measure.pi fun _ => μ) := by
  classical
  have hmeas : Measurable (fun (x : Fin d → X) (j : Fin m) => x (e j)) :=
    measurable_pi_iff.mpr (fun j => measurable_pi_apply (e j))
  refine ⟨hmeas, ?_⟩
  symm
  refine Measure.pi_eq (fun s hs => ?_)
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hs)]
  let t : Fin d → Set X := Function.extend e s (fun _ => Set.univ)
  have ht1 : ∀ j, t (e j) = s j := fun j => he.extend_apply _ _ j
  have ht2 : ∀ i, i ∉ Set.range e → t i = Set.univ := fun i hi =>
    Function.extend_apply' _ _ _ (by simpa [Set.mem_range] using hi)
  have hpre : (fun (x : Fin d → X) (j : Fin m) => x (e j)) ⁻¹' (Set.univ.pi s) = Set.univ.pi t := by
    ext x
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro h i
      by_cases hi : i ∈ Set.range e
      · obtain ⟨j, rfl⟩ := hi
        rw [ht1]; exact h j
      · rw [ht2 i hi]; trivial
    · intro h j
      have := h (e j)
      rwa [ht1] at this
  rw [hpre, Measure.pi_pi]
  have hsub : ∏ i : Fin d, μ (t i) = ∏ i ∈ Finset.univ.image e, μ (t i) := by
    symm
    apply Finset.prod_subset (Finset.subset_univ _)
    intro i _ hi
    have : i ∉ Set.range e := by
      intro h; obtain ⟨j, rfl⟩ := h; exact hi (Finset.mem_image_of_mem _ (Finset.mem_univ _))
    rw [ht2 i this, measure_univ]
  rw [hsub, Finset.prod_image (fun a _ b _ h => he h)]
  exact Finset.prod_congr rfl (fun j _ => by rw [ht1])

/-! ## Coordinate masks of cosine-power tensors -/

section tensor
open Legacy.BecknerOnofri
open BecknerOnofri.CosineMixtureTransfer

theorem cosinePower_zero_ge_one' (n : ℕ) : 1 ≤ Legacy.D10.cosinePower n 0 := by
  have h := integral_mono (Legacy.D10.cosinePower_integrable n)
    (integrable_const (Legacy.D10.cosinePower n 0))
    (CosineMixtureApproximation.cosinePower_le_zero n)
  simpa only [CosineFourier.mass, integral_const, probReal_univ, smul_eq_mul, one_mul] using h

theorem cosinePower_zero_index (x : UnitAddCircle) : Legacy.D10.cosinePower 0 x = 1 := by
  simp [Legacy.D10.cosinePower]

/-- The mask of a tensor to the coordinates `I` is the tensor of the restricted index evaluated at the
restricted point. -/
theorem tensor_mask_eq {d : ℕ} (I : Finset (Fin d)) (N : Fin d → ℕ) (x : Torus d) :
    CosineMixture.tensor (maskIndex I N) x =
      CosineMixture.tensor (fun j : Fin I.card => N (coordinateEmbedding I j))
        (fun j : Fin I.card => x (coordinateEmbedding I j)) := by
  classical
  unfold CosineMixture.tensor
  have h1 : ∏ i : Fin d, Legacy.D10.cosinePower (maskIndex I N i) (x i) =
      ∏ i ∈ I, Legacy.D10.cosinePower (N i) (x i) := by
    symm
    rw [← Finset.prod_subset (Finset.subset_univ I)]
    · apply Finset.prod_congr rfl
      intro i hi
      simp [maskIndex, hi]
    · intro i _ hi
      simp [maskIndex, hi, cosinePower_zero_index]
  rw [h1]
  have hmap : (Finset.univ : Finset (Fin I.card)).map (coordinateEmbedding I) = I := by
    ext i
    simp only [Finset.mem_map, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨j, rfl⟩; exact coordinateEmbedding_mem I j
    · intro hi
      have : i ∈ Set.range (coordinateEmbedding I) := by
        rw [coordinateEmbedding_range]; exact hi
      exact this
  conv_lhs => rw [← hmap]
  rw [Finset.prod_map]

theorem tensor_mask_zero_le {d : ℕ} (I : Finset (Fin d)) (N : Fin d → ℕ) :
    CosineMixture.tensor (maskIndex I N) 0 ≤ CosineMixture.tensor N 0 := by
  unfold CosineMixture.tensor
  refine Finset.prod_le_prod₀ (fun i _ => Legacy.D10.cosinePower_nonneg _ _) (fun i _ => ?_)
  by_cases hi : i ∈ I
  · simp [maskIndex, hi]
  · simp only [maskIndex, hi, ite_false, cosinePower_zero_index]
    exact cosinePower_zero_ge_one' _

theorem tensor_embed_zero_le {d : ℕ} (I : Finset (Fin d)) (N : Fin d → ℕ) :
    CosineMixture.tensor (fun j : Fin I.card => N (coordinateEmbedding I j)) 0 ≤
      CosineMixture.tensor N 0 := by
  have h := tensor_mask_eq I N 0
  have h0 : (fun j : Fin I.card => (0 : Torus d) (coordinateEmbedding I j)) = 0 := rfl
  rw [h0] at h
  rw [← h]
  exact tensor_mask_zero_le I N

end tensor

/-! ## The transported marginal density -/

section transport
open Legacy.BecknerOnofri
open BecknerOnofri.CosineMixtureTransfer

/-- The restricted mixture `ρ_I` as a function on `𝕋^{|I|}`. -/
theorem marginal_ae_eq_restrict {d : ℕ} (ρ : ProbabilityDensity d) (I : Finset (Fin d))
    (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ) (hw : ∀ n, 0 ≤ w n) (hm : HasSum w 1)
    (he : ρ.value =ᵐ[torusMeasure d] CosineMixtureApproximation.rho w N) :
    coordinateMarginal ρ I =ᵐ[torusMeasure d] fun x =>
      CosineMixtureApproximation.rho w
        (fun n (j : Fin I.card) => N n (coordinateEmbedding I j))
        (fun j => x (coordinateEmbedding I j)) := by
  have h1 : coordinateMarginal ρ I = HighDim.EntropyShearer.fullAvg Iᶜ ρ.value := by
    rw [HighDim.EntropyShearer.coordinateMarginal_eq]; rfl
  rw [h1]
  refine ((fullAvg_congr_ae Iᶜ he).trans
    (fullAvg_countable_mixture_subset I w N hw hm)).trans (Filter.Eventually.of_forall ?_)
  intro x
  unfold CosineMixtureApproximation.rho
  exact tsum_congr (fun n => by rw [tensor_mask_eq])

/-- **Transport of a marginal.**  Let `ρ` be a continuous probability density on `𝕋^d` that is a
countable cosine mixture and let `I ⊆ {0,…,d-1}` have `r ≥ 1` elements.  Then there is a probability
density `ρ'` on `𝕋^r` with finite entropy, whose `Ḣ^{-r/2}` energy `spectralEnergy ρ'` is the
(`ℝ≥0∞`-valued) energy `inversePowerEnergy r (ρ_I)` of the `I`-marginal and whose entropy is the entropy
of the marginal. -/
theorem exists_marginal_density {d r : ℕ} (hr : 0 < r) (ρ : ProbabilityDensity d)
    (hρ : IsCountableCosineMixture ρ) (hc : Continuous ρ.value)
    (I : Finset (Fin d)) (hI : I.card = r) :
    ∃ ρ' : ProbabilityDensity r, ρ'.FiniteEntropy ∧
      spectralEnergy ρ' = inversePowerEnergy r (coordinateMarginal ρ I) ∧
      entropy ρ' = coordinateMarginalEntropy ρ I := by
  subst hI
  obtain ⟨w, N, hw, hm, he⟩ := hρ
  rw [countableCosineMixture_eq] at he
  have hSup := mixture_majorant_of_continuous ρ.value hc w N hw hm.summable he
  let N' : ℕ → Fin I.card → ℕ := fun n j => N n (coordinateEmbedding I j)
  have hSup' : Summable (fun n => w n * CosineMixture.tensor (N' n) 0) :=
    hSup.of_nonneg_of_le (fun n => mul_nonneg (hw n) (CosineMixture.tensor_nonneg _ _))
      (fun n => mul_le_mul_of_nonneg_left (tensor_embed_zero_le I (N n)) (hw n))
  let ρ' : ProbabilityDensity I.card :=
    { value := CosineMixtureApproximation.rho w N'
      nonneg := Filter.Eventually.of_forall (CosineMixtureApproximation.rho_nonneg w N' hw)
      integrable := CosineMixtureApproximation.rho_integrable w N' hw hSup'
      mass := CosineMixtureApproximation.rho_mass w N' hw hm }
  have hg : Continuous ρ'.value := CosineMixtureApproximation.rho_continuous w N' hw hSup'
  have hmp := measurePreserving_restrict_pi (X := UnitAddCircle) AddCircle.haarAddCircle
    (coordinateEmbedding I) (coordinateEmbedding I).injective
  have hmarg := marginal_ae_eq_restrict ρ I w N hw hm he
  have hfe : ρ'.FiniteEntropy :=
    (Real.continuous_mul_log.comp hg).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  refine ⟨ρ', hfe, ?_, ?_⟩
  · -- energy
    have h1 : coordinateEnergy I (I.card : ℝ) (CosineMixtureApproximation.rho w N) =
        inversePowerEnergy I.card (coordinateMarginal ρ I) :=
      coordinateEnergy_eq_inversePower_marginal hr ρ I w N hw hm he
    rw [← h1, coordinateEnergy_embedding I _ w N hw hm.summable,
      weightedEnergyENN_eq_inversePowerEnergy hr]
    rfl
  · -- entropy
    have hφ : Continuous fun y : ℝ => y * Real.log y := Real.continuous_mul_log
    have himg : entropy ρ' =
        ∫ x : Torus d, (ρ'.value (fun j => x (coordinateEmbedding I j))) *
          Real.log (ρ'.value (fun j => x (coordinateEmbedding I j))) ∂torusMeasure d := by
      have hf : Continuous fun y : Torus I.card => ρ'.value y * Real.log (ρ'.value y) :=
        hφ.comp hg
      have key := integral_map (μ := Measure.pi fun _ : Fin d => (AddCircle.haarAddCircle : Measure UnitAddCircle))
        (φ := fun (x : Fin d → UnitAddCircle) (j : Fin I.card) => x (coordinateEmbedding I j))
        hmp.measurable.aemeasurable hf.aestronglyMeasurable
      rw [hmp.map_eq] at key
      exact key
    rw [himg]
    unfold coordinateMarginalEntropy
    apply integral_congr_ae
    filter_upwards [hmarg] with x hx
    rw [hx]

end transport

end BecknerOnofri.V2.Transfer
