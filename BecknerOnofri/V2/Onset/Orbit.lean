module

public import BecknerOnofri.V2.Onset.Smallness
public import BecknerOnofri.V2.Onset.Exclusion
public import BecknerOnofri.PressureDuality
public import BecknerOnofri.GlobalPressureOnset
public import BecknerOnofri.LocalElevenCore.SupportedFullIdentification
public import BecknerOnofri.LocalElevenCore.StableSupportedClassification
public import BecknerOnofri.GeneralSobolevEmbedding
public import BecknerOnofri.Translation

@[expose] public section

/-! # Classification of near-threshold optimizers (manuscript route)

Sobolev smallness (`Smallness`) places every near-threshold optimizer in the neighbourhood in which
the `H^s` classification (`SupportedFamily.raw_sobolev_classification`) applies; the optimizer is
nonzero because the pressure is positive above the spectral threshold; it is a translate of a
supported branch `branch I`; by `optimizer_full_support` (Proposition 5.24) every axis mode is
nonzero, so `I` is the full index set, and the full-support branch is the explicit branch
(`SupportedFamily.full_branch_identification`). -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped Topology

namespace BecknerOnofri.V2.Onset
open BecknerOnofri.HighDim ContinuousGibbs ContinuousFirstShell

theorem dual_zero {d : ℕ} (β : ℝ) : dualFunctional β (0 : Torus d → ℝ) = 0 := by
  have h0 : normalizedPotentialEnergy (0 : Torus d → ℝ) = 0 := by
    unfold normalizedPotentialEnergy potentialEnergy potentialTerm
    simp [BecknerOnofri.HighDim.fourierCoeff]
  unfold dualFunctional logPartition
  simp [centered, h0]

theorem eq_of_ae_eq {d : ℕ} (f g : Space d) (h : ⇑f =ᵐ[torusMeasure d] ⇑g) : f = g := by
  have : (torusMeasure d).IsOpenPosMeasure := by
    change (Legacy.TorusEndpoint.torusMeasure d).IsOpenPosMeasure
    rw [Legacy.TorusEndpoint.torusMeasure_explicit]; infer_instance
  exact ContinuousMap.ext fun x =>
    congrFun ((Continuous.ae_eq_iff_eq (torusMeasure d) f.continuous g.continuous).mp h) x

/-- Above the spectral threshold a global optimizer is nonzero (the pressure is positive). -/
theorem optimizer_ne_zero {d : ℕ} (hd : 0 < d) {μ : ℝ} (hμ : 1 < μ) (u : Space d)
    (hu : InCriticalSobolev ⇑u)
    (hmax : ∀ v : Torus d → ℝ, InCriticalSobolev v →
      dualFunctional (μ * spectralThreshold d) v ≤ dualFunctional (μ * spectralThreshold d) ⇑u) :
    u ≠ 0 := by
  intro h
  subst h
  have hσ : 0 < spectralThreshold d := Legacy.TorusEndpoint.endpointSigma_pos hd
  have hβ : 0 < μ * spectralThreshold d := mul_pos (by linarith) hσ
  have hp := GlobalPressureOnset.optimizer_pressure hd hβ _ hu hmax
  have hpos := pressure_pos_of_spectral_lt hd (β := μ * spectralThreshold d)
    (by nlinarith)
  rw [hp] at hpos
  have h0 : dualFunctional (μ * spectralThreshold d) ⇑(0 : Space d) = 0 := dual_zero _
  rw [h0] at hpos
  exact lt_irrefl _ hpos

open BecknerOnofri.HighDim.LocalEleven in
/-- **Orbit classification of near-threshold optimizers.**  For `μ` slightly above `1`, every
continuous global maximizer of the dual functional at coupling `μ β_s` is a translate of the
explicit full-mode branch.  The only conditional hypothesis is `OnsetEndpointInputs d`. -/
theorem optimizers_eventually_branch_orbit_v2 {d : ℕ} (hd : 12 ≤ d) (E : OnsetEndpointInputs d) :
    ∀ᶠ μ in 𝓝[>] (1 : ℝ), ∀ u : Space d, InCriticalSobolev ⇑u → MeanZero ⇑u →
      (∀ v : Torus d → ℝ, InCriticalSobolev v →
        dualFunctional (μ * spectralThreshold d) v ≤ dualFunctional (μ * spectralThreshold d) ⇑u) →
      ∃ a : Torus d, u = ContinuousSymmetry.translation a
        (DiagonalScalarBranch.branchPotential (by omega : 11 ≤ d)
          (DiagonalScalarBranch.amplitude (by omega : 11 ≤ d) μ)) := by
  have hd0 : 0 < d := by omega
  have hd11 : 11 ≤ d := by omega
  have hs : (d : ℝ) / 2 < d := by
    have : (0 : ℝ) < d := by exact_mod_cast hd0
    linarith
  obtain ⟨ε1, hε1, hcls⟩ := SupportedFamily.raw_sobolev_classification hd11 (d : ℝ) hs
  obtain ⟨ε0, hε0, hfs⟩ := Metric.eventually_nhds_iff.mp (optimizer_full_support hd11)
  set C := ‖SobolevEmbedding.inverseScaleLp hd0 hs‖ with hCdef
  have hC : 0 ≤ C := norm_nonneg _
  have hε' : 0 < min ε1 (ε0 / (C + 1)) := lt_min hε1 (div_pos hε0 (by positivity))
  have hsmall := optimizers_sobolev_small hd E (r := (d : ℝ)) (Nat.cast_nonneg d) hε'
  have hδ : Tendsto (fun μ : ℝ => 1 - 1 / μ) (𝓝[>] 1) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have : ContinuousAt (fun μ : ℝ => 1 - 1 / μ) 1 :=
        continuousAt_const.sub (continuousAt_const.div continuousAt_id one_ne_zero)
      simpa using this.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with μ hμ
      have : 1 < μ := hμ
      simp only [Set.mem_Ioi]
      have : 1 / μ < 1 := by rw [div_lt_one (by linarith)]; exact this
      linarith
  have hprof : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ I : Finset (Fin d), I.Nonempty → ∀ j : Fin d, j ∉ I →
      BecknerOnofri.HighDim.fourierCoeff (SupportedFamily.branch hd11 I δ) (axisFrequency j) = 0 := by
    apply eventually_all.mpr
    intro I
    by_cases hI : I.Nonempty
    · filter_upwards [(SupportedFamily.branch_profile hd11 I hI).1.2] with δ h _ j hj
      by_contra hne
      exact hj ((h.2.2.2.2.2.2.2 j).mp hne)
    · exact Eventually.of_forall (fun δ h => (hI h).elim)
  filter_upwards [hsmall.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin,
    hδ.eventually hprof, SupportedFamily.full_branch_identification hd11,
    (show ∀ᶠ μ in 𝓝 (1 : ℝ), μ ∈ Metric.ball (1 : ℝ) (min ε1 ε0) from
      Metric.ball_mem_nhds (1 : ℝ) (lt_min hε1 hε0)).filter_mono nhdsWithin_le_nhds] with
    μ hsm hp hpr hid hball u hu hm hmax
  have hμ1 : 1 < μ := hp
  obtain ⟨hI, hn⟩ := hsm u hu hm hmax
  have hne := optimizer_ne_zero hd0 hμ1 u hu hmax
  have hdist : dist μ 1 < min ε1 ε0 := hball
  rw [Real.dist_eq] at hdist
  -- sup-norm bound
  obtain ⟨v, hvu, -, hvb⟩ := SobolevEmbedding.exists_continuous_representative hd0 hs ⇑u hI
  have hvuEq : v = u := eq_of_ae_eq v u hvu
  subst hvuEq
  have hn1 : sobolevNorm (d : ℝ) ⇑v < ε1 := hn.trans_le (min_le_left _ _)
  have hn2 : sobolevNorm (d : ℝ) ⇑v < ε0 / (C + 1) := hn.trans_le (min_le_right _ _)
  have hsup : ‖v‖ < ε0 := by
    have hh := (lt_div_iff₀ (by positivity : 0 < C + 1)).mp hn2
    have hN : 0 ≤ sobolevNorm (d : ℝ) ⇑v := Real.sqrt_nonneg _
    nlinarith
  have hnear : dist ((μ, v) : ℝ × Space d) (1, 0) < ε0 := by
    rw [Prod.dist_eq, max_lt_iff]
    exact ⟨by rw [Real.dist_eq]; exact hdist.trans_le (min_le_right _ _),
      by simpa using hsup⟩
  have hfull := hfs hnear hu hm hmax hne
  -- Euler equation
  have hEuler : ∀ k : NonzeroFrequency d,
      ((frequencyLength k.val ^ d : ℝ) : ℂ) * BecknerOnofri.HighDim.fourierCoeff v k.val =
        (μ : ℂ) * BecknerOnofri.HighDim.fourierCoeff (normalizedGibbs v) k.val := by
    intro k
    have := optimizer_euler_frequency hd0 (by linarith) v hu hm hmax k.val k.property
    simpa using this
  have hnz : ¬ ⇑v =ᵐ[torusMeasure d] (fun _ => 0) := by
    intro h
    apply hne
    apply eq_of_ae_eq
    filter_upwards [h] with x hx
    simpa using hx
  obtain ⟨-, I, hIne, a, hae⟩ := hcls μ v hI hm (lt_of_lt_of_le hdist (min_le_left _ _)) hn1 hEuler hnz
  have hveq : v = ContinuousSymmetry.translation a (SupportedFamily.branch hd11 I (1 - 1 / μ)) :=
    eq_of_ae_eq _ _ hae
  have hIuniv : I = Finset.univ := by
    rw [Finset.eq_univ_iff_forall]
    intro j
    by_contra hj
    have h0 := hpr I hIne j hj
    apply hfull j
    rw [hveq, OptimizerTranslation.coe_translation,
      BecknerOnofri.HighDim.fourierCoeff_translate_eq_zero_iff]
    exact h0
  refine ⟨a, ?_⟩
  rw [hveq, hIuniv, hid]

end BecknerOnofri.V2.Onset
