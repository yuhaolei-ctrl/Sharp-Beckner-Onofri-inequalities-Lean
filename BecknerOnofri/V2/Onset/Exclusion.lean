module

public import BecknerOnofri.LocalElevenCore.ContinuousEnergyAlongLine
public import BecknerOnofri.LocalElevenCore.SmallSolutionSaddles
public import BecknerOnofri.OptimizerEulerPaper

@[expose] public section

/-! # Second-order necessary condition and exclusion of proper-support branches

Manuscript (Proof of Proposition 5.24, last paragraph): a nonzero small solution of the Euler
equation whose first-shell coordinates do not all lie in the support is a saddle of the
physical second variation (Proposition 5.23, `small_stationary_saddle`), hence it cannot be a
global maximizer of the dual functional; therefore every nonzero small global optimizer has full
first-shell support.

* `secondVariation_nonpos_of_optimizer` : at a global maximizer `u` of `dualFunctional β` over
  `InCriticalSobolev`, `secondVariation β u q ≤ 0` for every mean-zero critical continuous `q`
  (the second-order necessary condition, derived from the line derivative identities of
  `ContinuousEnergy`);
* `no_proper_support_optimizer` : the exclusion statement, in the neighbourhood of `(1, 0)`.
* `optimizer_full_support` : Euler-free form: small nonzero global optimizers have all
  axis Fourier modes nonzero. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter Set
open scoped Topology

namespace BecknerOnofri.V2.Onset
open BecknerOnofri.HighDim ContinuousGibbs
open BecknerOnofri.HighDim.LocalEleven.ContinuousEnergy

theorem meanZero_line {d : ℕ} (u q : Space d) (hu : MeanZero ⇑u) (hq : MeanZero ⇑q) (t : ℝ) :
    MeanZero ⇑(u + t • q) := by
  have hu' : mean d u = 0 := by simpa [MeanZero, mean_apply] using hu
  have hq' : mean d q = 0 := by simpa [MeanZero, mean_apply] using hq
  have : mean d (u + t • q) = 0 := by rw [map_add, map_smul, hu', hq']; simp
  simpa [MeanZero, mean_apply] using this

/-- **Second-order necessary condition at a global maximizer.** -/
theorem secondVariation_nonpos_of_optimizer {d : ℕ} (hd : 0 < d) (μ : ℝ) (u q : Space d)
    (hu : InCriticalSobolev ⇑u) (hum : MeanZero ⇑u) (hq : InCriticalSobolev ⇑q)
    (hqm : MeanZero ⇑q)
    (hmax : ∀ v : Torus d → ℝ, InCriticalSobolev v →
      dualFunctional (μ * spectralThreshold d) v ≤ dualFunctional (μ * spectralThreshold d) ⇑u) :
    secondVariation (μ * spectralThreshold d) ⇑u ⇑q ≤ 0 := by
  set g : ℝ → ℝ := fun t => value μ (u + t • q) with hg
  have hline : ∀ t, InCriticalSobolev ⇑(u + t • q) := fun t =>
    LocalEleven.FullHessianDecomposition.critical_add _ _ hu
      (LocalEleven.GraphCritical.critical_smul t q hq)
  have hle : ∀ t, g t ≤ g 0 := by
    intro t
    have h := hmax ⇑(u + t • q) (hline t)
    rw [value_eq_dual hd μ _ (meanZero_line u q hum hqm t),
      show ⇑u = ⇑(u + (0:ℝ) • q) by simp,
      value_eq_dual hd μ _ (meanZero_line u q hum hqm 0)] at h
    simpa [hg] using (EReal.coe_le_coe_iff.mp h)
  have hder : ∀ t, HasDerivAt g (lineDerivative μ u q t) t := fun t =>
    value_line_hasDerivAt hd μ u q hu hq t
  have hfirst : lineDerivative μ u q 0 = 0 :=
    (IsLocalMax.hasDerivAt_eq_zero (Filter.Eventually.of_forall hle) (hder 0)).symm ▸ rfl
  by_contra hcon
  have hpos : 0 < secondVariation (μ * spectralThreshold d) ⇑u ⇑q := not_le.mp hcon
  have hL : HasDerivAt (lineDerivative μ u q) (secondVariation (μ * spectralThreshold d) ⇑u ⇑q) 0 := by
    simpa using lineDerivative_hasDerivAt hd μ u q 0
  have hslope := hasDerivAt_iff_tendsto_slope.mp hL
  have hev : ∀ᶠ t in 𝓝[≠] (0:ℝ), 0 < slope (lineDerivative μ u q) 0 t :=
    hslope.eventually (lt_mem_nhds hpos)
  have hev' : ∀ᶠ t in 𝓝[>] (0:ℝ), 0 < slope (lineDerivative μ u q) 0 t :=
    hev.filter_mono (nhdsWithin_mono _ (fun t ht => ne_of_gt ht))
  obtain ⟨δ, hδ, hδ'⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).mp hev'
  have hLpos : ∀ t ∈ Ioo (0:ℝ) δ, 0 < lineDerivative μ u q t := by
    intro t ht
    have h : 0 < slope (lineDerivative μ u q) 0 t := hδ' ht
    rw [slope_def_field, hfirst, sub_zero, sub_zero] at h
    exact (div_pos_iff_of_pos_right ht.1).mp h
  have hδ2 : (0:ℝ) < δ / 2 := by
    have : (0:ℝ) < δ := by simpa using hδ
    linarith
  have hmono : StrictMonoOn g (Icc 0 (δ / 2)) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc 0 (δ / 2))
      (fun t _ => (hder t).continuousAt.continuousWithinAt) ?_
    intro t ht
    rw [interior_Icc] at ht
    rw [(hder t).deriv]
    apply hLpos
    exact ⟨ht.1, lt_of_lt_of_le ht.2 (by
      have : (0:ℝ) < δ := by simpa using hδ
      linarith)⟩
  have := hmono (left_mem_Icc.mpr hδ2.le) (right_mem_Icc.mpr hδ2.le) hδ2
  exact absurd (hle (δ / 2)) (not_le.mpr this)

/-- **Exclusion of proper-support branches (Proposition 5.24).**  In a neighbourhood of
`(1, 0)` no nonzero Euler solution with a vanishing axis mode is a global maximizer of the
dual functional. -/
theorem no_proper_support_optimizer {d : ℕ} (hd : 11 ≤ d) :
    ∀ᶠ x : ℝ × Space d in 𝓝 (1, 0),
      InCriticalSobolev ⇑x.2 → MeanZero ⇑x.2 →
      (∀ k : NonzeroFrequency d,
        ((frequencyLength k.val ^ d : ℝ) : ℂ) * BecknerOnofri.HighDim.fourierCoeff x.2 k.val =
          (x.1 : ℂ) * BecknerOnofri.HighDim.fourierCoeff (normalizedGibbs x.2) k.val) →
      x.2 ≠ 0 →
      (∃ j : Fin d, BecknerOnofri.HighDim.fourierCoeff x.2 (axisFrequency j) = 0) →
      ¬ (∀ v : Torus d → ℝ, InCriticalSobolev v →
          dualFunctional (x.1 * spectralThreshold d) v ≤
            dualFunctional (x.1 * spectralThreshold d) ⇑x.2) := by
  filter_upwards [LocalEleven.small_stationary_saddle hd] with x hx hu hm he hne hj hmax
  obtain ⟨v, q, hv, hvm, hq, hqm, hpos, hneg⟩ := hx hm he hne hj
  exact absurd (secondVariation_nonpos_of_optimizer (by omega) x.1 x.2 v hu hm hv hvm hmax)
    (not_le.mpr hpos)

/-- **Full support of small nonzero global optimizers.**  Euler-free form of
`no_proper_support_optimizer`: the Euler equation is supplied by
`OptimizerDuality.raw_optimizer_euler`. -/
theorem optimizer_full_support {d : ℕ} (hd : 11 ≤ d) :
    ∀ᶠ x : ℝ × Space d in 𝓝 (1, 0),
      InCriticalSobolev ⇑x.2 → MeanZero ⇑x.2 →
      (∀ v : Torus d → ℝ, InCriticalSobolev v →
          dualFunctional (x.1 * spectralThreshold d) v ≤
            dualFunctional (x.1 * spectralThreshold d) ⇑x.2) →
      x.2 ≠ 0 → ∀ j : Fin d, BecknerOnofri.HighDim.fourierCoeff x.2 (axisFrequency j) ≠ 0 := by
  have hpos : ∀ᶠ x : ℝ × Space d in 𝓝 (1, 0), 0 < x.1 :=
    (isOpen_lt continuous_const continuous_fst).mem_nhds (by simp)
  filter_upwards [no_proper_support_optimizer hd, hpos] with x hx hx1 hu hm hmax hne j hj
  have hσ : 0 < spectralThreshold d := Legacy.TorusEndpoint.endpointSigma_pos (by omega)
  have hβ : 0 < x.1 * spectralThreshold d := mul_pos hx1 hσ
  refine hx hu hm ?_ hne ⟨j, hj⟩ hmax
  intro k
  have he := OptimizerDuality.raw_optimizer_euler (by omega) hβ ⇑x.2 hu hm hmax k
  have hdiv : x.1 * spectralThreshold d / spectralThreshold d = x.1 := by field_simp
  rw [hdiv] at he
  simpa using he

end BecknerOnofri.V2.Onset
