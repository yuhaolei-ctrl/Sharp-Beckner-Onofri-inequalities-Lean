module

public import BecknerOnofri.OnsetContinuous
public import BecknerOnofri.OnsetCompactness
public import BecknerOnofri.V2.Onset.Bootstrap
public import BecknerOnofri.V2.Onset.FirstStep
public import BecknerOnofri.OptimizerEulerPaper
public import BecknerOnofri.V2.Reaudit.ExternalInputs.RoughFromAdams

@[expose] public section

/-! # Uniform bounds for near-threshold optimizers (Proposition 5.24, `eq:section5-onset-uniform-bounds`)

For `μ` near `1` (i.e. `β = μ β_s` near `β_s`) every continuous global maximizer `u` of the dual
functional satisfies uniform bounds on the critical energy and on `∫ ρ_u²`, `ρ_u = e^u/Z(u)`.
The proof uses the rough exponential estimate with a coefficient strictly below `1/2`, obtained from
the printed sharp critical Adams inequality (`Reaudit.ExternalInputs.exists_rough_gap_of_adams`, i.e.
`ExternalInputs.criticalAdams` with `b = endpointConstant d`), and `Z ≥ 1`. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped Topology

namespace BecknerOnofri.V2.Onset
open BecknerOnofri.HighDim ContinuousGibbs ContinuousFirstShell
open Legacy.BecknerOnofri.TorusSobolev Legacy.BecknerOnofri.SubcriticalAttainment

/-- A `HighDim` dual maximizer in `C(𝕋ᵈ)` is a legacy maximizer of `functional (β_s/(2β))`. -/
theorem legacy_maximizer {d : ℕ} (hd : 0 < d) {β : ℝ} (u : Space d)
    (hu : InCriticalSobolev ⇑u) (hm : MeanZero ⇑u)
    (hmax : ∀ v : Torus d → ℝ, InCriticalSobolev v → dualFunctional β v ≤ dualFunctional β ⇑u) :
    Admissible (toL2 d u) ∧ ∀ v : TorusL2 d, Admissible v →
      functional (spectralThreshold d / (2 * β)) v ≤
        functional (spectralThreshold d / (2 * β)) (toL2 d u) := by
  refine ⟨OnsetContinuous.toL2_admissible hd u hu hm, ?_⟩
  intro v hv
  have hh := hmax (RawAttainment.realValue v) (RawAttainment.realValue_sobolev v hv)
  rw [OnsetRaw.dualFunctional_eq_normalized hd _ _ (RawAttainment.realValue_sobolev v hv),
    OnsetRaw.dualFunctional_eq_normalized hd _ _ hu,
    RawAttainment.center_potentialLp_realValue v hv,
    ← OnsetContinuous.toL2_eq_potentialLp u hu, OnsetContinuous.center_toL2 u hm] at hh
  exact_mod_cast hh

theorem gibbs_sq_integral_le {d : ℕ} (u : Space d) (hm : mean d u = 0) :
    ∫ x, (normalizedGibbs (fun y => u y) x) ^ 2 ∂torusMeasure d ≤
      ∫ x, Real.exp (2 * u x) ∂torusMeasure d := by
  have hZ : (1 : ℝ) ≤ ∫ y, Real.exp (u y) ∂torusMeasure d := by
    have := LocalEleven.WeightedExponentialRemainder.partition_ge_one u hm
    simpa [ContinuousGibbs.partition] using this
  have hint : ∀ f : Space d, Integrable (fun x => f x) (torusMeasure d) := fun f =>
    ContinuousGibbs.integrable d f
  have hint2 : Integrable (fun x => Real.exp (2 * u x)) (torusMeasure d) := by
    have : Continuous fun x => Real.exp (2 * u x) := by fun_prop
    exact this.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hint1 : Integrable (fun x => (normalizedGibbs (fun y => u y) x) ^ 2) (torusMeasure d) := by
    have : Continuous fun x => (normalizedGibbs (fun y => u y) x) ^ 2 := by
      unfold normalizedGibbs; fun_prop
    exact this.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  refine integral_mono hint1 hint2 fun x => ?_
  simp only [normalizedGibbs]
  set Z := ∫ y, Real.exp (u y) ∂torusMeasure d
  have hZ2 : 1 ≤ Z ^ 2 := by nlinarith
  have h0 : 0 < Real.exp (2 * u x) := Real.exp_pos _
  have : Real.exp (u x) ^ 2 = Real.exp (2 * u x) := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [div_pow, this]
  exact div_le_self h0.le hZ2

/-- **Uniform `L²` bound for the optimal densities** (`eq:section5-onset-uniform-bounds` and
`Z ≥ 1`): near the threshold, all continuous global maximizers have `∫ ρ_u² ≤ M`. -/
theorem uniform_density_bound {d : ℕ} (hd : 12 ≤ d) :
    ∃ M E : ℝ, ∀ᶠ μ in 𝓝 (1 : ℝ), ∀ u : Space d, InCriticalSobolev ⇑u → MeanZero ⇑u →
      (∀ v : Torus d → ℝ, InCriticalSobolev v →
        dualFunctional (μ * spectralThreshold d) v ≤ dualFunctional (μ * spectralThreshold d) ⇑u) →
      ∫ x, (normalizedGibbs (fun y => u y) x) ^ 2 ∂torusMeasure d ≤ M ∧
        criticalEnergy (toL2 d u) ≤ E := by
  have hd0 : 0 < d := by omega
  -- `eq:section5-onset-uniform-bounds`: the rough exponential estimate with exponent
  -- `b = endpointConstant d`, i.e. the printed sharp critical Adams inequality
  -- `eq:section2-critical-adams` (`ExternalInputs.criticalAdams`).
  obtain ⟨b, Ab, hb, hR, hgap⟩ := Reaudit.ExternalInputs.exists_rough_gap_of_adams hd
  have hσ : 0 < spectralThreshold d := Legacy.TorusEndpoint.endpointSigma_pos hd0
  set a0 : ℝ := (1 / (4 * b) + 1 / 2) / 2 with ha0
  have ha0gt : 1 / (4 * b) < a0 := by rw [ha0]; linarith
  have ha0lt : a0 < 1 / 2 := by rw [ha0]; linarith
  set Eb : ℝ := Real.log Ab / (a0 - 1 / (4 * b)) with hEb
  have hlog : 0 ≤ Real.log Ab := rough_log_nonneg hR
  refine ⟨Real.exp (Eb / b + Real.log Ab), Eb, ?_⟩
  -- μ close to 1 gives A = 1/(2μ) > a0
  have hev : ∀ᶠ μ in 𝓝 (1 : ℝ), 0 < μ ∧ a0 < 1 / (2 * μ) := by
    have h1 : ∀ᶠ μ in 𝓝 (1 : ℝ), 0 < μ := lt_mem_nhds one_pos
    have hc : ContinuousAt (fun μ : ℝ => 1 / (2 * μ)) 1 := by
      apply ContinuousAt.div continuousAt_const (by fun_prop) (by norm_num)
    have h2 : ∀ᶠ μ in 𝓝 (1 : ℝ), a0 < 1 / (2 * μ) :=
      hc.eventually (lt_mem_nhds (by norm_num; linarith))
    exact h1.and h2
  filter_upwards [hev] with μ ⟨hμ, hA⟩ u hu hm hmax
  have hβ : 0 < μ * spectralThreshold d := mul_pos hμ hσ
  obtain ⟨hU, hUmax⟩ := legacy_maximizer hd0 u hu hm hmax
  have hAeq : spectralThreshold d / (2 * (μ * spectralThreshold d)) = 1 / (2 * μ) := by
    field_simp
  rw [hAeq] at hUmax
  set A : ℝ := 1 / (2 * μ) with hAdef
  have hz : 0 ≤ functional A (toL2 d u) := by simpa using hUmax 0 (admissible_zero d)
  have hc := coercivity hR A hU
  have hE0 : 0 ≤ criticalEnergy (toL2 d u) := energy_nonneg _
  have hpos : 0 < a0 - 1 / (4 * b) := by linarith
  have hE : criticalEnergy (toL2 d u) ≤ Eb := by
    rw [hEb, le_div_iff₀ hpos]
    nlinarith [mul_le_mul_of_nonneg_right hA.le hE0]
  have hrough := (hR (toL2 d u) hU 2 two_pos).2
  have hmean : mean d u = 0 := by simpa [MeanZero, mean_apply] using hm
  have hsq := gibbs_sq_integral_le u hmean
  have hae : ∀ᵐ x ∂torusMeasure d, Real.exp (2 * (toL2 d u x).re) = Real.exp (2 * u x) := by
    filter_upwards [toL2_ae u] with x hx
    rw [hx]; simp
  have hint : ∫ x, Real.exp (2 * (toL2 d u x).re) ∂torusMeasure d =
      ∫ x, Real.exp (2 * u x) ∂torusMeasure d := integral_congr_ae hae
  have hI : Integrable (fun x => Real.exp (2 * (toL2 d u x).re)) (torusMeasure d) :=
    (hR (toL2 d u) hU 2 two_pos).1
  have hIpos : 0 < ∫ x, Real.exp (2 * (toL2 d u x).re) ∂torusMeasure d := by
    have : NeZero (torusMeasure d) := ⟨by
      intro h
      have := (inferInstance : IsProbabilityMeasure (torusMeasure d)).measure_univ
      simp [h] at this⟩
    exact integral_exp_pos hI
  have hle : ∫ x, Real.exp (2 * (toL2 d u x).re) ∂torusMeasure d ≤
      Real.exp (Eb / b + Real.log Ab) := by
    rw [← Real.log_le_iff_le_exp hIpos]
    refine hrough.trans ?_
    have : (2 : ℝ) ^ 2 * criticalEnergy (toL2 d u) / (4 * b) ≤ Eb / b := by
      rw [show (2 : ℝ) ^ 2 * criticalEnergy (toL2 d u) / (4 * b) = criticalEnergy (toL2 d u) / b by
        field_simp; ring]
      exact div_le_div_of_nonneg_right hE hb.le
    linarith
  exact ⟨hsq.trans (hint.symm.le.trans hle), hE⟩

/-- The Euler equation of a continuous maximizer in the form used by the bootstrap. -/
theorem optimizer_euler_frequency {d : ℕ} (hd : 0 < d) {μ : ℝ} (hμ : 0 < μ) (u : Space d)
    (hu : InCriticalSobolev ⇑u) (hm : MeanZero ⇑u)
    (hmax : ∀ v : Torus d → ℝ, InCriticalSobolev v →
      dualFunctional (μ * spectralThreshold d) v ≤ dualFunctional (μ * spectralThreshold d) ⇑u) :
    ∀ k : Frequency d, k ≠ 0 →
      ((frequencyLength k : ℂ) ^ d) * fourierCoeff (⇑u) k =
        (μ : ℂ) * fourierCoeff (normalizedGibbs (⇑u)) k := by
  have hσ : 0 < spectralThreshold d := Legacy.TorusEndpoint.endpointSigma_pos hd
  intro k hk
  have h := OptimizerDuality.raw_optimizer_euler hd (mul_pos hμ hσ) ⇑u hu hm hmax ⟨k, hk⟩
  rw [mul_div_cancel_right₀ _ hσ.ne'] at h
  simpa using h

/-- **Uniform Sobolev bounds** (`eq:section5-onset-uniform-smoothness`): all continuous maximizers
at couplings near the threshold lie in every `H^{(m+1)d}` with bounds independent of the
maximizer and of the coupling. -/
theorem uniform_sobolev_bound {d : ℕ} (hd : 12 ≤ d) :
    ∃ B : ℕ → ℝ, ∀ᶠ μ in 𝓝 (1 : ℝ), ∀ u : Space d, InCriticalSobolev ⇑u → MeanZero ⇑u →
      (∀ v : Torus d → ℝ, InCriticalSobolev v →
        dualFunctional (μ * spectralThreshold d) v ≤ dualFunctional (μ * spectralThreshold d) ⇑u) →
      ∀ m : ℕ, InSobolev (((m : ℝ) + 1) * d) ⇑u ∧ sobolevNorm (((m : ℝ) + 1) * d) ⇑u ≤ B m := by
  have hd0 : 0 < d := by omega
  obtain ⟨M, E, hM⟩ := uniform_density_bound hd
  refine ⟨bootBound d 2 (eulerConst d * 2 * Real.sqrt M), ?_⟩
  have hint : ∀ᶠ μ in 𝓝 (1 : ℝ), 0 < μ ∧ μ < 2 :=
    (lt_mem_nhds one_pos).and (gt_mem_nhds (by norm_num))
  filter_upwards [hM, hint] with μ hMμ ⟨hμ0, hμ2⟩ u hu hm hmax
  have hmean : mean d u = 0 := by simpa [MeanZero, mean_apply] using hm
  have heuler := optimizer_euler_frequency hd0 hμ0 u hu hm hmax
  have hρ : MemLp (normalizedGibbs (fun y => u y)) 2 (torusMeasure d) := by
    have hfun : (⇑(normalized u) : Torus d → ℝ) = normalizedGibbs (fun y => u y) :=
      funext (normalized_apply u)
    rw [← hfun]
    exact (normalized u).continuous.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hfirst := sobolev_first_step μ M ⇑u (normalizedGibbs (fun y => u y))
    (ContinuousMap.memLp (p := 2) (torusMeasure d) ℝ u) hm hρ (hMμ u hu hm hmax).1 heuler
  have hB : sobolevNorm (d : ℝ) ⇑u ≤ eulerConst d * 2 * Real.sqrt M := by
    refine hfirst.2.trans ?_
    have : |μ| ≤ 2 := by rw [abs_of_pos hμ0]; exact hμ2.le
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this (eulerConst_nonneg d))
      (Real.sqrt_nonneg _)
  exact sobolev_bootstrap hd0 2 _ μ (by rw [abs_of_pos hμ0]; exact hμ2.le) u hmean heuler hfirst.1 hB

end BecknerOnofri.V2.Onset
