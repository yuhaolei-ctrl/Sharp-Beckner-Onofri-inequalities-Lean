module

public import BecknerOnofri.V2.Onset.Compactness
public import BecknerOnofri.LocalElevenCore.ContinuousEnergyAlongLine
public import BecknerOnofri.ContinuousVariations

@[expose] public section

/-! # Upper semicontinuity of the dual functional along Sobolev convergence

If `u_n → v` in `H^d` (hence uniformly) and `Φ_{μ_n}(u_n) ≥ 0` with `μ_n → 1`, then `v` is critical
Sobolev and `Φ_1(v) ≥ 0`.  The logarithm of the partition function is continuous for the uniform
norm; the energy is handled by Fatou, coefficient by coefficient. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped Topology

namespace BecknerOnofri.V2.Onset
open BecknerOnofri.HighDim ContinuousGibbs
open BecknerOnofri.HighDim.LocalEleven.ContinuousEnergy

theorem continuous_logPartitionReal {d : ℕ} : Continuous (logPartitionReal : Space d → ℝ) :=
  continuous_iff_continuousAt.2 fun u => (hasFDerivAt_logPartitionReal u).continuousAt

theorem coeff_norm_le_sobolevNorm {d : ℕ} {r : ℝ} (hr : 0 ≤ r) (f : Torus d → ℝ)
    (hf : InSobolev r f) (k : Frequency d) : ‖fourierCoeff f k‖ ≤ sobolevNorm r f := by
  have h1 : ‖fourierCoeff f k‖ ^ 2 ≤ sobolevTerm r f k := by
    unfold sobolevTerm
    have : (1 : ℝ) ≤ (1 + (2 * Real.pi * frequencyLength k) ^ 2) ^ r :=
      Real.one_le_rpow (by nlinarith [sq_nonneg (2 * Real.pi * frequencyLength k)]) hr
    nlinarith [sq_nonneg ‖fourierCoeff f k‖]
  have h2 : sobolevTerm r f k ≤ ∑' k, sobolevTerm r f k :=
    hf.2.le_tsum k (fun j _ => by rw [sobolevTerm_eq]; positivity)
  unfold sobolevNorm
  exact Real.le_sqrt_of_sq_le (h1.trans h2)

theorem coeff_tendsto_of_sobolev {d : ℕ} (u : ℕ → ContinuousGibbs.Space d) (v : ContinuousGibbs.Space d)
    {r : ℝ} (hr : 0 ≤ r) (hmem : ∀ n, InSobolev r (⇑(u n) - ⇑v))
    (hconv : Tendsto (fun n => sobolevNorm r (⇑(u n) - ⇑v)) atTop (𝓝 0)) (k : Frequency d) :
    Tendsto (fun n => fourierCoeff ⇑(u n) k) atTop (𝓝 (fourierCoeff ⇑v k)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hconv
  have := coeff_norm_le_sobolevNorm hr _ (hmem n) k
  rwa [FullHessianDecomposition.fourierCoeff_sub _ _
    (ContinuousMap.memLp (p := 2) (torusMeasure d) ℝ (u n))
    (ContinuousMap.memLp (p := 2) (torusMeasure d) ℝ v)] at this

/-- **Upper semicontinuity of the dual functional.**  If `u_n → v` in `H^d`, `μ_n → 1` and
`Φ_{μ_n}(u_n) ≥ 0`, then `v` is critical Sobolev and `Φ_1(v) ≥ 0`. -/
theorem limit_value_nonneg {d : ℕ} (hd : 0 < d) (μ : ℕ → ℝ) (u : ℕ → ContinuousGibbs.Space d)
    (v : ContinuousGibbs.Space d) (hμ : Tendsto μ atTop (𝓝 1))
    (hcrit : ∀ n, InCriticalSobolev ⇑(u n))
    (hmem : ∀ n, InSobolev (d : ℝ) (⇑(u n) - ⇑v))
    (hconv : Tendsto (fun n => sobolevNorm (d : ℝ) (⇑(u n) - ⇑v)) atTop (𝓝 0))
    (hnonneg : ∀ n, 0 ≤ value (μ n) (u n)) :
    InCriticalSobolev ⇑v ∧ 0 ≤ value 1 v := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  -- uniform convergence
  have hsup : Tendsto u atTop (𝓝 v) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hs : (d : ℝ) / 2 < d := by linarith
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
      (by simpa using hconv.const_mul ‖SobolevEmbedding.inverseScaleLp hd hs‖)
    have := SobolevEmbedding.continuous_norm_bound hd hs (u n - v) (hmem n)
    simpa using this
  have hlog : Tendsto (fun n => logPartitionReal (u n)) atTop (𝓝 (logPartitionReal v)) :=
    (continuous_logPartitionReal.tendsto v).comp hsup
  have hcoef := coeff_tendsto_of_sobolev u v hdpos.le hmem hconv
  have hμpos : ∀ᶠ n in atTop, 0 < μ n := hμ.eventually (lt_mem_nhds one_pos)
  have hc : 0 < (2 * Real.pi) ^ d := by positivity
  set Bd : ℝ := (2 * Real.pi) ^ d * (2 * logPartitionReal v) with hBd
  have hfin : ∀ F : Finset (NonzeroFrequency d), ∑ k ∈ F, potentialTerm ⇑v k ≤ Bd := by
    intro F
    have hlim : Tendsto (fun n => ∑ k ∈ F, potentialTerm ⇑(u n) k) atTop
        (𝓝 (∑ k ∈ F, potentialTerm ⇑v k)) := by
      refine tendsto_finsetSum _ fun k _ => ?_
      unfold potentialTerm
      exact (((hcoef k.val).norm).pow 2).const_mul _
    have hlim2 : Tendsto (fun n => (2 * Real.pi) ^ d * (2 * μ n * logPartitionReal (u n))) atTop
        (𝓝 Bd) := by
      have := ((hμ.const_mul 2).mul hlog).const_mul ((2 * Real.pi) ^ d)
      simpa [hBd] using this
    refine le_of_tendsto_of_tendsto hlim hlim2 ?_
    filter_upwards [hμpos] with n hn
    have h1 : ∑ k ∈ F, potentialTerm ⇑(u n) k ≤ potentialEnergy ⇑(u n) :=
      (hcrit n).2.sum_le_tsum F (fun k _ => by unfold potentialTerm frequencyLength; positivity)
    have h2 : 0 ≤ logPartitionReal (u n) - (1 / (2 * μ n)) * normalizedPotentialEnergy ⇑(u n) :=
      hnonneg n
    have h3 : normalizedPotentialEnergy ⇑(u n) ≤ 2 * μ n * logPartitionReal (u n) := by
      have : (1 / (2 * μ n)) * normalizedPotentialEnergy ⇑(u n) ≤ logPartitionReal (u n) := by linarith
      rw [one_div, inv_mul_le_iff₀ (by positivity)] at this
      exact this
    have h4 : potentialEnergy ⇑(u n) = (2 * Real.pi) ^ d * normalizedPotentialEnergy ⇑(u n) := by
      unfold normalizedPotentialEnergy; field_simp
    rw [h4] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left h3 hc.le)
  have hnn : 0 ≤ potentialTerm ⇑v := fun k => by unfold potentialTerm frequencyLength; positivity
  have hsum := summable_of_sum_le hnn hfin
  have hen : potentialEnergy ⇑v ≤ Bd := Real.tsum_le_of_sum_le hnn hfin
  refine ⟨⟨ContinuousMap.memLp (p := 2) (torusMeasure d) ℝ v, hsum⟩, ?_⟩
  unfold value
  have h5 : normalizedPotentialEnergy ⇑v ≤ 2 * logPartitionReal v := by
    unfold normalizedPotentialEnergy
    rw [div_le_iff₀ hc]
    calc potentialEnergy ⇑v ≤ Bd := hen
      _ = 2 * logPartitionReal v * (2 * Real.pi) ^ d := by rw [hBd]; ring
  linarith

end BecknerOnofri.V2.Onset
