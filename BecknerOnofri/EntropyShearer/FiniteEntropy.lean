module

public import BecknerOnofri.EntropyShearer.AllSubsets
public import BecknerOnofri.EntropyShearer.L1Contraction
public import BecknerOnofri.EntropyShearer.EntropyFatou

@[expose] public section

/-! Shearer's inequality on the full finite-entropy probability-density domain.
Heat regularization, actual Haar marginalization, and Fatou's lemma remove
all boundedness and strict-positivity assumptions from the final theorem. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped Topology BigOperators
namespace BecknerOnofri.HighDim.EntropyShearer

lemma finiteEntropy_of_positiveBounded {d : ℕ} (ρ : ProbabilityDensity d)
    (hρ : PositiveBounded ρ.value) : ρ.FiniteEntropy :=
  (hρ.bounded.mul hρ.logBounded).integrable

lemma fullMarginalDensity_positiveBounded {d : ℕ} (s : Finset (Fin d))
    (ρ : ProbabilityDensity d) (hρ : PositiveBounded ρ.value) :
    PositiveBounded (fullMarginalDensity s ρ).value := by
  change PositiveBounded (fullAvg s ρ.value)
  rw [fullAvg_eq_avg s hρ.bounded]
  exact hρ.avg s

lemma entropy_marginal_le_of_bounds {d : ℕ} (s : Finset (Fin d))
    (ρ : ProbabilityDensity d) (hρ : PositiveBounded ρ.value) :
    entropy (fullMarginalDensity s ρ) ≤ entropy ρ := by
  have hone : PositiveBounded (fun _ : Torus d => (1:ℝ)) :=
    ⟨measurable_const,1,1,zero_lt_one,fun _ => ⟨le_rfl,le_rfl⟩⟩
  have h := relativeEntropy_avg_le hρ hone s
  rw [avg_const] at h
  change entropyIntegral (fullAvg s ρ.value) ≤ entropyIntegral ρ.value
  rw [fullAvg_eq_avg s hρ.bounded]
  simpa only [relativeEntropy, entropyIntegral, Real.log_one, sub_zero] using h

private def approximation {d : ℕ} (ρ : ProbabilityDensity d) (n : ℕ) : ProbabilityDensity d :=
  Bridge.rawDensity (Legacy.BecknerOnofri.HeatDensityApproximation.heatDensity (Bridge.density ρ)
    (show (0:ℝ)<1/((n:ℝ)+1) by positivity))

private lemma approximation_bounded {d : ℕ} (ρ : ProbabilityDensity d) (n : ℕ) :
    PositiveBounded (approximation ρ n).value :=
  positiveBounded_of_continuous_pos
    (Legacy.BecknerOnofri.HeatDensityApproximation.heatValue_continuous _ (by positivity))
    (Legacy.BecknerOnofri.HeatDensityApproximation.heatValue_pos _ (by positivity))

private lemma approximation_entropy_le {d : ℕ} (ρ : ProbabilityDensity d)
    (hρ : ρ.FiniteEntropy) (n : ℕ) : entropy (approximation ρ n) ≤ entropy ρ :=
  Legacy.BecknerOnofri.HeatDensityApproximation.heatDensity_entropy_le (Bridge.density ρ) hρ (by positivity)

private lemma approximation_l1 {d : ℕ} (ρ : ProbabilityDensity d) :
    Tendsto (fun n => ∫ x, ‖(approximation ρ n).value x-ρ.value x‖ ∂torusMeasure d) atTop (𝓝 0) :=
  HeatApproximation.heat_l1_tendsto (Bridge.density ρ) (fun n => 1/((n:ℝ)+1))
    (fun _ => by positivity) tendsto_one_div_add_atTop_nhds_zero_nat

/-- Each actual Haar marginal of a finite-entropy density has finite entropy. -/
theorem marginal_finiteEntropy {d : ℕ} (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy)
    (s : Finset (Fin d)) : (fullMarginalDensity s ρ).FiniteEntropy ∧
      entropy (fullMarginalDensity s ρ) ≤ entropy ρ := by
  let r := fun n => fullMarginalDensity s (approximation ρ n)
  have hr (n : ℕ) : (r n).FiniteEntropy :=
    finiteEntropy_of_positiveBounded _ (fullMarginalDensity_positiveBounded s _ (approximation_bounded ρ n))
  have hbound (n : ℕ) : entropy (r n) ≤ entropy ρ :=
    (entropy_marginal_le_of_bounds s _ (approximation_bounded ρ n)).trans
      (approximation_entropy_le ρ hρ n)
  have hm := fullAvg_tendstoInMeasure s ρ (approximation ρ) (approximation_l1 ρ)
  obtain ⟨ns,hns,hae⟩ := hm.exists_seq_tendsto_ae
  exact finiteEntropy_of_ae_limit d (fullMarginalDensity s ρ) (fun n => r (ns n))
    (fun n => hr _) (entropy ρ) (fun n => hbound _) hae

/-- No continuity, boundedness, strict positivity, or L2 premise is required. -/
theorem all_subsets_finiteEntropy {d r : ℕ} (hr : 0 < r)
    (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy) :
    (∑ s ∈ (Finset.univ : Finset (Fin d)).powersetCard r,
      entropy (fullMarginalDensity sᶜ ρ)) ≤ ((d-1).choose (r-1):ℝ) * entropy ρ := by
  let S := (Finset.univ : Finset (Fin d)).powersetCard r
  let a := fun s => entropy (fullMarginalDensity sᶜ ρ)
  let b := fun n s => entropy (fullMarginalDensity sᶜ (approximation ρ n))
  apply sum_le_of_eventually_lower S a b
  · intro s hs ε hε
    have hm := fullAvg_tendstoInMeasure sᶜ ρ (approximation ρ) (approximation_l1 ρ)
    have hl := entropy_eventually_lower (fullMarginalDensity sᶜ ρ) (marginal_finiteEntropy ρ hρ sᶜ).1
      (fun n => fullMarginalDensity sᶜ (approximation ρ n))
      (fun n => finiteEntropy_of_positiveBounded _
        (fullMarginalDensity_positiveBounded sᶜ _ (approximation_bounded ρ n)))
      hm (a s-ε) (by dsimp [a]; linarith)
    exact hl.mono (fun n hn => hn.le)
  · intro n
    have h := all_subsets_of_bounds hr (approximation_bounded ρ n) (approximation ρ n).mass
    have he (s : Finset (Fin d)) : b n s = entropyIntegral (avg sᶜ (approximation ρ n).value) := by
      change entropyIntegral (fullAvg sᶜ (approximation ρ n).value) = _
      rw [fullAvg_eq_avg sᶜ (approximation_bounded ρ n).bounded]
    simp_rw [he]
    exact h.trans (mul_le_mul_of_nonneg_left (approximation_entropy_le ρ hρ n) (by positivity))

#print axioms marginal_finiteEntropy
#print axioms all_subsets_finiteEntropy
end BecknerOnofri.HighDim.EntropyShearer
