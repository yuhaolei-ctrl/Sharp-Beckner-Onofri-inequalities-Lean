module

public import BecknerOnofri.HeatL1Convergence
public import BecknerOnofri.HeatRegularization

@[expose] public section

/-! Entropy convergence of actual heat smoothing on the full finite-entropy
domain. Fatou gives lower semicontinuity along a.e. convergent subsequences;
L1 convergence and entropy contraction close the argument. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped Topology
namespace BecknerOnofri.HighDim.HeatApproximation

lemma shifted_entropy_nonneg {d : ℕ} (ρ : ProbabilityDensity d) :
    0 ≤ᵐ[torusMeasure d] (fun x => ρ.value x*Real.log (ρ.value x)+1) := by
  filter_upwards [ρ.nonneg] with x hx
  have h := Legacy.TorusEndpoint.entropy_young (ρ.value x) 0 hx
  simp only [mul_zero,Real.exp_zero] at h
  change 0 ≤ ρ.value x*Real.log (ρ.value x)+1
  linarith

lemma shifted_entropy_integral {d : ℕ} (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy) :
    (∫⁻ x, ENNReal.ofReal (ρ.value x*Real.log (ρ.value x)+1) ∂torusMeasure d) =
      ENNReal.ofReal (entropy ρ+1) := by
  have hi : Integrable (fun x => ρ.value x*Real.log (ρ.value x)+1) (torusMeasure d) :=
    hρ.add (integrable_const 1)
  rw [← ofReal_integral_eq_lintegral_ofReal hi (shifted_entropy_nonneg ρ)]
  have he := integral_add hρ (integrable_const (1:ℝ))
  rw [he]
  simp [entropy]

theorem entropy_le_of_ae_limit {d : ℕ} (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy)
    (r : ℕ → ProbabilityDensity d) (hr : ∀ n, (r n).FiniteEntropy) (C : ℝ)
    (hC : ∀ n, entropy (r n) ≤ C)
    (hlim : ∀ᵐ x ∂torusMeasure d, Tendsto (fun n => (r n).value x) atTop (𝓝 (ρ.value x))) :
    entropy ρ ≤ C := by
  let F := fun n x => ENNReal.ofReal ((r n).value x*Real.log ((r n).value x)+1)
  let f := fun x => ENNReal.ofReal (ρ.value x*Real.log (ρ.value x)+1)
  have hF (n : ℕ) : AEMeasurable (F n) (torusMeasure d) :=
    ENNReal.measurable_ofReal.comp_aemeasurable ((hr n).aestronglyMeasurable.aemeasurable.add_const 1)
  have hflim : ∀ᵐ x ∂torusMeasure d, Tendsto (fun n => F n x) atTop (𝓝 (f x)) := by
    filter_upwards [hlim] with x hx
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (((Real.continuous_mul_log.tendsto (ρ.value x)).comp hx).add_const 1)
  have hfatou : (∫⁻ x, f x ∂torusMeasure d) ≤
      liminf (fun n => ∫⁻ x, F n x ∂torusMeasure d) atTop := by
    calc
      _ = ∫⁻ x, liminf (fun n => F n x) atTop ∂torusMeasure d :=
        lintegral_congr_ae (hflim.mono (fun x hx => hx.liminf_eq.symm))
      _ ≤ _ := lintegral_liminf_le' hF
  have hb : liminf (fun n => ∫⁻ x, F n x ∂torusMeasure d) atTop ≤ ENNReal.ofReal (C+1) := by
    apply liminf_le_of_frequently_le'
    apply Eventually.frequently
    exact Eventually.of_forall (fun n => by
      dsimp only [F]
      rw [shifted_entropy_integral (r n) (hr n)]
      exact ENNReal.ofReal_le_ofReal (by linarith [hC n]))
  have hC0 : 0 ≤ C :=
    (Legacy.TorusEndpoint.densityEntropy_nonneg_of_finite (Bridge.density (r 0)) (hr 0)).trans (hC 0)
  have h := hfatou.trans hb
  dsimp only [f] at h
  rw [shifted_entropy_integral ρ hρ,ENNReal.ofReal_le_ofReal_iff (by linarith : 0 ≤ C+1)] at h
  linarith

theorem entropy_tendsto_of_inMeasure_of_upper {d : ℕ} (ρ : ProbabilityDensity d)
    (hρ : ρ.FiniteEntropy) (r : ℕ → ProbabilityDensity d) (hr : ∀ n, (r n).FiniteEntropy)
    (hm : TendstoInMeasure (torusMeasure d) (fun n => (r n).value) atTop ρ.value)
    (hupper : ∀ n, entropy (r n) ≤ entropy ρ) :
    Tendsto (fun n => entropy (r n)) atTop (𝓝 (entropy ρ)) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    by_contra hn
    have hf : ∃ᶠ n in atTop, entropy (r n) ≤ a := by
      simpa only [not_eventually,not_lt] using hn
    obtain ⟨ns,hns,hbad⟩ := extraction_of_frequently_atTop hf
    obtain ⟨ms,hms,hae⟩ := (hm.comp hns.tendsto_atTop).exists_seq_tendsto_ae
    have h := entropy_le_of_ae_limit ρ hρ (fun n => r (ns (ms n)))
      (fun n => hr _) a (fun n => hbad _) hae
    exact (not_le.mpr ha) h
  · intro b hb
    exact Eventually.of_forall (fun n => (hupper n).trans_lt hb)

theorem heat_entropy_tendsto {d : ℕ} (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy)
    (t : ℕ → ℝ) (ht : ∀ n, 0 < t n) (ht0 : Tendsto t atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, heatRegularization ρ (t n) x *
      Real.log (heatRegularization ρ (t n) x) ∂torusMeasure d) atTop (𝓝 (entropy ρ)) := by
  let τ := fun n => 4*Real.pi*t n
  have hτ (n : ℕ) : 0 < τ n := mul_pos (by positivity) (ht n)
  have hτ0 : Tendsto τ atTop (𝓝 0) := by simpa [τ] using ht0.const_mul (4*Real.pi)
  let r := fun n => Bridge.rawDensity
    (Legacy.BecknerOnofri.HeatDensityApproximation.heatDensity (Bridge.density ρ) (hτ n))
  have hr (n : ℕ) : (r n).FiniteEntropy :=
    Legacy.BecknerOnofri.HeatDensityApproximation.heatDensity_finiteEntropy _ (hτ n)
  have hm : TendstoInMeasure (torusMeasure d) (fun n => (r n).value) atTop ρ.value :=
    heat_tendstoInMeasure (Bridge.density ρ) τ hτ hτ0
  have hu (n : ℕ) : entropy (r n) ≤ entropy ρ :=
    Legacy.BecknerOnofri.HeatDensityApproximation.heatDensity_entropy_le (Bridge.density ρ) hρ (hτ n)
  have h := entropy_tendsto_of_inMeasure_of_upper ρ hρ r hr hm hu
  simp only [heatRegularization_eq]
  exact h

#print axioms entropy_le_of_ae_limit
#print axioms heat_entropy_tendsto
end BecknerOnofri.HighDim.HeatApproximation
