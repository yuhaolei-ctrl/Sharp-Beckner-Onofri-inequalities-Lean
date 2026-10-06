module

public import BecknerOnofri.HeatEntropyConvergence

@[expose] public section

/-! Finite entropy of an L1 limit follows from a uniform entropy bound;
finiteness is a conclusion, not an additional assumption on the limiting density. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace BecknerOnofri.HighDim.EntropyShearer

lemma finiteEntropy_of_ae_limit (d : ℕ) (ρ : ProbabilityDensity d)
    (r : ℕ → ProbabilityDensity d) (hr : ∀ n, (r n).FiniteEntropy) (C : ℝ)
    (hC : ∀ n, entropy (r n) ≤ C)
    (hlim : ∀ᵐ x ∂torusMeasure d, Tendsto (fun n => (r n).value x) atTop (𝓝 (ρ.value x))) :
    ρ.FiniteEntropy ∧ entropy ρ ≤ C := by
  let F := fun n x => ENNReal.ofReal ((r n).value x * Real.log ((r n).value x)+1)
  let g := fun x => ρ.value x * Real.log (ρ.value x)+1
  have hF (n : ℕ) : AEMeasurable (F n) (torusMeasure d) :=
    ENNReal.measurable_ofReal.comp_aemeasurable ((hr n).aestronglyMeasurable.aemeasurable.add_const 1)
  have hlimF : ∀ᵐ x ∂torusMeasure d,
      Tendsto (fun n => F n x) atTop (𝓝 (ENNReal.ofReal (g x))) := by
    filter_upwards [hlim] with x hx
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (((Real.continuous_mul_log.tendsto (ρ.value x)).comp hx).add_const 1)
  have hfatou : (∫⁻ x, ENNReal.ofReal (g x) ∂torusMeasure d) ≤ ENNReal.ofReal (C+1) := by
    calc
      _ = ∫⁻ x, liminf (fun n => F n x) atTop ∂torusMeasure d :=
        lintegral_congr_ae (hlimF.mono (fun x hx => hx.liminf_eq.symm))
      _ ≤ liminf (fun n => ∫⁻ x, F n x ∂torusMeasure d) atTop := lintegral_liminf_le' hF
      _ ≤ ENNReal.ofReal (C+1) := by
        apply liminf_le_of_frequently_le'
        exact Eventually.frequently (Eventually.of_forall (fun n => by
          dsimp only [F]
          rw [HeatApproximation.shifted_entropy_integral (r n) (hr n)]
          exact ENNReal.ofReal_le_ofReal (by linarith [hC n])))
  have hgm : AEStronglyMeasurable g (torusMeasure d) :=
    ((Real.continuous_mul_log.comp_aestronglyMeasurable ρ.integrable.aestronglyMeasurable).add_const 1)
  have hgi : Integrable g (torusMeasure d) :=
    (lintegral_ofReal_ne_top_iff_integrable hgm (HeatApproximation.shifted_entropy_nonneg ρ)).mp
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hfatou)
  have hρ : ρ.FiniteEntropy := by
    exact (hgi.sub (integrable_const (1:ℝ))).congr
      (ae_of_all _ (fun x => by simp [g]))
  exact ⟨hρ, HeatApproximation.entropy_le_of_ae_limit ρ hρ r hr C hC hlim⟩

lemma entropy_eventually_lower {d : ℕ} (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy)
    (r : ℕ → ProbabilityDensity d) (hr : ∀ n, (r n).FiniteEntropy)
    (hm : TendstoInMeasure (torusMeasure d) (fun n => (r n).value) atTop ρ.value)
    (a : ℝ) (ha : a < entropy ρ) : ∀ᶠ n in atTop, a < entropy (r n) := by
  by_contra hn
  have hf : ∃ᶠ n in atTop, entropy (r n) ≤ a := by
    simpa only [not_eventually, not_lt] using hn
  obtain ⟨ns,hns,hbad⟩ := extraction_of_frequently_atTop hf
  obtain ⟨ms,hms,hae⟩ := (hm.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  have h := HeatApproximation.entropy_le_of_ae_limit ρ hρ (fun n => r (ns (ms n)))
    (fun n => hr _) a (fun n => hbad _) hae
  exact (not_le.mpr ha) h

lemma sum_le_of_eventually_lower {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (b : ℕ → ι → ℝ) (C : ℝ)
    (hlo : ∀ i ∈ s, ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, a i-ε ≤ b n i)
    (hhi : ∀ n, ∑ i ∈ s, b n i ≤ C) : ∑ i ∈ s, a i ≤ C := by
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ := ε / ((s.card:ℝ)+1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have he : ∀ᶠ n in atTop, ∀ i ∈ s, a i-δ ≤ b n i :=
    (Filter.eventually_all_finset s).mpr (fun i hi => hlo i hi δ hδ)
  obtain ⟨n,hn⟩ := he.exists
  have hsum := (Finset.sum_le_sum hn).trans (hhi n)
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at hsum
  have hδle : (s.card:ℝ)*δ ≤ ε := by
    dsimp [δ]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : (0:ℝ)<(s.card:ℝ)+1)).mpr
    nlinarith
  linarith

#print axioms entropy_eventually_lower
#print axioms sum_le_of_eventually_lower

#print axioms finiteEntropy_of_ae_limit
end BecknerOnofri.HighDim.EntropyShearer
