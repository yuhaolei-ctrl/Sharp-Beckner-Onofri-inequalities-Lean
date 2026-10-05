import BecknerOnofri.GinibreMonotonicity

/-! Summable nonnegative cosine series define genuine uniformly convergent
continuous potentials. Ginibre covariance and normalized expectations pass to
their actual continuous limits. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped Topology BigOperators
namespace BecknerOnofri.HighDim.GinibreCovariance
open ContinuousGibbs

theorem cosine_norm_le_one {d : ℕ} (k : Frequency d) : ‖cosine k‖≤1 := by
  apply (ContinuousMap.norm_le _ (by norm_num : (0:ℝ)≤1)).mpr
  intro x
  change ‖(UnitAddTorus.mFourier k x).re‖≤1
  exact (show ‖(UnitAddTorus.mFourier k x).re‖≤‖UnitAddTorus.mFourier k x‖ from Complex.abs_re_le_norm _).trans_eq (mFourier_norm_apply k x)

theorem cosineSeries_summable {d : ℕ} {ι : Type*} (a : ι → ℝ) (k : ι → Frequency d)
    (ha : ∀ i,0≤a i) (hs : Summable a) : Summable (fun i => a i • cosine (k i)) := by
  apply hs.of_norm_bounded
  intro i
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (ha i)]
  exact mul_le_of_le_one_right (ha i) (cosine_norm_le_one (k i))

theorem cosineSeries_norm_summable {d : ℕ} {ι : Type*} (a : ι → ℝ) (k : ι → Frequency d)
    (ha : ∀ i,0≤a i) (hs : Summable a) : Summable (fun i => ‖a i • cosine (k i)‖) := by
  apply hs.of_norm_bounded
  intro i
  rw [norm_norm,norm_smul,Real.norm_eq_abs,abs_of_nonneg (ha i)]
  exact mul_le_of_le_one_right (ha i) (cosine_norm_le_one (k i))

def cosineSeries {d : ℕ} {ι : Type*} (a : ι → ℝ) (k : ι → Frequency d) : Space d :=
  ∑' i, a i • cosine (k i)

theorem cosineSeries_norm_le {d : ℕ} {ι : Type*} (a : ι → ℝ) (k : ι → Frequency d)
    (ha : ∀ i,0≤a i) (hs : Summable a) : ‖cosineSeries a k‖≤∑' i,a i := by
  apply (norm_tsum_le_tsum_norm (cosineSeries_norm_summable a k ha hs)).trans
  apply Summable.tsum_le_tsum _ (cosineSeries_norm_summable a k ha hs) hs
  intro i
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (ha i)]
  exact mul_le_of_le_one_right (ha i) (cosine_norm_le_one (k i))

theorem finitePotential_eq_sum {d : ℕ} {ι : Type*} (a : ι → ℝ) (k : ι → Frequency d) (s : Finset ι) :
    cosinePotential (fun i : s => a i) (fun i => k i)=∑ i∈s,a i • cosine (k i) := by
  classical
  unfold cosinePotential
  convert! Finset.sum_attach s (fun i => a i • cosine (k i)) using 1

theorem cosineSeries_tendsto {d : ℕ} {ι : Type*} (a : ι → ℝ) (k : ι → Frequency d)
    (ha : ∀ i,0≤a i) (hs : Summable a) :
    Tendsto (fun s : Finset ι => cosinePotential (fun i : s => a i) (fun i => k i)) atTop
      (𝓝 (cosineSeries a k)) := by
  simp_rw [finitePotential_eq_sum]
  exact (cosineSeries_summable a k ha hs).hasSum

theorem weightedMean_continuous_apply {d : ℕ} (h : Space d) :
    Continuous (fun q : Space d => weightedMean q h) := by
  have hn : Continuous (@normalized d) := continuous_iff_continuousAt.mpr
    (fun q => (normalized_analytic q).continuousAt)
  change Continuous (fun q : Space d => mean d (normalized q*h))
  exact (mean d).continuous.comp (hn.mul continuous_const)

theorem covariance_continuous_potential {d : ℕ} (f g : Space d) :
    Continuous (fun q : Space d => logPartitionHessian q f g) := by
  simp_rw [logPartitionHessian_apply]
  exact (weightedMean_continuous_apply (f*g)).sub
    ((weightedMean_continuous_apply f).mul (weightedMean_continuous_apply g))

/-- Ginibre's inequality for arbitrary summable nonnegative cosine series.
The summability proves convergence in the continuous supremum norm itself. -/
theorem cosineSeries_covariance_nonneg {d : ℕ} {ι : Type*}
    (a : ι → ℝ) (k : ι → Frequency d) (ha : ∀ i,0≤a i) (hs : Summable a) (r s : Frequency d) :
    0≤logPartitionHessian (cosineSeries a k) (cosine r) (cosine s) := by
  have hl := (covariance_continuous_potential (cosine r) (cosine s)).tendsto (cosineSeries a k)
    |>.comp (cosineSeries_tendsto a k ha hs)
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hl (Eventually.of_forall (fun F : Finset ι =>
    cosine_covariance_nonneg (fun i : F => a i) (fun i => k i) (fun i => ha i) r s))

theorem cosineSeries_expectation_mono {d : ℕ} {ι : Type*}
    (a b : ι → ℝ) (k : ι → Frequency d) (ha : ∀ i,0≤a i) (hab : ∀ i,a i≤b i)
    (has : Summable a) (hbs : Summable b) (r : Frequency d) :
    weightedMean (cosineSeries a k) (cosine r)≤weightedMean (cosineSeries b k) (cosine r) := by
  have hb (i : ι) : 0≤b i := (ha i).trans (hab i)
  have hl := (weightedMean_continuous_apply (cosine r)).tendsto (cosineSeries a k)
    |>.comp (cosineSeries_tendsto a k ha has)
  have hr := (weightedMean_continuous_apply (cosine r)).tendsto (cosineSeries b k)
    |>.comp (cosineSeries_tendsto b k hb hbs)
  exact le_of_tendsto_of_tendsto hl hr (Eventually.of_forall (fun F : Finset ι =>
    cosine_expectation_mono (fun i : F => a i) (fun i => b i) (fun i => k i)
      (fun i => ha i) (fun i => hab i) r))

theorem normalized_cosineSeries_expectation_mono {d : ℕ} {ι : Type*}
    (a b : ι → ℝ) (k : ι → Frequency d) (ha : ∀ i,0≤a i) (hab : ∀ i,a i≤b i)
    (has : Summable a) (hbs : Summable b) (r : Frequency d) :
    (∫ x, normalizedGibbs (cosineSeries a k) x*cosine r x ∂torusMeasure d)≤
      ∫ x, normalizedGibbs (cosineSeries b k) x*cosine r x ∂torusMeasure d := by
  simpa only [weightedMean_apply,mean_apply,ContinuousMap.mul_apply,normalized_apply] using
    cosineSeries_expectation_mono a b k ha hab has hbs r

#print axioms cosineSeries_covariance_nonneg
#print axioms normalized_cosineSeries_expectation_mono
end BecknerOnofri.HighDim.GinibreCovariance
