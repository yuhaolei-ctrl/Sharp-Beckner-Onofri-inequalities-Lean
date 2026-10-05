module

public import BecknerOnofri.GinibreStrictKernel
public import BecknerOnofri.GridGibbsComparison
public import BecknerOnofri.GinibreNormMonotonicity

@[expose] public section

/-! Quantitative strict Ginibre covariance. A positive difference-frequency
coefficient contributes a strictly positive first-order tensor-square term. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped Topology BigOperators ComplexConjugate
namespace BecknerOnofri.HighDim.GinibreCovariance
open ContinuousGibbs ContinuousFirstShell GinibrePositiveKernel

theorem cosine_mean_eq {d : ℕ} (k : Frequency d) :
    mean d (cosine k)=if k=0 then 1 else 0 := by
  have he := GridGibbsComparison.coefficient_re (ContinuousMap.const (Torus d) 1) k
  simp only [show (ContinuousMap.const (Torus d) (1:ℝ))=1 from rfl,one_mul] at he
  rw [← he]
  change (coefficient k (ContinuousMap.const (Torus d) (1:ℝ))).re=_
  rw [coefficient_const]
  split_ifs <;> norm_num

theorem cosine_mul_cosine {d : ℕ} (r s : Frequency d) :
    cosine r*cosine s=(1/2:ℝ) • (cosine (r-s)+cosine (r+s)) := by
  ext x
  simp only [ContinuousMap.mul_apply,ContinuousMap.smul_apply,ContinuousMap.add_apply,
    smul_eq_mul,cosine_apply,sub_eq_add_neg,UnitAddTorus.mFourier_add,UnitAddTorus.mFourier_neg,
    Complex.mul_re,Complex.conj_re,Complex.conj_im]
  ring

theorem sine_mul_sine {d : ℕ} (r s : Frequency d) :
    sine r*sine s=(1/2:ℝ) • (cosine (r-s)-cosine (r+s)) := by
  ext x
  change sine r x*sine s x=(1/2:ℝ)*(cosine (r-s) x-cosine (r+s) x)
  simp only [ContinuousMap.mul_apply,ContinuousMap.smul_apply,ContinuousMap.sub_apply,
    smul_eq_mul,cosine_apply,sine_apply,sub_eq_add_neg,UnitAddTorus.mFourier_add,UnitAddTorus.mFourier_neg,
    Complex.mul_re,Complex.conj_re,Complex.conj_im]
  ring

private theorem frequency_double_ne_zero {d : ℕ} {k : Frequency d} (hk : k≠0) : k+k≠0 := by
  intro h
  apply hk
  funext i
  have hi := congrFun h i
  change k i+k i=0 at hi
  change k i=0
  omega

theorem sine_sine_cosine_moment {d : ℕ} (r s : Frequency d)
    (hr : r≠0) (hs : s≠0) (hrs : r≠s) :
    mean d (sine r*sine s*cosine (r-s))=1/4 := by
  rw [sine_mul_sine,smul_mul_assoc,sub_mul,cosine_mul_cosine,cosine_mul_cosine]
  simp only [map_smul,map_sub,map_add,smul_eq_mul,cosine_mean_eq]
  have hd : r-s≠0 := sub_ne_zero.mpr hrs
  have h1 : r-s-(r-s)=0 := by abel
  have h2 : r+s-(r-s)=s+s := by abel
  have h3 : r+s+(r-s)=r+r := by abel
  rw [h1,h2,h3,if_pos rfl,if_neg (frequency_double_ne_zero hd),
    if_neg (frequency_double_ne_zero hs),if_neg (frequency_double_ne_zero hr)]
  norm_num

/-- Quantitative covariance lower bound from any retained finite kernel term. -/
theorem cosine_covariance_moment_lower {d : ℕ} {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (k : ι → Frequency d) (ha : ∀ i,0≤a i)
    (r s : Frequency d) (j : ι) :
    4*a j*(mean d (sine r*sine s*cosine (k j)))^2≤
      (partition (cosinePotential a k))^2*logPartitionHessian (cosinePotential a k) (cosine r) (cosine s) := by
  let q := cosinePotential a k
  let D := doubleCovariance q (cosine r) (cosine s)
  have hp := finiteKernel_exp_integral_lower (torusMeasure d) (fun i => 2*a i)
    (fun i => cosine (k i)) (fun i => mul_nonneg (by norm_num) (ha i)) (sine r*sine s) j
  have he : (∫ p, D (GinibreHaar.doubleMap d p) ∂(torusMeasure d).prod (torusMeasure d))=
      4*(∫ p : Torus d×Torus d, (sine r*sine s) p.1*(sine r*sine s) p.2*
        Real.exp (∑ i, (2*a i)*cosine (k i) p.1*cosine (k i) p.2)
          ∂(torusMeasure d).prod (torusMeasure d)) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall (fun p => by
      dsimp only
      rw [show D (GinibreHaar.doubleMap d p)=
        (cosine r (p.1+p.2)-cosine r (p.1-p.2))*
        (cosine s (p.1+p.2)-cosine s (p.1-p.2))*
        Real.exp (q (p.1+p.2)+q (p.1-p.2)) from doubleCovariance_apply _ _ _ _,
        cosine_sub_sub,cosine_sub_sub,cosinePotential_double]
      simp only [ContinuousMap.mul_apply]
      ring)
  have hi := integral_map (μ := (torusMeasure d).prod (torusMeasure d))
    (f := (D : Torus d×Torus d → ℝ)) (GinibreHaar.doubleMap_measurePreserving d).measurable.aemeasurable
    D.continuous.aestronglyMeasurable
  rw [(GinibreHaar.doubleMap_measurePreserving d).map_eq] at hi
  have hD : (8*a j)*(mean d (sine r*sine s*cosine (k j)))^2≤
      expectation ((torusMeasure d).prod (torusMeasure d)) D := by
    change _≤∫ p, D p ∂(torusMeasure d).prod (torusMeasure d)
    rw [hi,he]
    change (2*a j)*(mean d (sine r*sine s*cosine (k j)))^2≤_ at hp
    linarith
  rw [show D=doubleCovariance q (cosine r) (cosine s) from rfl,two_copy_identity] at hD
  change (8*a j)*(mean d (sine r*sine s*cosine (k j)))^2≤
    2*(partition (cosinePotential a k))^2*logPartitionHessian (cosinePotential a k) (cosine r) (cosine s) at hD
  linarith

theorem cosine_covariance_difference_lower {d : ℕ} {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (k : ι → Frequency d) (ha : ∀ i,0≤a i)
    (r s : Frequency d) (hr : r≠0) (hs : s≠0) (hrs : r≠s)
    (j : ι) (hj : k j=r-s) :
    a j/4≤(partition (cosinePotential a k))^2*
      logPartitionHessian (cosinePotential a k) (cosine r) (cosine s) := by
  have hh := cosine_covariance_moment_lower a k ha r s j
  rw [hj,sine_sine_cosine_moment r s hr hs hrs] at hh
  nlinarith

/-- The same quantitative term survives the genuine uniform series limit. -/
theorem cosineSeries_covariance_difference_lower {d : ℕ} {ι : Type*}
    (a : ι → ℝ) (k : ι → Frequency d) (ha : ∀ i,0≤a i) (has : Summable a)
    (r s : Frequency d) (hr : r≠0) (hs : s≠0) (hrs : r≠s)
    (j : ι) (hj : k j=r-s) :
    a j/4≤(partition (cosineSeries a k))^2*
      logPartitionHessian (cosineSeries a k) (cosine r) (cosine s) := by
  classical
  have hc : Continuous (fun q : Space d => (partition q)^2*logPartitionHessian q (cosine r) (cosine s)) :=
    (partition_continuous.pow 2).mul (covariance_continuous_potential (cosine r) (cosine s))
  have hl := (hc.tendsto _).comp (cosineSeries_tendsto a k ha has)
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hl
  filter_upwards [eventually_ge_atTop ({j} : Finset ι)] with F hF
  have hjF : j∈F := hF (by simp)
  exact cosine_covariance_difference_lower (fun i : F => a i) (fun i => k i)
    (fun i => ha i) r s hr hs hrs ⟨j,hjF⟩ hj

theorem cosineSeries_covariance_pos {d : ℕ} {ι : Type*}
    (a : ι → ℝ) (k : ι → Frequency d) (ha : ∀ i,0≤a i) (has : Summable a)
    (r s : Frequency d) (hr : r≠0) (hs : s≠0) (hrs : r≠s)
    (j : ι) (hj : k j=r-s) (haj : 0<a j) :
    0<logPartitionHessian (cosineSeries a k) (cosine r) (cosine s) := by
  have hl := cosineSeries_covariance_difference_lower a k ha has r s hr hs hrs j hj
  by_contra hn
  have hh := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (partition (cosineSeries a k)))
    (le_of_not_gt hn)
  linarith

#print axioms sine_sine_cosine_moment
#print axioms cosine_covariance_difference_lower
#print axioms cosineSeries_covariance_difference_lower
#print axioms cosineSeries_covariance_pos
end BecknerOnofri.HighDim.GinibreCovariance
