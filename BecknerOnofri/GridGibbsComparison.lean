import BecknerOnofri.GinibreMonotonicity
import BecknerOnofri.GraphRegularity
import Legacy.TorusEndpoint.GridAliasing

/-! Exact comparison of continuous and grid Gibbs expectations.
Positive Fourier aliasing applies directly to the centered covariance density,
so no unformalized Laplace localization step is required. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace BecknerOnofri.HighDim.GridGibbsComparison
open ContinuousGibbs ContinuousFirstShell GinibreCovariance

abbrev complexify {d : ℕ} (u : Space d) : C(Torus d,ℂ) :=
  Complex.ofRealCLM.compLeftContinuous ℝ (Torus d) u

theorem coefficient_complexify {d : ℕ} (u : Space d) (k : Frequency d) :
    UnitAddTorus.mFourierCoeff (complexify u) k=coefficient k u := by
  rw [coefficient_integral]
  rfl

theorem coefficient_re {d : ℕ} (u : Space d) (k : Frequency d) :
    (coefficient k u).re=mean d (u*cosine k) := by
  rw [coefficient_integral]
  have hi : Integrable (fun x => UnitAddTorus.mFourier (-k) x*(u x : ℂ)) (torusMeasure d) :=
    ((UnitAddTorus.mFourier (-k)).continuous.mul (complexify u).continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have he : (∫ x, UnitAddTorus.mFourier (-k) x*(u x : ℂ) ∂torusMeasure d).re =
      ∫ x, (UnitAddTorus.mFourier (-k) x*(u x : ℂ)).re ∂torusMeasure d := (integral_re hi).symm
  rw [he]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by
    simp only [ContinuousMap.mul_apply,cosine_apply,UnitAddTorus.mFourier_neg,
      RCLike.star_def,Complex.mul_re,Complex.conj_re,Complex.ofReal_re,Complex.ofReal_im,
      mul_zero,sub_zero]
    ring)

theorem cosine_complex {d : ℕ} (k : Frequency d) (x : Torus d) :
    (cosine k x : ℂ)=(UnitAddTorus.mFourier k x+UnitAddTorus.mFourier (-k) x)/2 := by
  rw [UnitAddTorus.mFourier_neg]
  apply Complex.ext <;> simp [cosine,Complex.div_re,Complex.div_im] <;> ring

theorem coefficient_mul_cosine {d : ℕ} (u : Space d) (r k : Frequency d) :
    coefficient k (u*cosine r)=(coefficient (k-r) u+coefficient (k+r) u)/2 := by
  simp only [coefficient_integral]
  have he (x : Torus d) :
      UnitAddTorus.mFourier (-k) x*((u*cosine r) x : ℂ)=
        (UnitAddTorus.mFourier (-(k-r)) x*(u x : ℂ)+
          UnitAddTorus.mFourier (-(k+r)) x*(u x : ℂ))/2 := by
    rw [ContinuousMap.mul_apply,Complex.ofReal_mul,cosine_complex]
    have h1 : -(k-r)= -k+r := by abel
    have h2 : -(k+r)= -k+ -r := by abel
    rw [h1,h2,UnitAddTorus.mFourier_add,UnitAddTorus.mFourier_add]
    ring
  simp_rw [he]
  rw [integral_div,integral_add]
  · exact ((UnitAddTorus.mFourier (-(k-r))).continuous.mul (complexify u).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · exact ((UnitAddTorus.mFourier (-(k+r))).continuous.mul (complexify u).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

theorem summable_mul_cosine {d : ℕ} (u : Space d) (r : Frequency d)
    (hu : Summable (fun k => coefficient k u)) :
    Summable (fun k => coefficient k (u*cosine r)) := by
  have h1 : Summable (fun k => coefficient (k-r) u) :=
    hu.comp_injective (fun _ _ h => sub_left_injective h)
  have h2 : Summable (fun k => coefficient (k+r) u) :=
    hu.comp_injective (fun _ _ h => add_right_cancel h)
  simpa only [coefficient_mul_cosine] using (h1.add h2).div_const 2

theorem cosine_eq_synthesis {d : ℕ} (k : Frequency d) :
    cosine k=synthesis k (1/2 : ℂ) := by
  ext x
  simp [synthesis_apply,cosine_apply,Complex.mul_re]

theorem summable_cosine {d : ℕ} (k : Frequency d) :
    Summable (fun r => coefficient r (cosine k)) := by
  classical
  simp only [cosine_eq_synthesis,coefficient_synthesis]
  exact (hasSum_ite_eq k (1/2 : ℂ)).summable.add (hasSum_ite_eq (-k) (conj (1/2 : ℂ))).summable

theorem summable_cosinePotential {d : ℕ} {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (k : ι → Frequency d) :
    Summable (fun r => coefficient r (cosinePotential a k)) := by
  simp only [cosinePotential,map_sum,map_smul]
  exact summable_sum (fun i _ => (summable_cosine (k i)).mul_left (a i : ℂ))

theorem summable_normalized {d : ℕ} (u : Space d)
    (hu : Summable (fun k => coefficient k u)) :
    Summable (fun k => coefficient k (normalized u)) := by
  have hh := GraphRegularity.normalized_radial u 0
    ((Legacy.BecknerOnofri.RadialWiener.radialSummable_zero _).mpr hu.norm)
  exact ((Legacy.BecknerOnofri.RadialWiener.radialSummable_zero _).mp hh).of_norm

/-- Grid averaging is on the actual image of `(ZMod N)^d` in the torus. -/
def gridMean {d N : ℕ} [NeZero N] (u : Space d) : ℝ :=
  (Legacy.TorusEndpoint.gridAverage (N := N) (complexify u)).re

theorem gridMean_apply {d N : ℕ} [NeZero N] (u : Space d) :
    gridMean (N := N) u=((N : ℝ)^d)⁻¹*∑ j : Fin d → ZMod N,
      u (Legacy.TorusEndpoint.gridPoint j) := by
  rw [gridMean,Legacy.TorusEndpoint.gridAverage_re]
  rfl

theorem gridMean_sub {d N : ℕ} [NeZero N] (u v : Space d) :
    gridMean (N := N) (u-v)=gridMean (N := N) u-gridMean (N := N) v := by
  simp only [gridMean_apply,ContinuousMap.sub_apply,Finset.sum_sub_distrib,mul_sub]

theorem gridMean_smul {d N : ℕ} [NeZero N] (c : ℝ) (u : Space d) :
    gridMean (N := N) (c • u)=c*gridMean (N := N) u := by
  simp only [gridMean_apply,ContinuousMap.smul_apply,smul_eq_mul,← Finset.mul_sum]
  ring

theorem gridMean_normalized_pos {d N : ℕ} [NeZero N] (u : Space d) :
    0<gridMean (N := N) (normalized u) := by
  rw [gridMean_apply]
  have hN : 0<(N : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
  apply mul_pos (inv_pos.mpr (pow_pos hN d))
  exact Finset.sum_pos (fun _ _ => normalized_pos _ _) Finset.univ_nonempty

def gridExpectation {d N : ℕ} [NeZero N] (u f : Space d) : ℝ :=
  gridMean (N := N) (exponential u*f)/gridMean (N := N) (exponential u)

theorem gridExpectation_normalized {d N : ℕ} [NeZero N] (u f : Space d) :
    gridExpectation (N := N) u f=
      gridMean (N := N) (normalized u*f)/gridMean (N := N) (normalized u) := by
  rw [normalized,smul_mul_assoc,gridMean_smul,gridMean_smul]
  unfold gridExpectation
  exact (mul_div_mul_left _ _ (inv_ne_zero (partition_pos u).ne')).symm

/-- The actual centered covariance density has nonnegative real Fourier
coefficients. Its zero integral therefore lies below its exact grid average. -/
theorem cosine_expectation_le_grid {d N : ℕ} [NeZero N] {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (k : ι → Frequency d) (ha : ∀ i,0≤a i) (r : Frequency d) :
    weightedMean (cosinePotential a k) (cosine r)≤
      gridExpectation (N := N) (cosinePotential a k) (cosine r) := by
  let q := cosinePotential a k
  let c := weightedMean q (cosine r)
  let F : Space d := normalized q*cosine r-c • normalized q
  have hρ := summable_normalized q (summable_cosinePotential a k)
  have hF : Summable (fun l => coefficient l F) := by
    simpa only [F,map_sub,map_smul,Complex.real_smul] using
      (summable_mul_cosine (normalized q) r hρ).sub (hρ.mul_left (c : ℂ))
  have hpos (l : Frequency d) : 0≤(coefficient l F).re := by
    rw [coefficient_re]
    have he : mean d (F*cosine l)=logPartitionHessian q (cosine r) (cosine l) := by
      rw [logPartitionHessian_apply]
      simp only [F,sub_mul,smul_mul_assoc,map_sub,map_smul,smul_eq_mul,
        weightedMean_apply,mul_assoc]
      rfl
    rw [he]
    exact cosine_covariance_nonneg a k ha r l
  have hgrid := Legacy.TorusEndpoint.integral_le_grid_average (N := N) (complexify F)
    (hF.congr (fun l => (coefficient_complexify F l).symm)) (by simpa only [coefficient_complexify] using hpos)
  have hzero : mean d F=0 := by
    simp only [F,map_sub,map_smul,mean_normalized,smul_eq_mul,mul_one,c,weightedMean_apply,sub_self]
  have hleft : (∫ x, complexify F x ∂torusMeasure d).re=0 := by
    change (∫ x, (F x : ℂ) ∂torusMeasure d).re=0
    rw [integral_complex_ofReal,Complex.ofReal_re]
    exact hzero
  rw [Legacy.TorusEndpoint.torusMeasure_explicit] at hgrid
  change (∫ x, complexify F x ∂torusMeasure d).re ≤ _ at hgrid
  rw [hleft] at hgrid
  change 0≤gridMean (N := N) F at hgrid
  change 0≤gridMean (N := N) (normalized q*cosine r-c • normalized q) at hgrid
  rw [gridMean_sub,gridMean_smul] at hgrid
  rw [gridExpectation_normalized]
  apply (le_div_iff₀ (gridMean_normalized_pos (N := N) q)).mpr
  linarith

theorem mean_cosine_nonneg {d : ℕ} (r : Frequency d) : 0≤mean d (cosine r) := by
  have he := congrArg Complex.re (coefficient_zero (cosine r))
  rw [cosine_eq_synthesis,coefficient_synthesis] at he
  simp only [Complex.ofReal_re] at he
  rw [cosine_eq_synthesis,← he]
  split_ifs <;> norm_num

theorem cosine_expectation_nonneg {d : ℕ} {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (k : ι → Frequency d) (ha : ∀ i,0≤a i) (r : Frequency d) :
    0≤weightedMean (cosinePotential a k) (cosine r) := by
  have hh := cosine_expectation_mono (fun _ => 0) a k (fun _ => le_rfl) ha r
  have hz : cosinePotential (fun _ : ι => (0:ℝ)) k=0 := by simp [cosinePotential]
  rw [hz,weightedMean_zero] at hh
  exact (mean_cosine_nonneg r).trans hh

theorem exponential_eq_partition_smul {d : ℕ} (u : Space d) :
    exponential u=partition u • normalized u := by
  rw [normalized,smul_smul,mul_inv_cancel₀ (partition_pos u).ne',one_smul]

/-- Exact positive aliasing also controls the unnormalized partition function. -/
theorem partition_le_grid {d N : ℕ} [NeZero N] {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (k : ι → Frequency d) (ha : ∀ i,0≤a i) :
    partition (cosinePotential a k)≤gridMean (N := N) (exponential (cosinePotential a k)) := by
  let q := cosinePotential a k
  have hρ := summable_normalized q (summable_cosinePotential a k)
  have he : Summable (fun r => coefficient r (exponential q)) := by
    rw [exponential_eq_partition_smul]
    simpa only [map_smul,Complex.real_smul] using hρ.mul_left (partition q : ℂ)
  have hpos (r : Frequency d) : 0≤(coefficient r (exponential q)).re := by
    rw [exponential_eq_partition_smul,map_smul,Complex.real_smul,Complex.mul_re]
    simp only [Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,coefficient_re]
    exact mul_nonneg (partition_pos q).le (cosine_expectation_nonneg a k ha r)
  have hh := Legacy.TorusEndpoint.integral_le_grid_average (N := N) (complexify (exponential q))
    (he.congr (fun r => (coefficient_complexify (exponential q) r).symm))
    (by simpa only [coefficient_complexify] using hpos)
  rw [Legacy.TorusEndpoint.torusMeasure_explicit] at hh
  change (∫ x, (exponential q x : ℂ) ∂torusMeasure d).re ≤ _ at hh
  rw [integral_complex_ofReal,Complex.ofReal_re] at hh
  exact hh

#print axioms partition_le_grid
#print axioms cosine_expectation_le_grid
end BecknerOnofri.HighDim.GridGibbsComparison
