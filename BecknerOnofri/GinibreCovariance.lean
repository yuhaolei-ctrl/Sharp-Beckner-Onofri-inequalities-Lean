import BecknerOnofri.GinibrePositiveKernel
import BecknerOnofri.GinibreHaar
import BecknerOnofri.ContinuousVariations
import BecknerOnofri.Translation

/-! Ginibre cosine covariance positivity for genuine finite nonnegative cosine
potentials and their actual normalized Gibbs densities on the flat torus. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped Topology BigOperators ComplexConjugate
namespace BecknerOnofri.HighDim.GinibreCovariance
open ContinuousGibbs GinibrePositiveKernel

def cosine {d : ℕ} (k : Frequency d) : Space d :=
  ⟨fun x => (UnitAddTorus.mFourier k x).re,Complex.continuous_re.comp (UnitAddTorus.mFourier k).continuous⟩

def sine {d : ℕ} (k : Frequency d) : Space d :=
  ⟨fun x => (UnitAddTorus.mFourier k x).im,Complex.continuous_im.comp (UnitAddTorus.mFourier k).continuous⟩

@[simp] theorem cosine_apply {d : ℕ} (k : Frequency d) (x : Torus d) :
    cosine k x=(UnitAddTorus.mFourier k x).re := rfl

@[simp] theorem sine_apply {d : ℕ} (k : Frequency d) (x : Torus d) :
    sine k x=(UnitAddTorus.mFourier k x).im := rfl

theorem mFourier_neg_argument {d : ℕ} (k : Frequency d) (y : Torus d) :
    UnitAddTorus.mFourier k (-y)=conj (UnitAddTorus.mFourier k y) := by
  rw [← UnitAddTorus.mFourier_neg]
  simp only [UnitAddTorus.mFourier,ContinuousMap.coe_mk,Pi.neg_apply,fourier_apply,zsmul_neg,neg_zsmul]

theorem cosine_add_sub {d : ℕ} (k : Frequency d) (x y : Torus d) :
    cosine k (x+y)+cosine k (x-y)=2*cosine k x*cosine k y := by
  simp only [cosine_apply,sub_eq_add_neg,mFourier_add_argument,mFourier_neg_argument,
    Complex.mul_re,Complex.conj_re,Complex.conj_im]
  ring

theorem cosine_sub_sub {d : ℕ} (k : Frequency d) (x y : Torus d) :
    cosine k (x+y)-cosine k (x-y)= -2*sine k x*sine k y := by
  simp only [cosine_apply,sine_apply,sub_eq_add_neg,mFourier_add_argument,mFourier_neg_argument,
    Complex.mul_re,Complex.conj_re,Complex.conj_im]
  ring

def cosinePotential {d : ℕ} {ι : Type*} [Fintype ι] (a : ι → ℝ) (k : ι → Frequency d) : Space d :=
  ∑ i, a i • cosine (k i)

theorem cosinePotential_double {d : ℕ} {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (k : ι → Frequency d) (x y : Torus d) :
    cosinePotential a k (x+y)+cosinePotential a k (x-y)=
      ∑ i, (2*a i)*cosine (k i) x*cosine (k i) y := by
  simp only [cosinePotential,ContinuousMap.sum_apply,ContinuousMap.smul_apply,smul_eq_mul,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← mul_add,cosine_add_sub]
  ring

/-- The unnormalized two-copy covariance kernel. -/
def doubleCovariance {d : ℕ} (q f g : Space d) : C(Torus d×Torus d,ℝ) :=
  (tensor f 1-tensor 1 f)*(tensor g 1-tensor 1 g)*tensor (exponential q) (exponential q)

theorem doubleCovariance_apply {d : ℕ} (q f g : Space d) (p : Torus d×Torus d) :
    doubleCovariance q f g p=(f p.1-f p.2)*(g p.1-g p.2)*Real.exp (q p.1+q p.2) := by
  simp only [doubleCovariance,ContinuousMap.mul_apply,ContinuousMap.sub_apply,tensor_apply,
    ContinuousMap.one_apply,exponential_apply,mul_one,one_mul,Real.exp_add]

/-- The exact algebraic two-copy identity, with the actual Gibbs normalization. -/
theorem two_copy_identity {d : ℕ} (q f g : Space d) :
    expectation ((torusMeasure d).prod (torusMeasure d)) (doubleCovariance q f g)=
      2*(partition q)^2*logPartitionHessian q f g := by
  have he : doubleCovariance q f g=
      tensor (exponential q*f*g) (exponential q)+tensor (exponential q) (exponential q*f*g)-
        tensor (exponential q*f) (exponential q*g)-tensor (exponential q*g) (exponential q*f) := by
    ext p
    simp only [doubleCovariance,ContinuousMap.mul_apply,ContinuousMap.sub_apply,
      ContinuousMap.add_apply,tensor_apply,ContinuousMap.one_apply]
    ring
  rw [he,map_sub,map_sub,map_add]
  simp only [expectation_tensor,show expectation (torusMeasure d)=mean d from rfl]
  rw [logPartitionHessian_apply]
  simp only [weightedMean_apply,normalized,smul_mul_assoc,map_smul,smul_eq_mul]
  change _=2*(mean d (exponential q))^2*
    ((mean d (exponential q))⁻¹*mean d (exponential q*(f*g))-
      ((mean d (exponential q))⁻¹*mean d (exponential q*f))*
        ((mean d (exponential q))⁻¹*mean d (exponential q*g)))
  rw [← mul_assoc (exponential q) f g]
  have hZ : mean d (exponential q)≠0 := (partition_pos q).ne'
  field_simp
  ring

/-- Every covariance of two cosine characters is nonnegative for a finite
nonnegative cosine potential. Frequencies need not be distinct or nonzero. -/
theorem cosine_covariance_nonneg {d : ℕ} {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (k : ι → Frequency d) (ha : ∀ i,0≤a i) (r s : Frequency d) :
    0≤logPartitionHessian (cosinePotential a k) (cosine r) (cosine s) := by
  let q := cosinePotential a k
  let D := doubleCovariance q (cosine r) (cosine s)
  have hp := finiteKernel_exp_quadratic_nonneg (torusMeasure d) (fun i => 2*a i)
    (fun i => cosine (k i)) (fun i => mul_nonneg (by norm_num) (ha i)) (sine r*sine s)
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
  have hD : 0≤expectation ((torusMeasure d).prod (torusMeasure d)) D := by
    change 0≤∫ p, D p ∂(torusMeasure d).prod (torusMeasure d)
    rw [hi,he]
    positivity
  rw [show D=doubleCovariance q (cosine r) (cosine s) from rfl,two_copy_identity] at hD
  exact nonneg_of_mul_nonneg_right hD (mul_pos (by norm_num) (sq_pos_of_pos (partition_pos q)))

/-- Integral form using the exact normalized Gibbs density from the trusted definitions. -/
theorem normalized_cosine_covariance_nonneg {d : ℕ} {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (k : ι → Frequency d) (ha : ∀ i,0≤a i) (r s : Frequency d) :
    0≤(∫ x, normalizedGibbs (cosinePotential a k) x*cosine r x*cosine s x ∂torusMeasure d)-
      (∫ x, normalizedGibbs (cosinePotential a k) x*cosine r x ∂torusMeasure d)*
      (∫ x, normalizedGibbs (cosinePotential a k) x*cosine s x ∂torusMeasure d) := by
  have h := cosine_covariance_nonneg a k ha r s
  simpa only [logPartitionHessian_apply,weightedMean_apply,mean_apply,ContinuousMap.mul_apply,
    normalized_apply,mul_assoc] using h

#print axioms cosine_covariance_nonneg
#print axioms normalized_cosine_covariance_nonneg
end BecknerOnofri.HighDim.GinibreCovariance
