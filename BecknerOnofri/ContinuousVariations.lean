module

public import BecknerOnofri.ContinuousLogPartitionTaylor
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM

@[expose] public section

/-! Exact Fréchet variations of the real continuous Gibbs map and log partition. -/
noncomputable section
open MeasureTheory
namespace BecknerOnofri.HighDim.ContinuousGibbs

/-- Continuous bilinear pairing by integration of the pointwise product. -/
def meanProduct (d : ℕ) : Space d →L[ℝ] Space d →L[ℝ] ℝ :=
  (ContinuousLinearMap.compL ℝ (Space d) (Space d) ℝ (mean d)).comp
    (ContinuousLinearMap.mul ℝ (Space d))

@[simp] theorem meanProduct_apply {d : ℕ} (u h : Space d) : meanProduct d u h = mean d (u*h) := rfl

/-- Expectation against the actual normalized Gibbs density. -/
def weightedMean {d : ℕ} (u : Space d) : Space d →L[ℝ] ℝ := meanProduct d (normalized u)

theorem weightedMean_apply {d : ℕ} (u h : Space d) : weightedMean u h = mean d (normalized u * h) := rfl

@[simp] theorem weightedMean_one {d : ℕ} (u : Space d) : weightedMean u 1 = 1 := by
  rw [weightedMean_apply, mul_one, mean_normalized]

def partitionDerivative {d : ℕ} (u : Space d) : Space d →L[ℝ] ℝ := meanProduct d (exponential u)

/-- The genuine derivative of the normalized exponential. -/
def normalizedDerivative {d : ℕ} (u : Space d) : Space d →L[ℝ] Space d :=
  ContinuousLinearMap.mul ℝ (Space d) (normalized u) - (weightedMean u).smulRight (normalized u)

theorem normalizedDerivative_apply {d : ℕ} (u h : Space d) :
    normalizedDerivative u h = normalized u * h - weightedMean u h • normalized u := rfl

theorem normalizedDerivative_apply_point {d : ℕ} (u h : Space d) (x : Torus d) :
    normalizedDerivative u h x = normalized u x * (h x - mean d (normalized u * h)) := by
  simp only [normalizedDerivative_apply, weightedMean_apply, ContinuousMap.sub_apply,
    ContinuousMap.mul_apply, ContinuousMap.smul_apply, smul_eq_mul]
  ring

theorem weightedMean_eq_scaled_partitionDerivative {d : ℕ} (u : Space d) :
    weightedMean u = (partition u)⁻¹ • partitionDerivative u := by
  ext h
  simp only [weightedMean_apply, normalized, smul_mul_assoc, map_smul, partitionDerivative,
    smul_apply, meanProduct_apply]

theorem hasFDerivAt_exponential {d : ℕ} (u : Space d) :
    HasFDerivAt exponential (ContinuousLinearMap.mul ℝ (Space d) (exponential u)) u := by
  convert! (hasFDerivAt_exp (𝕂 := ℝ) (x := u)) using 1

theorem hasFDerivAt_partition {d : ℕ} (u : Space d) :
    HasFDerivAt partition (partitionDerivative u) u := by
  convert! (mean d).hasFDerivAt.comp u (hasFDerivAt_exponential u) using 1

theorem hasFDerivAt_normalized {d : ℕ} (u : Space d) :
    HasFDerivAt normalized (normalizedDerivative u) u := by
  have hi := (hasDerivAt_inv (partition_pos u).ne').comp_hasFDerivAt u (hasFDerivAt_partition u)
  have hh := hi.smul (hasFDerivAt_exponential u)
  convert! hh using 1
  ext h x
  simp only [normalizedDerivative_apply, weightedMean_eq_scaled_partitionDerivative,
    smul_apply, normalized, ContinuousMap.sub_apply, ContinuousMap.mul_apply,
    ContinuousMap.smul_apply, smul_eq_mul, add_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.mul_apply',
    ContinuousMap.add_apply, Function.comp_apply]
  ring

@[simp] theorem fderiv_normalized {d : ℕ} (u : Space d) :
    fderiv ℝ normalized u = normalizedDerivative u := (hasFDerivAt_normalized u).fderiv

/-- Uncentered real log partition; the centered version is its composition with `center`. -/
def logPartitionReal {d : ℕ} (u : Space d) : ℝ := Real.log (partition u)

theorem hasFDerivAt_logPartitionReal {d : ℕ} (u : Space d) :
    HasFDerivAt logPartitionReal (weightedMean u) u := by
  rw [weightedMean_eq_scaled_partitionDerivative]
  exact (hasFDerivAt_partition u).log (partition_pos u).ne'

@[simp] theorem fderiv_logPartitionReal {d : ℕ} (u : Space d) :
    fderiv ℝ logPartitionReal u = weightedMean u := (hasFDerivAt_logPartitionReal u).fderiv

/-- The actual Fréchet Hessian of the log partition, as a continuous bilinear map. -/
def logPartitionHessian {d : ℕ} (u : Space d) : Space d →L[ℝ] Space d →L[ℝ] ℝ :=
  (meanProduct d).comp (normalizedDerivative u)

theorem hasFDerivAt_weightedMean {d : ℕ} (u : Space d) :
    HasFDerivAt weightedMean (logPartitionHessian u) u := by
  have hh := HasFDerivAt.comp (𝕜 := ℝ) (E := Space d) (F := Space d)
    (G := Space d →L[ℝ] ℝ) (f := @normalized d) (g := fun v : Space d => meanProduct d v)
    (f' := normalizedDerivative u) (g' := meanProduct d) u
    (by convert! (meanProduct d).hasFDerivAt (x := normalized u) using 1)
    (by convert! hasFDerivAt_normalized u using 1)
  convert! hh using 1

theorem hasFDerivAt_fderiv_logPartitionReal {d : ℕ} (u : Space d) :
    HasFDerivAt (fderiv ℝ (@logPartitionReal d)) (logPartitionHessian u) u := by
  have he : fderiv ℝ (@logPartitionReal d) = weightedMean := funext fderiv_logPartitionReal
  rw [he]
  exact hasFDerivAt_weightedMean u

theorem logPartitionHessian_apply {d : ℕ} (u h k : Space d) :
    logPartitionHessian u h k = weightedMean u (h*k) - weightedMean u h * weightedMean u k := by
  change mean d ((normalizedDerivative u h)*k) = _
  rw [normalizedDerivative_apply, sub_mul, smul_mul_assoc, map_sub, map_smul]
  simp only [smul_eq_mul, weightedMean_apply, mul_assoc]

theorem logPartitionHessian_symmetric {d : ℕ} (u h k : Space d) :
    logPartitionHessian u h k = logPartitionHessian u k h := by
  simp only [logPartitionHessian_apply, mul_comm]

/-- Variance under the actual strictly positive Gibbs density. -/
def gibbsVariance {d : ℕ} (u h : Space d) : ℝ :=
  weightedMean u ((h - ContinuousMap.const (Torus d) (weightedMean u h))^2)

theorem gibbsVariance_eq {d : ℕ} (u h : Space d) :
    gibbsVariance u h = weightedMean u (h^2) - (weightedMean u h)^2 := by
  have he : (h - ContinuousMap.const (Torus d) (weightedMean u h))^2 =
      h^2 - (2*weightedMean u h) • h + (weightedMean u h)^2 • (1 : Space d) := by
    ext x
    simp only [ContinuousMap.pow_apply, ContinuousMap.sub_apply, ContinuousMap.add_apply,
      ContinuousMap.const_apply, ContinuousMap.smul_apply, ContinuousMap.one_apply, smul_eq_mul]
    ring
  rw [gibbsVariance, he, map_add, map_sub, map_smul, map_smul, weightedMean_one]
  simp only [smul_eq_mul, mul_one]
  ring

theorem logPartitionHessian_diag {d : ℕ} (u h : Space d) :
    logPartitionHessian u h h = gibbsVariance u h := by
  rw [logPartitionHessian_apply, gibbsVariance_eq]
  simp only [pow_two]

theorem gibbsVariance_nonneg {d : ℕ} (u h : Space d) : 0 ≤ gibbsVariance u h := by
  change 0 ≤ ∫ x, normalized u x * (h x - weightedMean u h)^2 ∂torusMeasure d
  exact integral_nonneg (fun x => mul_nonneg (normalized_pos u x).le (sq_nonneg _))

theorem logPartitionHessian_nonneg {d : ℕ} (u h : Space d) : 0 ≤ logPartitionHessian u h h := by
  rw [logPartitionHessian_diag]
  exact gibbsVariance_nonneg u h

@[simp] theorem weightedMean_const {d : ℕ} (u : Space d) (c : ℝ) :
    weightedMean u (ContinuousMap.const (Torus d) c) = c := by
  have he : ContinuousMap.const (Torus d) c = c • (1 : Space d) := by ext x; simp
  rw [he, map_smul, weightedMean_one, smul_eq_mul, mul_one]

/-- The variance vanishes precisely in the constant directions. -/
theorem gibbsVariance_eq_zero_iff {d : ℕ} (u h : Space d) :
    gibbsVariance u h = 0 ↔ ∃ c : ℝ, h = ContinuousMap.const (Torus d) c := by
  constructor
  · intro hz
    let g : Space d := normalized u * (h - ContinuousMap.const (Torus d) (weightedMean u h))^2
    have hn : 0 ≤ (fun x => g x) := by
      intro x
      exact mul_nonneg (normalized_pos u x).le (sq_nonneg _)
    have hi := integrable d g
    have hae : (fun x => g x) =ᵐ[torusMeasure d] 0 :=
      (integral_eq_zero_iff_of_nonneg hn hi).mp hz
    have heq : (fun x => h x) =ᵐ[torusMeasure d] (fun _ => weightedMean u h) := by
      filter_upwards [hae] with x hx
      change normalized u x * (h x - weightedMean u h)^2 = 0 at hx
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp ((mul_eq_zero.mp hx).resolve_left (normalized_pos u x).ne'))
    haveI : (torusMeasure d).IsOpenPosMeasure := by unfold torusMeasure; infer_instance
    exact ⟨weightedMean u h, ContinuousMap.ext (congrFun
      (Measure.eq_of_ae_eq heq h.continuous continuous_const))⟩
  · rintro ⟨c, rfl⟩
    rw [gibbsVariance, weightedMean_const, sub_self, zero_pow (by norm_num : (2:ℕ) ≠ 0), map_zero]

theorem logPartitionHessian_nullspace {d : ℕ} (u h : Space d) :
    logPartitionHessian u h h = 0 ↔ ∃ c : ℝ, h = ContinuousMap.const (Torus d) c := by
  rw [logPartitionHessian_diag, gibbsVariance_eq_zero_iff]

@[simp] theorem normalizedDerivative_zero (d : ℕ) : normalizedDerivative (0 : Space d) = center d :=
  (hasFDerivAt_normalized (0 : Space d)).unique (hasFDerivAt_normalized_zero d)

@[simp] theorem weightedMean_zero (d : ℕ) : weightedMean (0 : Space d) = mean d := by
  ext h
  rw [weightedMean_apply, normalized_zero, one_mul]

theorem logPartitionHessian_zero {d : ℕ} (h k : Space d) :
    logPartitionHessian (0 : Space d) h k = mean d (h*k) - mean d h * mean d k := by
  rw [logPartitionHessian_apply, weightedMean_zero]

theorem exponential_center {d : ℕ} (u : Space d) :
    exponential (center d u) = Real.exp (-mean d u) • exponential u := by
  ext x
  simp only [exponential_apply, center_apply, ContinuousMap.smul_apply, smul_eq_mul,
    Real.exp_sub, Real.exp_neg, div_eq_mul_inv]
  ring

theorem partition_center {d : ℕ} (u : Space d) :
    partition (center d u) = Real.exp (-mean d u) * partition u := by
  rw [partition, exponential_center, map_smul]
  rfl

@[simp] theorem normalized_center {d : ℕ} (u : Space d) : normalized (center d u) = normalized u := by
  unfold normalized
  rw [partition_center, exponential_center, smul_smul]
  have he : (Real.exp (-mean d u) * partition u)⁻¹ * Real.exp (-mean d u) = (partition u)⁻¹ := by
    field_simp [(Real.exp_pos (-mean d u)).ne', (partition_pos u).ne']
  rw [he]

theorem centeredLogPartition_eq {d : ℕ} (u : Space d) :
    centeredLogPartition u = logPartitionReal u - mean d u := by
  rw [centeredLogPartition, partition_center,
    Real.log_mul (Real.exp_pos _).ne' (partition_pos u).ne', Real.log_exp]
  unfold logPartitionReal
  ring

theorem hasFDerivAt_centeredLogPartition {d : ℕ} (u : Space d) :
    HasFDerivAt centeredLogPartition (weightedMean u - mean d) u := by
  have he : @centeredLogPartition d = fun v => logPartitionReal v - mean d v :=
    funext centeredLogPartition_eq
  rw [he]
  convert! (hasFDerivAt_logPartitionReal u).sub ((mean d).hasFDerivAt (x := u)) using 1

@[simp] theorem fderiv_centeredLogPartition {d : ℕ} (u : Space d) :
    fderiv ℝ centeredLogPartition u = weightedMean u - mean d :=
  (hasFDerivAt_centeredLogPartition u).fderiv

/-- The centered partition in the trusted theorem has exactly the same Hessian. -/
theorem hasFDerivAt_fderiv_centeredLogPartition {d : ℕ} (u : Space d) :
    HasFDerivAt (fderiv ℝ (@centeredLogPartition d)) (logPartitionHessian u) u := by
  have he : fderiv ℝ (@centeredLogPartition d) = fun v => weightedMean v - mean d :=
    funext fderiv_centeredLogPartition
  rw [he]
  have hh := (hasFDerivAt_sub_const_iff (𝕜 := ℝ) (E := Space d) (F := Space d →L[ℝ] ℝ)
    (f := @weightedMean d) (f' := logPartitionHessian u) (x := u) (mean d)).mpr
    (by convert! hasFDerivAt_weightedMean u using 1)
  convert! hh using 1

#print axioms hasFDerivAt_normalized
#print axioms hasFDerivAt_fderiv_centeredLogPartition
#print axioms logPartitionHessian_nullspace
#print axioms hasFDerivAt_fderiv_logPartitionReal
#print axioms logPartitionHessian_diag
end BecknerOnofri.HighDim.ContinuousGibbs
