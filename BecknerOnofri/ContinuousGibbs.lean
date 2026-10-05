module

public import BecknerOnofri.BranchDefinitions
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Topology.ContinuousMap.Bounded.Basic
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
public import Mathlib.Analysis.Calculus.Deriv.Inv

@[expose] public section

/-! The genuine normalized Gibbs map on the Banach algebra of real continuous
torus potentials: analyticity and its exact derivative at zero. -/
noncomputable section
open MeasureTheory
open scoped Topology
namespace BecknerOnofri.HighDim.ContinuousGibbs

abbrev Space (d : ℕ) := C(Torus d, ℝ)

theorem integrable (d : ℕ) (f : Space d) : Integrable f (torusMeasure d) :=
  f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

def mean (d : ℕ) : Space d →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ x, f x ∂torusMeasure d
      map_add' := fun f g => integral_add (integrable d f) (integrable d g)
      map_smul' := fun c f => integral_smul c f }
    1 (by
      intro f
      simp only [one_mul]
      calc
        _ ≤ ∫ x, ‖f x‖ ∂torusMeasure d := norm_integral_le_integral_norm _
        _ ≤ ∫ _ : Torus d, ‖f‖ ∂torusMeasure d :=
          integral_mono (integrable d f).norm (integrable_const _)
            (fun x => f.norm_coe_le_norm x)
        _ = ‖f‖ := by simp)

@[simp] theorem mean_apply (d : ℕ) (f : Space d) :
    mean d f = ∫ x, f x ∂torusMeasure d := rfl

@[simp] theorem mean_one (d : ℕ) : mean d 1 = 1 := by simp [mean_apply]

def exponential {d : ℕ} (u : Space d) : Space d := NormedSpace.exp u

@[simp] theorem exponential_apply {d : ℕ} (u : Space d) (x : Torus d) :
    exponential u x = Real.exp (u x) := by
  have h := NormedSpace.map_exp (ContinuousMap.evalAlgHom ℝ ℝ x)
    (ContinuousMap.evalCLM ℝ x).continuous u
  simpa only [exponential, ContinuousMap.evalAlgHom_apply, Real.exp_eq_exp_ℝ] using h

def partition {d : ℕ} (u : Space d) : ℝ := mean d (exponential u)

theorem partition_pos {d : ℕ} (u : Space d) : 0 < partition u := by
  change 0 < ∫ x, exponential u x ∂torusMeasure d
  apply (integral_pos_iff_support_of_nonneg
    (fun x => (show 0 < exponential u x by simpa using Real.exp_pos (u x)).le)
    (integrable d (exponential u))).mpr
  have hs : Function.support (fun x => exponential u x) = Set.univ := by
    ext x
    simp [Function.mem_support, (Real.exp_pos (u x)).ne']
  rw [hs]
  simp

def normalized {d : ℕ} (u : Space d) : Space d := (partition u)⁻¹ • exponential u

@[simp] theorem normalized_apply {d : ℕ} (u : Space d) (x : Torus d) :
    normalized u x = normalizedGibbs (fun y => u y) x := by
  simp only [normalized, ContinuousMap.smul_apply, smul_eq_mul,
    exponential_apply, partition, mean_apply, normalizedGibbs]
  ring

theorem exponential_analytic {d : ℕ} (u : Space d) : AnalyticAt ℝ exponential u :=
  NormedSpace.exp_analytic u

theorem partition_analytic {d : ℕ} (u : Space d) : AnalyticAt ℝ partition u :=
  ((mean d).analyticAt (exponential u)).comp (exponential_analytic u)

theorem normalized_analytic {d : ℕ} (u : Space d) : AnalyticAt ℝ normalized u :=
  ((partition_analytic u).inv (partition_pos u).ne').smul (exponential_analytic u)

@[simp] theorem exponential_zero (d : ℕ) : exponential (0 : Space d) = 1 :=
  NormedSpace.exp_zero

@[simp] theorem partition_zero (d : ℕ) : partition (0 : Space d) = 1 := by
  simp [partition]

@[simp] theorem normalized_zero (d : ℕ) : normalized (0 : Space d) = 1 := by
  simp [normalized]

theorem normalized_pos {d : ℕ} (u : Space d) (x : Torus d) : 0 < normalized u x := by
  change 0 < (partition u)⁻¹ * exponential u x
  exact mul_pos (inv_pos.mpr (partition_pos u)) (by simpa using Real.exp_pos (u x))

@[simp] theorem mean_normalized {d : ℕ} (u : Space d) : mean d (normalized u) = 1 := by
  rw [normalized, map_smul]
  change (partition u)⁻¹ * partition u = 1
  exact inv_mul_cancel₀ (partition_pos u).ne'

def center (d : ℕ) : Space d →L[ℝ] Space d :=
  ContinuousLinearMap.id ℝ (Space d) - (ContinuousLinearMap.const ℝ (Torus d)).comp (mean d)

@[simp] theorem center_apply (d : ℕ) (u : Space d) (x : Torus d) :
    center d u x = u x - mean d u := rfl

theorem hasFDerivAt_partition_zero (d : ℕ) :
    HasFDerivAt partition (mean d) (0 : Space d) := by
  have he : HasFDerivAt exponential (1 : Space d →L[ℝ] Space d) 0 :=
    hasFDerivAt_exp_zero
  convert! (mean d).hasFDerivAt.comp 0 he using 1

theorem hasFDerivAt_normalized_zero (d : ℕ) :
    HasFDerivAt normalized (center d) (0 : Space d) := by
  have he : HasFDerivAt exponential (1 : Space d →L[ℝ] Space d) 0 :=
    hasFDerivAt_exp_zero
  have hi := (hasDerivAt_inv (by simp : partition (0 : Space d) ≠ 0)).comp_hasFDerivAt
    (0 : Space d) (hasFDerivAt_partition_zero d)
  have h := hi.smul he
  convert! h using 1
  ext f x
  simp [center, exponential_zero, partition_zero, ContinuousLinearMap.smulRight_apply, sub_eq_add_neg]

def nonlinearRemainder {d : ℕ} (u : Space d) : Space d := normalized u - 1 - center d u

theorem nonlinearRemainder_analytic {d : ℕ} (u : Space d) :
    AnalyticAt ℝ nonlinearRemainder u :=
  ((normalized_analytic u).sub analyticAt_const).sub ((center d).analyticAt u)

@[simp] theorem nonlinearRemainder_zero (d : ℕ) : nonlinearRemainder (0 : Space d) = 0 := by
  simp [nonlinearRemainder]

theorem hasFDerivAt_remainder_zero (d : ℕ) :
    HasFDerivAt (𝕜 := ℝ) nonlinearRemainder 0 (0 : Space d) := by
  convert! ((hasFDerivAt_normalized_zero d).sub_const (1 : Space d)).sub
    ((center d).hasFDerivAt (x := (0 : Space d))) using 1
  simp

theorem nonlinearRemainder_quadratic (d : ℕ) :
    nonlinearRemainder =O[𝓝 (0 : Space d)] (fun u => ‖u‖ ^ 2) := by
  obtain ⟨p, hp⟩ := nonlinearRemainder_analytic (0 : Space d)
  have h0 (u : Fin 0 → Space d) : p 0 u = 0 := by
    simpa using hp.coeff_zero u
  have h1 : continuousMultilinearCurryFin1 ℝ (Space d) (Space d) (p 1) = 0 :=
    hp.hasFDerivAt.unique (hasFDerivAt_remainder_zero d)
  have h1' (u : Space d) : p 1 (fun _ => u) = 0 := by
    have h := congrArg (fun f : Space d →L[ℝ] Space d => f u) h1
    exact h
  have hsum (u : Space d) : p.partialSum 2 u = 0 := by
    simp [FormalMultilinearSeries.partialSum, Finset.sum_range_succ, h0, h1']
  simpa only [zero_add, hsum, sub_zero] using hp.isBigO_sub_partialSum_pow 2

#print axioms normalized_analytic
#print axioms hasFDerivAt_normalized_zero
#print axioms hasFDerivAt_remainder_zero
#print axioms nonlinearRemainder_quadratic
end BecknerOnofri.HighDim.ContinuousGibbs
