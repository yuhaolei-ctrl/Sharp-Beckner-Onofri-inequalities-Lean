import BecknerOnofri.ContinuousGibbs
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Exponentiating a finite nonnegative sum of real rank-one product kernels
preserves positivity of the actual double integral. The proof uses the full
convergent Banach-algebra exponential series and squares of actual integrals. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped Topology BigOperators
namespace BecknerOnofri.GinibrePositiveKernel
variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]

private theorem integrable_cont (μ : Measure X) [IsProbabilityMeasure μ] (f : C(X,ℝ)) :
    Integrable f μ := f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

def expectation (μ : Measure X) [IsProbabilityMeasure μ] : C(X,ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ x, f x ∂μ
      map_add' := fun f g => integral_add (integrable_cont μ f) (integrable_cont μ g)
      map_smul' := fun c f => integral_smul c f }
    1 (by
      intro f
      simp only [one_mul]
      calc
        _ ≤ ∫ x, ‖f x‖ ∂μ := norm_integral_le_integral_norm _
        _ ≤ ∫ _ : X, ‖f‖ ∂μ := integral_mono (integrable_cont μ f).norm (integrable_const _)
          (fun x => f.norm_coe_le_norm x)
        _ = ‖f‖ := by simp)

@[simp] theorem expectation_apply (μ : Measure X) [IsProbabilityMeasure μ] (f : C(X,ℝ)) :
    expectation μ f=∫ x, f x ∂μ := rfl

def tensor (f g : C(X,ℝ)) : C(X×X,ℝ) :=
  ⟨fun p => f p.1*g p.2,(f.continuous.comp continuous_fst).mul (g.continuous.comp continuous_snd)⟩

@[simp] theorem tensor_apply (f g : C(X,ℝ)) (p : X×X) : tensor f g p=f p.1*g p.2 := rfl

theorem tensor_mul (f g h k : C(X,ℝ)) : tensor f g*tensor h k=tensor (f*h) (g*k) := by
  ext p
  simp only [ContinuousMap.mul_apply,tensor_apply]
  ring

theorem expectation_tensor (μ : Measure X) [IsProbabilityMeasure μ] (f g : C(X,ℝ)) :
    expectation (μ.prod μ) (tensor f g)=expectation μ f*expectation μ g := integral_prod_mul f g

def finiteKernel {ι : Type*} [Fintype ι] (a : ι → ℝ) (f : ι → C(X,ℝ)) : C(X×X,ℝ) :=
  ∑ j, a j • tensor (f j) (f j)

theorem finiteKernel_pow {ι : Type*} [Fintype ι] (a : ι → ℝ) (f : ι → C(X,ℝ)) (n : ℕ) :
    finiteKernel a f^n = ∑ w : Fin n → ι, (∏ i, a (w i)) •
      tensor (∏ i, f (w i)) (∏ i, f (w i)) := by
  ext p
  simp only [finiteKernel,ContinuousMap.pow_apply,ContinuousMap.sum_apply,
    ContinuousMap.smul_apply,tensor_apply,ContinuousMap.prod_apply,smul_eq_mul]
  rw [Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro w _
  simp only [Finset.prod_mul_distrib]

theorem finiteKernel_pow_quadratic_nonneg {ι : Type*} [Fintype ι]
    (μ : Measure X) [IsProbabilityMeasure μ] (a : ι → ℝ) (f : ι → C(X,ℝ))
    (ha : ∀ i, 0≤a i) (g : C(X,ℝ)) (n : ℕ) :
    0≤expectation (μ.prod μ) (tensor g g*finiteKernel a f^n) := by
  rw [finiteKernel_pow,Finset.mul_sum,map_sum]
  apply Finset.sum_nonneg
  intro w _
  rw [mul_smul_comm,tensor_mul,map_smul,expectation_tensor,smul_eq_mul]
  exact mul_nonneg (Finset.prod_nonneg (fun _ _ => ha _)) (mul_self_nonneg _)

/-- The exponential of a finite positive separable kernel has nonnegative
quadratic integrals against every continuous real test function. -/
theorem finiteKernel_exp_quadratic_nonneg {ι : Type*} [Fintype ι]
    (μ : Measure X) [IsProbabilityMeasure μ] (a : ι → ℝ) (f : ι → C(X,ℝ))
    (ha : ∀ i, 0≤a i) (g : C(X,ℝ)) :
    0≤∫ p, g p.1*g p.2*Real.exp (∑ i, a i*f i p.1*f i p.2) ∂μ.prod μ := by
  let L : C(X×X,ℝ) →L[ℝ] ℝ := (expectation (μ.prod μ)).comp
    (ContinuousLinearMap.mul ℝ C(X×X,ℝ) (tensor g g))
  have hs := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (finiteKernel a f)).map
    L.toAddMonoidHom L.continuous
  have hn (n : ℕ) : 0≤L ((n.factorial:ℝ)⁻¹ • finiteKernel a f^n) := by
    rw [map_smul,smul_eq_mul]
    exact mul_nonneg (by positivity) (finiteKernel_pow_quadratic_nonneg μ a f ha g n)
  have hpos := hasSum_le (fun n => hn n) (hasSum_zero (α := ℝ) (β := ℕ)) hs
  change 0≤expectation (μ.prod μ) (tensor g g*NormedSpace.exp (finiteKernel a f)) at hpos
  convert hpos using 1
  apply integral_congr_ae
  exact Eventually.of_forall (fun p => by
    have he := NormedSpace.map_exp (ContinuousMap.evalAlgHom ℝ ℝ p)
      (ContinuousMap.evalCLM ℝ p).continuous (finiteKernel a f)
    have hexp : NormedSpace.exp (finiteKernel a f) p=Real.exp (finiteKernel a f p) := by
      simpa only [ContinuousMap.evalAlgHom_apply,Real.exp_eq_exp_ℝ] using he
    rw [ContinuousMap.mul_apply,hexp]
    simp only [tensor_apply,finiteKernel,ContinuousMap.sum_apply,
      ContinuousMap.smul_apply,smul_eq_mul]
    congr 2
    apply Finset.sum_congr rfl
    intro i _
    ring)

#print axioms finiteKernel_exp_quadratic_nonneg
end BecknerOnofri.GinibrePositiveKernel
