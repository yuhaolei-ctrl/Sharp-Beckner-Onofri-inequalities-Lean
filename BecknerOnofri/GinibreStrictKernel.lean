module

public import BecknerOnofri.GinibrePositiveKernel

@[expose] public section

/-! A quantitative single-term lower bound for the actual positive
exponential kernel, retaining one nonzero first-order Taylor contribution. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped Topology BigOperators
namespace BecknerOnofri.GinibrePositiveKernel
variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]

theorem finiteKernel_exp_quadratic_lower {ι : Type*} [Fintype ι]
    (μ : Measure X) [IsProbabilityMeasure μ] (a : ι → ℝ) (f : ι → C(X,ℝ))
    (ha : ∀ i,0≤a i) (g : C(X,ℝ)) (j : ι) :
    a j*(expectation μ (g*f j))^2≤
      expectation (μ.prod μ) (tensor g g*NormedSpace.exp (finiteKernel a f)) := by
  classical
  let L : C(X×X,ℝ) →L[ℝ] ℝ := (expectation (μ.prod μ)).comp
    (ContinuousLinearMap.mul ℝ C(X×X,ℝ) (tensor g g))
  have hs := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (finiteKernel a f)).map
    L.toAddMonoidHom L.continuous
  have hn (n : ℕ) : 0≤L ((n.factorial:ℝ)⁻¹ • finiteKernel a f^n) := by
    rw [map_smul,smul_eq_mul]
    exact mul_nonneg (by positivity) (finiteKernel_pow_quadratic_nonneg μ a f ha g n)
  have hh := sum_le_hasSum ({1} : Finset ℕ) (fun n _ => hn n) hs
  simp only [Finset.sum_singleton,Nat.factorial_one,Nat.cast_one,inv_one,one_smul,pow_one] at hh
  apply le_trans _ hh
  change _≤expectation (μ.prod μ) (tensor g g*finiteKernel a f)
  rw [finiteKernel,Finset.mul_sum,map_sum]
  simp only [mul_smul_comm,tensor_mul,map_smul,expectation_tensor,smul_eq_mul]
  simpa only [pow_two] using Finset.single_le_sum
    (fun i (_ : i∈Finset.univ) => mul_nonneg (ha i) (mul_self_nonneg (expectation μ (g*f i))))
    (Finset.mem_univ j)

theorem finiteKernel_exp_integral_lower {ι : Type*} [Fintype ι]
    (μ : Measure X) [IsProbabilityMeasure μ] (a : ι → ℝ) (f : ι → C(X,ℝ))
    (ha : ∀ i,0≤a i) (g : C(X,ℝ)) (j : ι) :
    a j*(∫ x, g x*f j x ∂μ)^2≤
      ∫ p, g p.1*g p.2*Real.exp (∑ i, a i*f i p.1*f i p.2) ∂μ.prod μ := by
  have hh := finiteKernel_exp_quadratic_lower μ a f ha g j
  convert! hh using 1
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

#print axioms finiteKernel_exp_integral_lower
end BecknerOnofri.GinibrePositiveKernel
