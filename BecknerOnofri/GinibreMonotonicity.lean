import BecknerOnofri.GinibreCovariance
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Coefficientwise monotonicity of actual normalized cosine expectations,
proved from the genuine Ginibre covariance and the true Gibbs derivative. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter Set
open scoped Topology BigOperators
namespace BecknerOnofri.HighDim.GinibreCovariance
open ContinuousGibbs

theorem cosinePotential_line {d : ℕ} {ι : Type*} [Fintype ι]
    (a b : ι → ℝ) (k : ι → Frequency d) (t : ℝ) :
    cosinePotential a k+t • cosinePotential (fun i => b i-a i) k=
      cosinePotential (fun i => a i+t*(b i-a i)) k := by
  ext x
  simp only [cosinePotential,ContinuousMap.add_apply,ContinuousMap.sum_apply,
    ContinuousMap.smul_apply,smul_eq_mul,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem cosine_expectation_hasDerivAt {d : ℕ} (q v : Space d) (r : Frequency d) (t : ℝ) :
    HasDerivAt (fun t : ℝ => weightedMean (q+t • v) (cosine r))
      (logPartitionHessian (q+t • v) v (cosine r)) t := by
  have hp : HasDerivAt (fun t : ℝ => q+t • v) v t := by
    convert! ((hasDerivAt_id t).smul_const v).const_add q using 1 <;> simp
  have h : HasDerivAt (fun s : ℝ => weightedMean (q+s • v))
      (logPartitionHessian (q+t • v) v) t := by
    apply HasFDerivAt.comp_hasDerivAt t (f := fun s : ℝ => q+s • v) (l := @weightedMean d)
      (f' := v) (l' := logPartitionHessian (q+t • v))
    · convert! hasFDerivAt_weightedMean (q+t • v) using 1
    · convert! hp using 1
  apply HasFDerivAt.comp_hasDerivAt t
    (l := fun A : Space d →L[ℝ] ℝ => A (cosine r))
    (l' := ContinuousLinearMap.apply ℝ ℝ (cosine r))
    (f := fun s : ℝ => weightedMean (q+s • v))
    (f' := logPartitionHessian (q+t • v) v)
  · convert! (ContinuousLinearMap.apply ℝ ℝ (cosine r)).hasFDerivAt using 1
  · convert! h using 1

/-- Increasing finitely many nonnegative cosine coefficients increases every
normalized Gibbs cosine expectation. -/
theorem cosine_expectation_mono {d : ℕ} {ι : Type*} [Fintype ι]
    (a b : ι → ℝ) (k : ι → Frequency d) (ha : ∀ i,0≤a i)
    (hab : ∀ i,a i≤b i) (r : Frequency d) :
    weightedMean (cosinePotential a k) (cosine r)≤
      weightedMean (cosinePotential b k) (cosine r) := by
  let q := cosinePotential a k
  let v := cosinePotential (fun i => b i-a i) k
  let F : ℝ → ℝ := fun t => weightedMean (q+t • v) (cosine r)
  have hD (t : ℝ) : HasDerivAt F (logPartitionHessian (q+t • v) v (cosine r)) t :=
    cosine_expectation_hasDerivAt q v r t
  have hcont : Continuous F := continuous_iff_continuousAt.mpr (fun t => (hD t).continuousAt)
  have hn (t : ℝ) (ht : 0≤t) : 0≤logPartitionHessian (q+t • v) v (cosine r) := by
    have hpos (i : ι) : 0≤a i+t*(b i-a i) := add_nonneg (ha i) (mul_nonneg ht (sub_nonneg.mpr (hab i)))
    change 0≤logPartitionHessian (cosinePotential a k+t • cosinePotential (fun i => b i-a i) k)
      (cosinePotential (fun i => b i-a i) k) (cosine r)
    rw [cosinePotential_line]
    simp only [cosinePotential,map_sum,map_smul,ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smul_apply,smul_eq_mul]
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (sub_nonneg.mpr (hab i))
      (cosine_covariance_nonneg (fun i => a i+t*(b i-a i)) k hpos (k i) r)
  have hmono : MonotoneOn F (Icc (0:ℝ) 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) hcont.continuousOn
      (fun t _ => (hD t).differentiableAt.differentiableWithinAt)
    intro t ht
    rw [interior_Icc] at ht
    rw [(hD t).deriv]
    exact hn t ht.1.le
  have hh := hmono (by simp : (0:ℝ)∈Icc 0 1) (by simp : (1:ℝ)∈Icc 0 1) (by norm_num)
  have h1 : q+(1:ℝ) • v=cosinePotential b k := by
    rw [show q+(1:ℝ) • v=cosinePotential a k+(1:ℝ) • cosinePotential (fun i => b i-a i) k from rfl,
      cosinePotential_line]
    congr 1
    funext i
    ring
  simpa only [F,zero_smul,add_zero,h1] using hh

theorem normalized_cosine_expectation_mono {d : ℕ} {ι : Type*} [Fintype ι]
    (a b : ι → ℝ) (k : ι → Frequency d) (ha : ∀ i,0≤a i)
    (hab : ∀ i,a i≤b i) (r : Frequency d) :
    (∫ x, normalizedGibbs (cosinePotential a k) x*cosine r x ∂torusMeasure d)≤
      ∫ x, normalizedGibbs (cosinePotential b k) x*cosine r x ∂torusMeasure d := by
  simpa only [weightedMean_apply,mean_apply,ContinuousMap.mul_apply,normalized_apply] using
    cosine_expectation_mono a b k ha hab r

#print axioms cosine_expectation_mono
#print axioms normalized_cosine_expectation_mono
end BecknerOnofri.HighDim.GinibreCovariance
