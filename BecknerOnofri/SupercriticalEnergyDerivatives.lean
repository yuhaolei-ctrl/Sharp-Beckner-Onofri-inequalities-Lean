import BecknerOnofri.BranchDerivativeLimits
import BecknerOnofri.AmplitudeDifferentiability
import BecknerOnofri.SupercriticalBranchEnergy
import Mathlib.Analysis.Calculus.Deriv.Inv

/-! Genuine first and second derivatives of the supercritical energy. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter Asymptotics Set
open scoped Topology
namespace BecknerOnofri.HighDim.DiagonalScalarBranch

lemma eventually_local_right {P : ℝ → Prop} {a : ℝ} (h : ∀ᶠ x in 𝓝[>] a, P x) :
    ∀ᶠ x in 𝓝[>] a, ∀ᶠ y in 𝓝 x, P y := by
  filter_upwards [eventually_eventually_nhdsWithin.mpr h,self_mem_nhdsWithin] with x hx hp
  rwa [nhdsWithin_eq_nhds.mpr (Ioi_mem_nhds hp)] at hx

lemma supercriticalEnergy_hasDerivAt {d : ℕ} (hd : 12 ≤ d) :
    ∀ᶠ μ in 𝓝[>] (1:ℝ), HasDerivAt (supercriticalEnergy hd)
      (deriv (branchEnergy hd) (amplitude hd μ)/deriv (parameter hd) (amplitude hd μ)) μ := by
  filter_upwards [amplitude_hasDerivAt hd,
    (amplitude_tendsto hd).eventually (branchEnergy_analytic hd).eventually_analyticAt] with μ ha he
  simpa only [supercriticalEnergy,Function.comp_def,div_eq_mul_inv] using!
    he.differentiableAt.hasDerivAt.comp μ ha

lemma supercriticalEnergy_second_hasDerivAt {d : ℕ} (hd : 12 ≤ d) :
    ∀ᶠ μ in 𝓝[>] (1:ℝ), HasDerivAt (deriv (supercriticalEnergy hd))
      ((deriv (deriv (branchEnergy hd)) (amplitude hd μ)*deriv (parameter hd) (amplitude hd μ)-
        deriv (branchEnergy hd) (amplitude hd μ)*deriv (deriv (parameter hd)) (amplitude hd μ))/
        (deriv (parameter hd) (amplitude hd μ))^3) μ := by
  have hfirst : ∀ᶠ μ in 𝓝[>] (1:ℝ), deriv (supercriticalEnergy hd) μ =
      deriv (branchEnergy hd) (amplitude hd μ)/deriv (parameter hd) (amplitude hd μ) :=
    (supercriticalEnergy_hasDerivAt hd).mono (fun _ h => h.deriv)
  filter_upwards [eventually_local_right hfirst,amplitude_hasDerivAt hd,
    (amplitude_tendsto hd).eventually (branchEnergy_analytic hd).deriv.eventually_analyticAt,
    (amplitude_tendsto hd).eventually (parameter_analytic hd).deriv.eventually_analyticAt,
    (amplitude_tendsto hd).eventually (parameter_derivative_pos hd),self_mem_nhdsWithin,
    (gt_mem_nhds (upperParameter_gt_one hd)).filter_mono nhdsWithin_le_nhds]
    with μ hlocal ha he hp hpos hμ hupper
  have hne := (hpos (amplitude_pos hd hμ hupper.le)).ne'
  have hh := (he.differentiableAt.hasDerivAt.div hp.differentiableAt.hasDerivAt hne).comp μ ha
  have hs : HasDerivAt (fun x => deriv (branchEnergy hd) (amplitude hd x)/
      deriv (parameter hd) (amplitude hd x))
      ((deriv (deriv (branchEnergy hd)) (amplitude hd μ)*deriv (parameter hd) (amplitude hd μ)-
        deriv (branchEnergy hd) (amplitude hd μ)*deriv (deriv (parameter hd)) (amplitude hd μ))/
        (deriv (parameter hd) (amplitude hd μ))^3) μ := by
    convert! hh using 1
    field_simp
    <;> ring
  exact hs.congr_of_eventuallyEq hlocal

lemma amplitude_tendsto_right {d : ℕ} (hd : 12 ≤ d) :
    Tendsto (amplitude hd) (𝓝[>] (1:ℝ)) (𝓝[>] (0:ℝ)) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨amplitude_tendsto hd,?_⟩
  filter_upwards [self_mem_nhdsWithin,eventually_parameter_interval hd] with μ hμ hi
  exact amplitude_pos hd hμ hi.2

lemma supercriticalEnergy_second_derivative_limit {d : ℕ} (hd : 12 ≤ d) :
    Tendsto (deriv (deriv (supercriticalEnergy hd))) (𝓝[>] (1:ℝ)) (𝓝 ((d:ℝ)/kappa d)) := by
  have ht := (energy_parameter_second_derivative_limit hd).comp (amplitude_tendsto_right hd)
  apply ht.congr'
  filter_upwards [supercriticalEnergy_second_hasDerivAt hd] with μ hμ
  exact hμ.deriv.symm

#print axioms supercriticalEnergy_hasDerivAt
#print axioms supercriticalEnergy_second_hasDerivAt
#print axioms supercriticalEnergy_second_derivative_limit
end BecknerOnofri.HighDim.DiagonalScalarBranch
