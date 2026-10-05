import BecknerOnofri.Friedrichs.MixedProductDerivative
import BecknerOnofri.Friedrichs.SmoothCutoffApproximation

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace BecknerOnofri.Friedrichs.MixedSpatial

def scalarCutoff (m : ℕ) (δ : ℝ) : ℝ → ℝ := if m=0 then (fun _ => 1) else boundaryCutoff δ

lemma scalarCutoff_smooth (m : ℕ) (δ : ℝ) : ContDiff ℝ ∞ (scalarCutoff m δ) := by
  by_cases h : m=0
  · simp only [scalarCutoff,h,if_true]
    exact contDiff_const
  · simpa only [scalarCutoff,if_neg h] using boundaryCutoff_smooth δ

lemma scalarCutoff_mem (m : ℕ) (δ t : ℝ) : scalarCutoff m δ t∈Icc 0 1 := by
  unfold scalarCutoff
  split_ifs
  · exact ⟨zero_le_one,le_rfl⟩
  · exact boundaryCutoff_mem δ t

lemma scalarCutoff_deriv (m : ℕ) (δ t : ℝ) :
    deriv (scalarCutoff m δ) t=if m=0 then 0 else deriv (boundaryCutoff δ) t := by
  by_cases h : m=0 <;> simp only [scalarCutoff,h,if_true,if_false,deriv_const]

lemma scalarCutoff_eventually {m : ℕ} {t : ℝ} (ht : m≠0 → t∈Ioo 0 Real.pi) :
    ∀ᶠ δ : ℝ in 𝓝[>] 0,scalarCutoff m δ t=1 ∧ deriv (scalarCutoff m δ) t=0 := by
  by_cases h : m=0
  · simp only [scalarCutoff,h,if_true,deriv_const,and_self,eventually_const]
  · filter_upwards [boundaryCutoff_eventually_one (ht h)] with δ hδ
    simpa only [scalarCutoff,if_neg h] using hδ

lemma scalarCutoff_product_smooth (m : ℕ) {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (δ : ℝ) :
    ContDiff ℝ ∞ (fun t => scalarCutoff m δ t*f t) := (scalarCutoff_smooth m δ).mul hf

lemma scalarCutoff_product_deriv (m : ℕ) {f : ℝ → ℝ} (hf : Differentiable ℝ f) (δ t : ℝ) :
    deriv (fun t => scalarCutoff m δ t*f t) t=
      deriv (scalarCutoff m δ) t*f t+scalarCutoff m δ t*deriv f t :=
  deriv_mul ((scalarCutoff_smooth m δ).differentiable (by simp) t) (hf t)

lemma scalarCutoff_derivative_bound (m : ℕ) {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hend : m≠0 → f 0=0 ∧ f Real.pi=0) :
    ∃ B : ℝ,0≤B ∧ ∀ δ,0<δ → ∀ t,(m≠0 → t∈Ioo 0 Real.pi) →
      |deriv (scalarCutoff m δ) t*f t|≤B := by
  by_cases hm : m=0
  · refine ⟨0,le_rfl,?_⟩
    intro δ hδ t ht
    simp only [scalarCutoff_deriv,hm,if_true,zero_mul,abs_zero,le_refl]
  · obtain ⟨C,hC,hCb⟩ := boundaryCutoff_deriv_bound
    obtain ⟨L,hL,hLd,hLend⟩ := smooth_endpoint_bound hf (hend hm).1 (hend hm).2
    refine ⟨2*C*L,by positivity,?_⟩
    intro δ hδ t ht
    rw [scalarCutoff_deriv,if_neg hm]
    exact cutoff_derivative_times_vanishing_bound hC hL hδ (ht hm) (hCb δ hδ t)
      (hLend t (ht hm)).1 (hLend t (ht hm)).2

#print axioms scalarCutoff_derivative_bound
end BecknerOnofri.Friedrichs.MixedSpatial
