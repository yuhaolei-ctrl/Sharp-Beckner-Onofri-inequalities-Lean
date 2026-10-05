module

public import BecknerOnofri.SubspectralResolvent
public import Mathlib.Analysis.Calculus.ImplicitContDiff

@[expose] public section

/-! Banach implicit-function proof of local uniqueness below the spectral
threshold. This auxiliary version uses continuous potentials, with the
same Euler map and Fourier inverse as the manuscript's H^d argument. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology ContDiff
namespace BecknerOnofri.HighDim.SubspectralLocalUniqueness
open ContinuousGibbs ContinuousFirstShell ReducedEquation

lemma green_const {d : ℕ} (hd : 0 < d) (c : ℝ) :
    greenContinuous d (ContinuousMap.const (Torus d) c) = 0 := by
  apply coefficient_ext
  intro k
  rw [coefficient_green hd, coefficient_const, map_zero]
  by_cases hk : k = 0 <;> simp [hk]

lemma green_center {d : ℕ} (hd : 0 < d) (u : Space d) :
    greenContinuous d (center d u) = greenContinuous d u := by
  change greenContinuous d (u-ContinuousMap.const (Torus d) (mean d u)) = _
  rw [map_sub, green_const hd, sub_zero]

lemma full_analytic {d : ℕ} (μ : ℝ) (u : Space d) :
    AnalyticAt ℝ (fun x : ℝ × Space d => full d x.1 x.2) (μ,u) := by
  have hn : AnalyticAt ℝ (fun x : ℝ × Space d => normalized x.2) (μ,u) :=
    by
      have hh := (ContinuousGibbs.normalized_analytic u).comp
        ((ContinuousLinearMap.snd ℝ ℝ (Space d)).analyticAt (μ,u))
      convert! hh using 1
  have hr : AnalyticAt ℝ (fun x : ℝ × Space d => normalized x.2-1) (μ,u) :=
    hn.sub analyticAt_const
  have hg : AnalyticAt ℝ (fun x : ℝ × Space d => greenContinuous d (normalized x.2-1)) (μ,u) :=
    ((greenContinuous d).analyticAt _).comp hr
  exact analyticAt_snd.sub (analyticAt_fst.smul hg)

lemma full_derivative {d : ℕ} (hd : 0 < d) (μ : ℝ) :
    HasFDerivAt (fun x : ℝ × Space d => full d x.1 x.2)
      ((SubspectralResolvent.forward d μ).comp (ContinuousLinearMap.snd ℝ ℝ (Space d))) (μ,0) := by
  let P := ContinuousLinearMap.snd ℝ ℝ (Space d)
  let Q := ContinuousLinearMap.fst ℝ ℝ (Space d)
  have hn := (hasFDerivAt_normalized_zero d).comp (μ, (0:Space d)) P.hasFDerivAt
  have hg := (greenContinuous d).hasFDerivAt.comp (μ,(0:Space d)) (hn.sub_const 1)
  have hh := (P.hasFDerivAt (x := (μ,(0:Space d)))).sub
    ((Q.hasFDerivAt (x := (μ,(0:Space d)))).smul hg)
  convert! hh using 1
  apply ContinuousLinearMap.ext
  intro y
  simp [P, Q, SubspectralResolvent.forward, green_center hd]

lemma local_unique {d : ℕ} (hd : 0 < d) {μ₀ : ℝ} (hμ : 0 ≤ μ₀) (hμ1 : μ₀ < 1) :
    ∀ᶠ x : ℝ × Space d in 𝓝 (μ₀,0), full d x.1 x.2 = 0 → x.2 = 0 := by
  let F := fun x : ℝ × Space d => full d x.1 x.2
  let e := SubspectralResolvent.equivalence hd hμ hμ1
  have hf0 : F (μ₀,0) = 0 := by simp [F, full]
  have hfd := full_derivative hd μ₀
  have hpartial : (fderiv ℝ F (μ₀,0)).comp (ContinuousLinearMap.inr ℝ ℝ (Space d)) =
      (e : Space d →L[ℝ] Space d) := by
    rw [hfd.fderiv]
    ext u
    rfl
  have hinv : ((fderiv ℝ F (μ₀,0)).comp (ContinuousLinearMap.inr ℝ ℝ (Space d))).IsInvertible := by
    rw [hpartial]
    exact ContinuousLinearMap.isInvertible_equiv
  have hc : ContDiffAt ℝ ω F (μ₀,0) := (full_analytic μ₀ 0).contDiffAt
  have hn : (ω : ℕ∞ω) ≠ 0 := by simp
  let ψ := hc.implicitFunction hn hinv
  have huniq : ∀ᶠ x in 𝓝 (μ₀,(0:Space d)), F x = 0 ↔ ψ x.1 = x.2 := by
    simpa only [hf0] using hc.eventually_apply_eq_iff_implicitFunction hn hinv
  have hz : ∀ᶠ μ in 𝓝 μ₀, ψ μ = 0 := by
    have ht : Tendsto (fun μ : ℝ => (μ,(0:Space d))) (𝓝 μ₀) (𝓝 (μ₀,0)) :=
      (continuous_id.prodMk continuous_const).continuousAt
    filter_upwards [ht.eventually huniq] with μ hμ
    exact hμ.mp (by simp [F, full])
  filter_upwards [huniq, (continuous_fst.tendsto (μ₀,(0:Space d))).eventually hz] with x hx hz
  intro hf
  exact (hx.mp hf).symm.trans hz

#print axioms local_unique
end BecknerOnofri.HighDim.SubspectralLocalUniqueness
