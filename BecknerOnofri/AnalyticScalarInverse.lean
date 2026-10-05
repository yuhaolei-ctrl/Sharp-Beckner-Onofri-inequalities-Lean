module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
public import Mathlib.Analysis.Calculus.FDeriv.Analytic

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology ContDiff
namespace BecknerOnofri

theorem exists_analytic_scalar_inverse {f : ℝ → ℝ} {c : ℝ}
    (hf : AnalyticAt ℝ f 0) (hf0 : f 0=0) (hd : HasDerivAt f c 0) (hc : c≠0) :
    ∃ g : ℝ → ℝ, AnalyticAt ℝ g 0 ∧ g 0=0 ∧ HasDerivAt g c⁻¹ 0 ∧
      (∀ᶠ t in 𝓝 (0:ℝ),g (f t)=t) ∧ (∀ᶠ t in 𝓝 (0:ℝ),f (g t)=t) := by
  have ha : ContDiffAt ℝ ω f 0 := hf.contDiffAt
  have hn : (ω : ℕ∞ω)≠0 := by simp
  let H := hd.hasFDerivAt_equiv hc
  let g := ha.localInverse H hn
  have hstrict := ha.hasStrictDerivAt' hd hn
  have hg : AnalyticAt ℝ g 0 := by
    simpa only [hf0] using (ha.to_localInverse H hn).analyticAt
  have hg0 : g 0=0 := by
    simpa only [hf0] using ha.localInverse_apply_image H hn
  have hl : ∀ᶠ t in 𝓝 (0:ℝ),g (f t)=t :=
    (ha.hasStrictFDerivAt' H hn).eventually_left_inverse
  have hr : ∀ᶠ t in 𝓝 (0:ℝ),f (g t)=t := by
    have hr' : ∀ᶠ t in 𝓝 (f 0),f (g t)=t :=
      (ha.hasStrictFDerivAt' H hn).eventually_right_inverse
    rwa [hf0] at hr'
  have hgd : HasDerivAt g c⁻¹ 0 := by
    simpa only [hf0] using (hstrict.to_local_left_inverse hc hl).hasDerivAt
  exact ⟨g,hg,hg0,hgd,hl,hr⟩

#print axioms exists_analytic_scalar_inverse
end BecknerOnofri
