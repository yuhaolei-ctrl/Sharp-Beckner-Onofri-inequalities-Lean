import BecknerOnofri.AnalyticLinearFactorUnique

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology
namespace BecknerOnofri.AnalyticParameterDivision
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem two_linear_factors_unique {g h : E → ℝ} {a e₁ e₂ : E}
    (L₁ L₂ : E →L[ℝ] ℝ) (he₁ : L₁ e₁=1) (he₂ : L₂ e₂=1)
    (ha₁ : L₁ a=0) (ha₂ : L₂ a=0) (hg : AnalyticAt ℝ g a) (hh : AnalyticAt ℝ h a)
    (hz : ∀ᶠ x in 𝓝 a,(L₁ x*L₂ x)*g x=(L₁ x*L₂ x)*h x) :
    g =ᶠ[𝓝 a] h := by
  apply linear_factor_unique L₂ he₂ ha₂ hg hh
  apply linear_factor_unique L₁ he₁ ha₁ ((L₂.analyticAt a).mul hg) ((L₂.analyticAt a).mul hh)
  simpa only [mul_assoc,Pi.mul_apply] using hz

#print axioms two_linear_factors_unique
end BecknerOnofri.AnalyticParameterDivision
