import Mathlib.Analysis.Convex.Slope
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-! The two-sign-change criterion used in the circle convex-order argument.
It works directly on an observable, so no arcsine change of variables is
needed for its later application to the actual cosine observable. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
namespace BecknerOnofri.HighDim.CircleScalar

theorem two_sign_change_convex_test {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (z g : X → ℝ) (φ : ℝ → ℝ) (a b : ℝ)
    (ha : a ∈ Icc (-1:ℝ) 1) (hb : b ∈ Icc (-1:ℝ) 1) (hab : a<b)
    (hφ : ConvexOn ℝ (Icc (-1:ℝ) 1) φ)
    (hz : ∀ᵐ x ∂μ,z x ∈ Icc (-1:ℝ) 1)
    (hinside : ∀ᵐ x ∂μ,a<z x → z x<b → g x≤0)
    (houtside : ∀ᵐ x ∂μ,z x<a ∨ b<z x → 0≤g x)
    (hi : Integrable g μ) (hzi : Integrable (fun x => z x*g x) μ)
    (hφi : Integrable (fun x => φ (z x)*g x) μ)
    (hmass : (∫ x,g x ∂μ)=0) (hmean : (∫ x,z x*g x ∂μ)=0) :
    0≤∫ x,φ (z x)*g x ∂μ := by
  let Q : ℝ → ℝ := fun y => (b-a)*φ y-((b-y)*φ a+(y-a)*φ b)
  have hQ : ∀ᵐ x ∂μ,0≤Q (z x)*g x := by
    filter_upwards [hz,hinside,houtside] with x hx hin hout
    rcases lt_trichotomy (z x) a with hxa | hxa | hax
    · have hsec := hφ.secant_mono_aux1 hx hb hxa hab
      exact mul_nonneg (by dsimp [Q]; nlinarith) (hout (Or.inl hxa))
    · simp [Q,hxa]
    · rcases lt_trichotomy (z x) b with hxb | hxb | hbx
      · have hsec := hφ.secant_mono_aux1 ha hb hax hxb
        exact mul_nonneg_of_nonpos_of_nonpos (by dsimp [Q]; nlinarith) (hin hax hxb)
      · simp [Q,hxb]
      · have hsec := hφ.secant_mono_aux1 ha hx hab hbx
        exact mul_nonneg (by dsimp [Q]; nlinarith) (hout (Or.inr hbx))
  have hnon := integral_nonneg_of_ae hQ
  have he : (fun x => Q (z x)*g x)=
      (fun x => (b-a)*(φ (z x)*g x)+(φ a-φ b)*(z x*g x)+(a*φ b-b*φ a)*g x) := by
    funext x
    dsimp [Q]
    ring
  rw [he,integral_add (f:=fun x => (b-a)*(φ (z x)*g x)+(φ a-φ b)*(z x*g x)) ((hφi.const_mul (b-a)).add (hzi.const_mul (φ a-φ b))) (hi.const_mul (a*φ b-b*φ a)),
    integral_add (hφi.const_mul (b-a)) (hzi.const_mul (φ a-φ b))] at hnon
  simp only [integral_const_mul,hmass,hmean,mul_zero,add_zero] at hnon
  exact nonneg_of_mul_nonneg_right hnon (sub_pos.mpr hab)

#print axioms two_sign_change_convex_test
end BecknerOnofri.HighDim.CircleScalar
