import BecknerOnofri.CircleLogConvexOrder
import BecknerOnofri.CircleVonMisesMoments

/-! Actual convex-order comparison for circle densities exp(F(cos θ)).
Both comparison densities and their matching moments are genuine integrals. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
namespace BecknerOnofri.HighDim.CircleScalar

theorem circle_vonMises_convex_test (F φ : ℝ → ℝ) (t : ℝ)
    (hcF : Continuous F) (hF : ConvexOn ℝ (Icc (-1:ℝ) 1) F)
    (hcφ : Continuous φ) (hφ : ConvexOn ℝ (Icc (-1:ℝ) 1) φ)
    (hmass : (∫ x : UnitAddCircle,Real.exp (F ((fourier 1 x).re)) ∂AddCircle.haarAddCircle)=1)
    (hm : (∫ x : UnitAddCircle,Real.exp (F ((fourier 1 x).re))*(fourier 1 x).re
      ∂AddCircle.haarAddCircle)=t) (ht : 0≤t) (ht1 : t<1) :
    0≤∫ x : UnitAddCircle,φ ((fourier 1 x).re)*
      (Real.exp (F ((fourier 1 x).re))-circleTiltDensity (parameter t) x) ∂AddCircle.haarAddCircle := by
  let z : UnitAddCircle → ℝ := fun x => (fourier 1 x).re
  let p : UnitAddCircle → ℝ := fun x => Real.exp (F (z x))
  let q := circleTiltDensity (parameter t)
  let g : UnitAddCircle → ℝ := fun x => p x-q x
  let R : ℝ → ℝ := fun y => F y-2*parameter t*y+Real.log (besselI0Two (parameter t))
  have hcz : Continuous z := Complex.continuous_re.comp (fourier 1).continuous
  have hcp : Continuous p := Real.continuous_exp.comp (hcF.comp hcz)
  have hcq : Continuous q := vonMises_continuous (parameter t)
  have hcg : Continuous g := hcp.sub hcq
  have hci {f : UnitAddCircle → ℝ} (hf : Continuous f) : Integrable f AddCircle.haarAddCircle :=
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hz : ∀ᵐ x ∂AddCircle.haarAddCircle,z x ∈ Icc (-1:ℝ) 1 := by
    apply Filter.Eventually.of_forall
    intro x
    have hb : |z x|≤1 := (Complex.abs_re_le_norm _).trans_eq (by simp [fourier_apply])
    exact abs_le.mp hb
  have hcR : Continuous R := by dsimp [R]; fun_prop
  have hR : ConvexOn ℝ (Icc (-1:ℝ) 1) R := by
    refine ⟨convex_Icc _ _,?_⟩
    intro x hx y hy a b ha hb hab
    have he := hF.2 hx hy ha hb hab
    simp only [smul_eq_mul] at he ⊢
    dsimp only [R]
    nlinarith [congrArg (fun v : ℝ => v*Real.log (besselI0Two (parameter t))) hab]
  have hg : ∀ᵐ x ∂AddCircle.haarAddCircle,g x=q x*(Real.exp (R (z x))-1) := by
    apply Filter.Eventually.of_forall
    intro x
    change Real.exp (F (z x))-Real.exp (2*parameter t*z x)/besselI0Two (parameter t)=
      (Real.exp (2*parameter t*z x)/besselI0Two (parameter t))*
        (Real.exp (F (z x)-2*parameter t*z x+Real.log (besselI0Two (parameter t)))-1)
    rw [Real.exp_add,Real.exp_sub,Real.exp_log (besselI0Two_pos (parameter t))]
    field_simp [(besselI0Two_pos (parameter t)).ne',Real.exp_ne_zero]
    <;> ring
  have hg0 : (∫ x,g x ∂AddCircle.haarAddCircle)=0 := by
    rw [integral_sub (hci hcp) (hci hcq)]
    change (∫ x,Real.exp (F ((fourier 1 x).re)) ∂AddCircle.haarAddCircle)-
      (∫ x,circleTiltDensity (parameter t) x ∂AddCircle.haarAddCircle)=0
    rw [hmass,circleTiltDensity_integral,sub_self]
  have hg1 : (∫ x,z x*g x ∂AddCircle.haarAddCircle)=0 := by
    have he : (fun x => z x*g x)=(fun x => p x*z x-q x*z x) := by funext x; dsimp [g]; ring
    rw [he,integral_sub (f:=fun x => p x*z x) (g:=fun x => q x*z x) (hci (hcp.mul hcz)) (hci (hcq.mul hcz))]
    change (∫ x,Real.exp (F ((fourier 1 x).re))*(fourier 1 x).re ∂AddCircle.haarAddCircle)-
      (∫ x,circleTiltDensity (parameter t) x*(fourier 1 x).re ∂AddCircle.haarAddCircle)=0
    rw [hm,show (1:ℤ)=(1:ℕ) by rfl,vonMises_moment,(parameter_mean ht ht1).1,sub_self]
  exact log_convex_order AddCircle.haarAddCircle z q g R φ hcR hR hφ hz
    (Filter.Eventually.of_forall (fun x => (circleTiltDensity_pos (parameter t) x).le)) hg
    (hci hcg) (hci (hcz.mul hcg)) (hci ((hcφ.comp hcz).mul hcg)) hg0 hg1

#print axioms circle_vonMises_convex_test
end BecknerOnofri.HighDim.CircleScalar
