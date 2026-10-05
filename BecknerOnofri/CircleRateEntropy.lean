import BecknerOnofri.CircleBesselInverse
import Legacy.TorusEndpoint.EntropyVariational

/-! The actual Gibbs variational step in the circle comparison: every
finite-entropy density with first cosine moment t has entropy at least I(t). -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
namespace BecknerOnofri.HighDim.CircleScalar

theorem rate_le_circle_entropy (p : UnitAddCircle → ℝ) (t : ℝ)
    (hp : ∀ᵐ x ∂AddCircle.haarAddCircle,0≤p x)
    (hmass : (∫ x,p x ∂AddCircle.haarAddCircle)=1)
    (hi : Integrable p AddCircle.haarAddCircle)
    (hent : Integrable (fun x => p x*Real.log (p x)) AddCircle.haarAddCircle)
    (hm : (∫ x,p x*(fourier 1 x).re ∂AddCircle.haarAddCircle)=t) :
    rate t≤∫ x,p x*Real.log (p x) ∂AddCircle.haarAddCircle := by
  let v : UnitAddCircle → ℝ := fun x => 2*parameter t*(fourier 1 x).re
  have hv : Continuous v := by dsimp [v]; fun_prop
  have hb : ∀ᵐ x ∂AddCircle.haarAddCircle,‖v x‖≤‖2*parameter t‖ := by
    apply Filter.Eventually.of_forall
    intro x
    have hc : ‖(fourier 1 x).re‖≤1 := by
      rw [Real.norm_eq_abs]
      exact (Complex.abs_re_le_norm _).trans_eq (by simp [fourier_apply])
    change ‖(2*parameter t)*(fourier 1 x).re‖≤‖2*parameter t‖
    rw [norm_mul]
    simpa using mul_le_mul_of_nonneg_left hc (norm_nonneg (2*parameter t))
  have hg := Legacy.TorusEndpoint.entropy_variational_bounded hp hmass hi hent hv.measurable hb
  have hpair : (∫ x,p x*v x ∂AddCircle.haarAddCircle)=2*parameter t*t := by
    calc
      _ =∫ x,(2*parameter t)*(p x*(fourier 1 x).re) ∂AddCircle.haarAddCircle := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun x => by dsimp [v]; ring)
      _ =_ := by rw [integral_const_mul,hm]
  have hpart : (∫ x,Real.exp (v x) ∂AddCircle.haarAddCircle)=bessel 0 (parameter t) := by
    rw [bessel_zero_eq,besselI0Two_eq_circle_integral]
    rfl
  rw [hpair,hpart] at hg
  exact hg

#print axioms rate_le_circle_entropy
end BecknerOnofri.HighDim.CircleScalar
