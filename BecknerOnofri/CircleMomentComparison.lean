module

public import BecknerOnofri.CircleMomentPolynomials

@[expose] public section

/-! The exact second- and third-moment comparisons from the manuscript,
now applied to the actual two circle densities, not assumed moments. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
namespace BecknerOnofri.HighDim.CircleScalar

theorem circle_moment_pair_bound (F : ℝ → ℝ) (t a b : ℝ)
    (hcF : Continuous F) (hF : ConvexOn ℝ (Icc (-1:ℝ) 1) F)
    (hmass : (∫ x : UnitAddCircle,Real.exp (F ((fourier 1 x).re)) ∂AddCircle.haarAddCircle)=1)
    (hm : (∫ x : UnitAddCircle,Real.exp (F ((fourier 1 x).re))*(fourier 1 x).re
      ∂AddCircle.haarAddCircle)=t) (ht : 0≤t) (ht1 : t<1) (hab : 6*|b|≤a) :
    0≤a*((∫ x : UnitAddCircle,Real.exp (F ((fourier 1 x).re))*(fourier 2 x).re
      ∂AddCircle.haarAddCircle)-besselMoment 2 (parameter t))+
      b*((∫ x : UnitAddCircle,Real.exp (F ((fourier 1 x).re))*(fourier 3 x).re
      ∂AddCircle.haarAddCircle)-besselMoment 3 (parameter t)) := by
  let p : UnitAddCircle → ℝ := fun x => Real.exp (F ((fourier 1 x).re))
  let q := circleTiltDensity (parameter t)
  let v : ℕ → UnitAddCircle → ℝ := fun n x => p x*(fourier (n:ℤ) x).re-q x*(fourier (n:ℤ) x).re
  have hcp : Continuous p := Real.continuous_exp.comp (hcF.comp (Complex.continuous_re.comp (fourier 1).continuous))
  have hcq : Continuous q := vonMises_continuous (parameter t)
  have hci {f : UnitAddCircle → ℝ} (hf : Continuous f) : Integrable f AddCircle.haarAddCircle :=
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi (n : ℕ) : Integrable (v n) AddCircle.haarAddCircle :=
    hci ((hcp.mul (Complex.continuous_re.comp (fourier (n:ℤ)).continuous)).sub
      (hcq.mul (Complex.continuous_re.comp (fourier (n:ℤ)).continuous)))
  have hint (n : ℕ) : (∫ x,v n x ∂AddCircle.haarAddCircle)=
      (∫ x,p x*(fourier (n:ℤ) x).re ∂AddCircle.haarAddCircle)-besselMoment n (parameter t) := by
    rw [integral_sub (f:=fun x => p x*(fourier (n:ℤ) x).re)
      (g:=fun x => q x*(fourier (n:ℤ) x).re)
      (hci (hcp.mul (Complex.continuous_re.comp (fourier (n:ℤ)).continuous)))
      (hci (hcq.mul (Complex.continuous_re.comp (fourier (n:ℤ)).continuous))),vonMises_moment]
  have htest := circle_vonMises_convex_test F (fun y => a*secondPolynomial y+b*thirdPolynomial y) t
    hcF hF (by unfold secondPolynomial thirdPolynomial; fun_prop)
    (moment_polynomial_convex a b hab) hmass hm ht ht1
  have he : (fun x : UnitAddCircle => (a*secondPolynomial ((fourier 1 x).re)+
      b*thirdPolynomial ((fourier 1 x).re))*(p x-q x))=(fun x => a*v 2 x+b*v 3 x) := by
    funext x
    rw [second_polynomial_cosine,third_polynomial_cosine]
    dsimp only [v]
    norm_num only [Nat.cast_ofNat]
    ring
  change 0≤∫ x,(a*secondPolynomial ((fourier 1 x).re)+b*thirdPolynomial ((fourier 1 x).re))*(p x-q x)
    ∂AddCircle.haarAddCircle at htest
  rw [he,integral_add ((hi 2).const_mul a) ((hi 3).const_mul b),integral_const_mul,integral_const_mul,
    hint,hint] at htest
  exact htest

theorem circle_second_third_comparison (F : ℝ → ℝ) (t : ℝ)
    (hcF : Continuous F) (hF : ConvexOn ℝ (Icc (-1:ℝ) 1) F)
    (hmass : (∫ x : UnitAddCircle,Real.exp (F ((fourier 1 x).re)) ∂AddCircle.haarAddCircle)=1)
    (hm : (∫ x : UnitAddCircle,Real.exp (F ((fourier 1 x).re))*(fourier 1 x).re
      ∂AddCircle.haarAddCircle)=t) (ht : 0≤t) (ht1 : t<1) :
    besselMoment 2 (parameter t)≤
      (∫ x : UnitAddCircle,Real.exp (F ((fourier 1 x).re))*(fourier 2 x).re ∂AddCircle.haarAddCircle) ∧
    |(∫ x : UnitAddCircle,Real.exp (F ((fourier 1 x).re))*(fourier 3 x).re ∂AddCircle.haarAddCircle)-
      besselMoment 3 (parameter t)|≤
      6*((∫ x : UnitAddCircle,Real.exp (F ((fourier 1 x).re))*(fourier 2 x).re ∂AddCircle.haarAddCircle)-
        besselMoment 2 (parameter t)) := by
  have h0 := circle_moment_pair_bound F t 1 0 hcF hF hmass hm ht ht1 (by norm_num)
  have hp := circle_moment_pair_bound F t 6 1 hcF hF hmass hm ht ht1 (by norm_num)
  have hn := circle_moment_pair_bound F t 6 (-1) hcF hF hmass hm ht ht1 (by norm_num)
  constructor
  · linarith
  · exact abs_le.mpr ⟨by linarith,by linarith⟩

#print axioms circle_second_third_comparison
end BecknerOnofri.HighDim.CircleScalar
