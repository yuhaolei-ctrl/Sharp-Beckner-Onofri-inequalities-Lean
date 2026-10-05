import BecknerOnofri.SpinSupportingParabola

/-! Soundness of the manuscript's interval certificates. A candidate's exact
mass, mean, positivity and residual bound give a lower bound for every
feasible law throughout the interval, not merely at sample points. -/
noncomputable section
open scoped BigOperators
namespace BecknerOnofri.HighDim.Spin

theorem concave_quadratic_interval (C D K a b t L : ℝ)
    (hK : 0≤K) (ha : a≤t) (hb : t≤b)
    (hleft : L≤C+D*a-K*a^2) (hright : L≤C+D*b-K*b^2) :
    L≤C+D*t-K*t^2 := by
  by_cases hab : a=b
  · have ht : t=a := by linarith
    simpa [ht] using hleft
  have habpos : 0<b-a := by
    by_contra hn
    apply hab
    linarith
  let θ := (t-a)/(b-a)
  have hθ : 0≤θ := div_nonneg (by linarith) habpos.le
  have hθ1 : θ≤1 := (div_le_one habpos).mpr (by linarith)
  have he : C+D*t-K*t^2=(1-θ)*(C+D*a-K*a^2)+θ*(C+D*b-K*b^2)+K*(t-a)*(b-t) := by
    dsimp [θ]
    field_simp
    <;> ring
  rw [he]
  have h1 := mul_le_mul_of_nonneg_left hleft (by linarith : 0≤1-θ)
  have h2 := mul_le_mul_of_nonneg_left hright hθ
  have h3 := mul_nonneg (mul_nonneg hK (sub_nonneg.mpr ha)) (sub_nonneg.mpr hb)
  nlinarith

/-- One source mesh cell, with the exact fourth power of its right endpoint
in the endpoint checks. No optimality of the input candidate is needed. -/
theorem spin_interval_certificate (p q : Count → ℝ) (a b s t δ ell η α β κ : ℝ)
    (hp : FeasibleAt s p) (hpos : ∀ j,0<p j) (hq : FeasibleAt t q)
    (hδ : ∀ j,|gradient p j-ell-η*meanCoordinate j|≤δ)
    (ha0 : 0≤a) (ha : a≤t) (hb : t≤b) (hκ : 0≤κ)
    (hleft : κ*b^4≤functional p+η*(a-s)-350*(a-s)^2-5*δ^2+12*(α*a+β))
    (hright : κ*b^4≤functional p+η*(b-s)-350*(b-s)^2-5*δ^2+12*(α*b+β)) :
    κ*t^4≤functional q+12*(α*t+β) := by
  have hsupport := global_supporting_parabola p q s t δ ell η hp hpos hq hδ
  have he (x : ℝ) : functional p+η*(x-s)-350*(x-s)^2-5*δ^2+12*(α*x+β)=
      (functional p-η*s-350*s^2-5*δ^2+12*β)+(η+700*s+12*α)*x-350*x^2 := by ring
  rw [he] at hleft hright
  have hi := concave_quadratic_interval _ _ 350 a b t (κ*b^4) (by norm_num) ha hb hleft hright
  rw [← he] at hi
  have ht0 : 0≤t := ha0.trans ha
  have ht4 : t^4≤b^4 := pow_le_pow_left₀ ht0 hb 4
  have hc := mul_le_mul_of_nonneg_left ht4 hκ
  linarith

#print axioms spin_interval_certificate
end BecknerOnofri.HighDim.Spin
