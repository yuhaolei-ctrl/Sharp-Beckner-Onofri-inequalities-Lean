import BecknerOnofri.SpinIntervalCertificate

/-! Rational interfaces for the manuscript's spin candidates. The only
transcendental input is a checked enclosure of each actual log(p_j / μ_j).
Feasibility, residuals and interval margins are exact rational inequalities. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace BecknerOnofri.HighDim.Spin

def rationalFunctionalLower (p L : Count → ℚ) : ℚ :=
  2*(∑ j : Count,p j*L j)-quadraticQ p

def rationalGradientBound (p L : Count → ℚ) (j : Count) : ℚ :=
  2*L j+2-2*(∑ k : Count,interactionQ j k*p k)

theorem rational_feasible (p : Count → ℚ) (s : ℚ)
    (hp : ∀ j,0<p j) (hm : (∑ j : Count,p j)=1)
    (hc : p 0≤1/4096) (hs : (∑ j : Count,meanCoordinateQ j*p j)=s) :
    FeasibleAt (s : ℝ) (fun j => (p j : ℝ)) := by
  refine ⟨⟨fun j => ?_, ?_, ?_⟩, ?_⟩
  · change (0 : ℝ)≤(p j : ℝ)
    exact_mod_cast (hp j).le
  · change (∑ j : Count,(p j : ℝ))=1
    exact_mod_cast hm
  · change (p 0 : ℝ)≤1/4096
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr hc
  · simpa only [mean, meanCoordinate, Rat.cast_sum, Rat.cast_mul] using
      congrArg (fun x : ℚ => (x : ℝ)) hs

theorem rational_functional_lower (p L : Count → ℚ) (hp : ∀ j,0≤p j)
    (hlog : ∀ j,(L j : ℝ)≤Real.log ((p j : ℝ)/reference j)) :
    (rationalFunctionalLower p L : ℝ)≤functional (fun j => (p j : ℝ)) := by
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
    mul_le_mul_of_nonneg_left (hlog j) (show (0 : ℝ)≤(p j : ℝ) from by exact_mod_cast hp j))
  simp only [functional, relativeEntropy, quadratic_cast]
  push_cast [rationalFunctionalLower]
  linarith

theorem rational_gradient_bounds (p L U : Count → ℚ)
    (hlog : ∀ j,(L j : ℝ)≤Real.log ((p j : ℝ)/reference j) ∧
      Real.log ((p j : ℝ)/reference j)≤(U j : ℝ)) (j : Count) :
    (rationalGradientBound p L j : ℝ)≤gradient (fun j => (p j : ℝ)) j ∧
      gradient (fun j => (p j : ℝ)) j≤(rationalGradientBound p U j : ℝ) := by
  simp only [rationalGradientBound, gradient, interaction]
  push_cast
  constructor <;> linarith [(hlog j).1, (hlog j).2]

theorem rational_residual (p L U : Count → ℚ) (ell η δ : ℚ)
    (hlog : ∀ j,(L j : ℝ)≤Real.log ((p j : ℝ)/reference j) ∧
      Real.log ((p j : ℝ)/reference j)≤(U j : ℝ))
    (hl : ∀ j,ell+η*meanCoordinateQ j-δ≤rationalGradientBound p L j)
    (hu : ∀ j,rationalGradientBound p U j≤ell+η*meanCoordinateQ j+δ) :
    ∀ j,|gradient (fun j => (p j : ℝ)) j-(ell : ℝ)-(η : ℝ)*meanCoordinate j|≤(δ : ℝ) := by
  intro j
  have h := rational_gradient_bounds p L U hlog j
  have h1 : (ell : ℝ)+(η : ℝ)*meanCoordinate j-(δ : ℝ)≤(rationalGradientBound p L j : ℝ) := by
    unfold meanCoordinate
    exact_mod_cast hl j
  have h2 : (rationalGradientBound p U j : ℝ)≤(ell : ℝ)+(η : ℝ)*meanCoordinate j+(δ : ℝ) := by
    unfold meanCoordinate
    exact_mod_cast hu j
  apply abs_le.mpr
  constructor <;> linarith [h.1,h.2]

theorem rational_interval_certificate
    (p L U : Count → ℚ) (a b s δ ell η α β κ : ℚ)
    (hp : ∀ j,0<p j) (hm : (∑ j : Count,p j)=1)
    (hc : p 0≤1/4096) (hs : (∑ j : Count,meanCoordinateQ j*p j)=s)
    (hlog : ∀ j,(L j : ℝ)≤Real.log ((p j : ℝ)/reference j) ∧
      Real.log ((p j : ℝ)/reference j)≤(U j : ℝ))
    (hl : ∀ j,ell+η*meanCoordinateQ j-δ≤rationalGradientBound p L j)
    (hu : ∀ j,rationalGradientBound p U j≤ell+η*meanCoordinateQ j+δ)
    (ha0 : 0≤a) (hκ : 0≤κ)
    (hleft : κ*b^4≤rationalFunctionalLower p L+η*(a-s)-350*(a-s)^2-5*δ^2+12*(α*a+β))
    (hright : κ*b^4≤rationalFunctionalLower p L+η*(b-s)-350*(b-s)^2-5*δ^2+12*(α*b+β))
    (q : Count → ℝ) (t : ℝ) (hq : FeasibleAt t q) (ha : (a : ℝ)≤t) (hb : t≤(b : ℝ)) :
    (κ : ℝ)*t^4≤functional q+12*((α : ℝ)*t+(β : ℝ)) := by
  have hf := rational_functional_lower p L (fun j => (hp j).le) (fun j => (hlog j).1)
  apply spin_interval_certificate (fun j => (p j : ℝ)) q a b s t δ ell η α β κ
    (rational_feasible p s hp hm hc hs) (fun j => by exact_mod_cast hp j) hq
    (rational_residual p L U ell η δ hlog hl hu)
    (by exact_mod_cast ha0) ha hb (by exact_mod_cast hκ)
  · have h := (Rat.cast_le (K := ℝ)).mpr hleft
    push_cast at h
    linarith
  · have h := (Rat.cast_le (K := ℝ)).mpr hright
    push_cast at h
    linarith

#print axioms rational_interval_certificate
end BecknerOnofri.HighDim.Spin
