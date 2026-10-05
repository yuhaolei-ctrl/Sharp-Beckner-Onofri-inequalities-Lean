module

public import BecknerOnofri.SpinRationalMatrix
public import BecknerOnofri.EntropyCheckedLog

@[expose] public section

namespace BecknerOnofri.HighDim.Spin
open scoped BigOperators

structure RationalCandidate where
  p : Count → ℚ
  s : ℚ
  ell : ℚ
  eta : ℚ
  delta : ℚ
  functionalLower : ℚ
  logs : Count → EntropyLogCertificate.CheckedLog

def RationalCandidate.check (c : RationalCandidate) : Bool :=
  decide ((∀ j,0<c.p j) ∧ (∑ j : Count,c.p j)=1 ∧ c.p 0≤1/4096 ∧
    (∑ j : Count,meanCoordinateQ j*c.p j)=c.s ∧
    (∀ j,(c.logs j).value=c.p j/referenceQ j) ∧
    (∀ j,c.ell+c.eta*meanCoordinateQ j-c.delta≤fastGradientBound c.p (fun i => (c.logs i).lower) j) ∧
    (∀ j,fastGradientBound c.p (fun i => (c.logs i).upper) j≤c.ell+c.eta*meanCoordinateQ j+c.delta) ∧
    c.functionalLower≤fastFunctionalLower c.p (fun j => (c.logs j).lower))

theorem RationalCandidate.sound (c : RationalCandidate) (hc : c.check=true) :
    FeasibleAt (c.s : ℝ) (fun j => (c.p j : ℝ)) ∧
    ∀ (q : Count → ℝ) (t : ℝ), FeasibleAt t q →
      (c.functionalLower : ℝ)+(c.eta : ℝ)*(t-c.s)-350*(t-c.s)^2-5*(c.delta : ℝ)^2≤functional q := by
  have h := of_decide_eq_true hc
  obtain ⟨hp,hm,hcap,hmean,halign,hlo,hup,hF⟩ := h
  simp only [fastGradientBound_eq] at hlo hup
  rw [fastFunctionalLower_eq] at hF
  have hf := rational_feasible c.p c.s hp hm hcap hmean
  have hlog (j : Count) : ((c.logs j).lower : ℝ)≤Real.log ((c.p j : ℝ)/reference j) ∧
      Real.log ((c.p j : ℝ)/reference j)≤((c.logs j).upper : ℝ) := by
    have h := (c.logs j).sound
    rw [halign j] at h
    simpa only [Rat.cast_div, reference] using h
  refine ⟨hf,?_⟩
  intro q t hq
  have hg := rational_residual c.p (fun j => (c.logs j).lower) (fun j => (c.logs j).upper)
    c.ell c.eta c.delta hlog hlo hup
  have he := rational_functional_lower c.p (fun j => (c.logs j).lower)
    (fun j => (hp j).le) (fun j => (hlog j).1)
  have hl := (Rat.cast_le (K := ℝ)).mpr hF
  have hpar := global_supporting_parabola (fun j => (c.p j : ℝ)) q c.s t c.delta c.ell c.eta
    hf (fun j => by exact_mod_cast hp j) hq hg
  linarith

#print axioms RationalCandidate.sound
end BecknerOnofri.HighDim.Spin
