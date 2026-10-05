module

public import BecknerOnofri.SpinCandidateCertificate
public import BecknerOnofri.ScalarConvexMinorant

@[expose] public section

namespace BecknerOnofri.HighDim.Spin
open ScalarCertificate Set

def candidateIntervalCheck (c : RationalCandidate) (a b : ℚ) (p : AffinePiece) : Bool :=
  decide (0≤a ∧ a≤b ∧
    b^4/250≤c.functionalLower+c.eta*(a-c.s)-350*(a-c.s)^2-5*c.delta^2+
      12*(p.slope*a+p.intercept) ∧
    b^4/250≤c.functionalLower+c.eta*(b-c.s)-350*(b-c.s)^2-5*c.delta^2+
      12*(p.slope*b+p.intercept))

theorem candidateInterval_sound (c : RationalCandidate) (hc : c.check=true)
    (a b : ℚ) (p : AffinePiece) (hi : candidateIntervalCheck c a b p=true)
    (q : Count → ℝ) (t : ℝ) (hq : FeasibleAt t q) (ht : t∈Icc (a : ℝ) (b : ℝ)) :
    t^4/250≤functional q+12*p.value t := by
  obtain ⟨ha,hab,hl,hu⟩ := of_decide_eq_true hi
  have hpar := (c.sound hc).2 q t hq
  have hleft := (Rat.cast_le (K := ℝ)).mpr hl
  have hright := (Rat.cast_le (K := ℝ)).mpr hu
  push_cast at hleft hright
  have he (x : ℝ) :
      (c.functionalLower : ℝ)+(c.eta : ℝ)*(x-c.s)-350*(x-c.s)^2-5*(c.delta : ℝ)^2+
        12*((p.slope : ℝ)*x+p.intercept)=
      ((c.functionalLower : ℝ)-(c.eta : ℝ)*c.s-350*(c.s : ℝ)^2-5*(c.delta : ℝ)^2+
        12*(p.intercept : ℝ))+((c.eta : ℝ)+700*(c.s : ℝ)+12*(p.slope : ℝ))*x-350*x^2 := by ring
  rw [he] at hleft hright
  have h := concave_quadratic_interval _ _ 350 a b t ((b : ℝ)^4/250)
    (by norm_num) ht.1 ht.2 hleft hright
  rw [← he] at h
  have ht0 : 0≤t := (show (0 : ℝ)≤a by exact_mod_cast ha).trans ht.1
  have hpow := pow_le_pow_left₀ ht0 ht.2 4
  unfold AffinePiece.value
  linarith

structure CertifiedSpinCell (ψ : ℝ → ℝ) where
  left : ℚ
  right : ℚ
  sound : ∀ (q : Count → ℝ) (t : ℝ), FeasibleAt t q →
    t∈Icc (left : ℝ) (right : ℝ) → t^4/250≤functional q+12*ψ t

noncomputable def spinCellOfCandidate (ψ : ℝ → ℝ) (c : RationalCandidate)
    (hc : c.check=true) (a b : ℚ) (p : AffinePiece)
    (hi : candidateIntervalCheck c a b p=true) (hp : ∀ t,p.value t≤ψ t) :
    CertifiedSpinCell ψ where
  left := a
  right := b
  sound := by
    intro q t hq ht
    have h := candidateInterval_sound c hc a b p hi q t hq ht
    linarith [hp t]

#print axioms candidateInterval_sound
end BecknerOnofri.HighDim.Spin
