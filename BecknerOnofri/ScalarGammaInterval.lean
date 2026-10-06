module

public import BecknerOnofri.ScalarCandidateEnclosure
public import BecknerOnofri.ScalarMomentFunctionEnclosure
public import BecknerOnofri.ScalarCheckedWeight
public import BecknerOnofri.CircleRateLower
public import BecknerOnofri.SpinBinaryCost

@[expose] public section

noncomputable section
namespace BecknerOnofri.HighDim.ScalarCertificate
open CircleScalar Set

/-- The source's gamma written in the Bessel parameter rather than the mean. -/
def gammaAt (h : ℝ) : ℝ :=
  let t := besselMoment 1 h
  (33/100)*rateAt h+(67/100)*t^2-2*Spin.binaryCost t+
    candidateMinimum (157/500) ((67/100)*weight 1 t) ((67/100)*weight 2 t)
      (6-t) (6*besselMoment 2 h-besselMoment 3 h) (t^2) (besselMoment 2 h)

def gammaBaseAt (h : ℝ) : ℝ :=
  (33/100)*rateAt h+(67/100)*(besselMoment 1 h)^2-2*Spin.binaryCost (besselMoment 1 h)

theorem gammaAt_parameter {t : ℝ} (ht : 0≤t) (ht1 : t<1) :
    gammaAt (parameter t)=gamma t := by
  simp only [gammaAt,rateAt,gamma,rate,(parameter_mean ht ht1).1]

theorem gammaBaseAt_derivative (h : ℝ) (ht : -1<besselMoment 1 h)
    (ht1 : besselMoment 1 h<1) :
    HasDerivAt gammaBaseAt
      ((besselMoment 0 h+besselMoment 2 h-2*besselMoment 1 h*besselMoment 1 h)*
        ((13/20)*h+(27/20)*besselMoment 1 h-
          Real.log (1+besselMoment 1 h)+Real.log (1-besselMoment 1 h))) h := by
  have hm := besselMoment_derivative 1 (by omega) h
  norm_num only [Nat.sub_self,Nat.reduceAdd] at hm
  have hi : HasDerivAt rateAt
      (2*h*(besselMoment 0 h+besselMoment 2 h-2*besselMoment 1 h*besselMoment 1 h)) h := by
    have he := (((hasDerivAt_id h).const_mul 2).mul hm).sub (log_bessel_derivative h)
    convert he using 1 <;> try rfl
    simp only [id_eq]
    ring
  have he := ((hi.const_mul (33/100)).add ((hm.pow 2).const_mul (67/100))).sub
    (((Spin.binaryCost_derivative (besselMoment 1 h) ht ht1).comp h hm).const_mul 2)
  convert he using 1 <;> try rfl
  dsimp [Spin.binaryCostSlope]
  ring

/-- The midpoint error estimate applies to the real gamma at every mean
whose inverse parameter lies in the certified interval. -/
theorem gamma_lower_from_parameter_interval {a b c l u L t : ℝ}
    (hc : c∈Icc a b) (hs : SlopeBounds (Icc a b) gammaAt l u)
    (hL : L≤gammaAt c) (ht : 0≤t) (ht1 : t<1)
    (hp : parameter t∈Icc a b) :
    L-max |l| |u| * max (c-a) (b-c)≤gamma t := by
  have h := hs.lower_from_point hc hL (parameter t) hp
  rwa [gammaAt_parameter ht ht1] at h

#print axioms gammaBaseAt_derivative
#print axioms gamma_lower_from_parameter_interval
end BecknerOnofri.HighDim.ScalarCertificate
