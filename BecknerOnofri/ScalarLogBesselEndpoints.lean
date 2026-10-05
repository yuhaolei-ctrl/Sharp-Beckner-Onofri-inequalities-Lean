module

public import BecknerOnofri.ScalarBesselPoint
public import BecknerOnofri.ScalarLogBesselEnclosure

@[expose] public section

namespace BecknerOnofri.HighDim.ScalarCertificate
open CircleScalar EntropyLogCertificate Set

def besselEndpointLogCheck (l u : BesselPoint) (ll uu : CheckedLog) : Bool :=
  decide (ll.value=(l.values 0).lower ∧ uu.value=(u.values 0).upper)

noncomputable def logBesselEndpoints (l u : BesselPoint) (ll uu : CheckedLog)
    (hc : besselEndpointLogCheck l u ll uu=true) :
    FunctionEnclosure l.argument u.argument (fun h => Real.log (bessel 0 h)) where
  value := ⟨ll.lower,uu.upper⟩
  slope := (⟨2,2⟩ : RationalInterval).mul (momentRange l u 1)
  value_mem := by
    obtain ⟨hll,huu⟩ := of_decide_eq_true hc
    intro x hx
    have hl0 : (0 : ℝ)≤l.argument := by exact_mod_cast l.nonneg
    have hx0 := hl0.trans hx.1
    have hu0 := hx0.trans hx.2
    have hlpos : (0 : ℝ)<(l.values 0).lower := by exact_mod_cast l.basepos
    have hupos : (0 : ℝ)<(u.values 0).lower := by exact_mod_cast u.basepos
    have hlo := ll.sound.1
    have hup := uu.sound.2
    rw [hll] at hlo
    rw [huu] at hup
    have hL := hlo.trans (Real.log_le_log hlpos (l.sound 0).1)
    have hU := (Real.log_le_log (hupos.trans_le (u.sound 0).1) (u.sound 0).2).trans hup
    exact ⟨hL.trans (logBessel_mono hl0 hx0 hx.1),
      (logBessel_mono hx0 hu0 hx.2).trans hU⟩
  slope_bounds := by
    apply slopeBounds_of_hasDerivAt
      (fun x _ => (log_bessel_derivative x).continuousAt.continuousWithinAt)
      (fun x _ => log_bessel_derivative x)
    intro x hx
    have h2 : (⟨2,2⟩ : RationalInterval).Contains (2 : ℝ) := by norm_num [RationalInterval.Contains]
    exact RationalInterval.contains_mul h2 (momentRange_sound l u 1 (Ioo_subset_Icc_self hx))

#print axioms logBesselEndpoints
end BecknerOnofri.HighDim.ScalarCertificate
