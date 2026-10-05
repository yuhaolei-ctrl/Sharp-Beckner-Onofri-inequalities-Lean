module

public import BecknerOnofri.ScalarMomentFunctionEnclosure
public import BecknerOnofri.ScalarCompositionEnclosure
public import BecknerOnofri.CircleRateLower

@[expose] public section

namespace BecknerOnofri.HighDim.ScalarCertificate
open CircleScalar EntropyLogCertificate Set

structure CheckedLogBessel where
  argument : ℚ
  value : RationalInterval
  sound : value.Contains (Real.log (bessel 0 (argument : ℝ)))

def logBesselCheck (c : CheckedBessel) (l u : CheckedLog) : Bool :=
  decide (c.order=0 ∧ 0<c.value.lower ∧ l.value=c.value.lower ∧ u.value=c.value.upper)

def checkedLogBessel (c : CheckedBessel) (l u : CheckedLog)
    (hc : logBesselCheck c l u=true) : CheckedLogBessel where
  argument := c.argument
  value := ⟨l.lower,u.upper⟩
  sound := by
    obtain ⟨hn,hp,hl,hu⟩ := of_decide_eq_true hc
    have hlo := l.sound.1
    have hup := u.sound.2
    rw [hl] at hlo
    rw [hu] at hup
    have hb := c.sound
    rw [hn] at hb
    have hpR : (0 : ℝ)<c.value.lower := by exact_mod_cast hp
    have hpB := hpR.trans_le hb.1
    exact ⟨hlo.trans (Real.log_le_log hpR hb.1),(Real.log_le_log hpB hb.2).trans hup⟩

theorem logBessel_mono : MonotoneOn (fun h => Real.log (bessel 0 h)) (Ici 0) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
    (fun x _ => (log_bessel_derivative x).continuousAt.continuousWithinAt)
    (fun x _ => (log_bessel_derivative x).hasDerivWithinAt)
  intro x hx
  have hx0 : 0≤x := interior_subset hx
  exact mul_nonneg (by norm_num) (besselMoment_nonneg 1 hx0)

noncomputable def logBesselFunctionEnclosure (l u : CheckedLogBessel)
    (hpos : 0≤l.argument) (t : RationalInterval)
    (ht : ∀ x∈Icc (l.argument : ℝ) (u.argument : ℝ),t.Contains (besselMoment 1 x)) :
    FunctionEnclosure l.argument u.argument (fun h => Real.log (bessel 0 h)) where
  value := ⟨l.value.lower,u.value.upper⟩
  slope := (⟨2,2⟩ : RationalInterval).mul t
  value_mem := by
    intro x hx
    have hl0 : (0 : ℝ)≤l.argument := by exact_mod_cast hpos
    have hx0 := hl0.trans hx.1
    have hu0 := hx0.trans hx.2
    exact ⟨l.sound.1.trans (logBessel_mono hl0 hx0 hx.1),
      (logBessel_mono hx0 hu0 hx.2).trans u.sound.2⟩
  slope_bounds := by
    apply slopeBounds_of_hasDerivAt
      (fun x _ => (log_bessel_derivative x).continuousAt.continuousWithinAt)
      (fun x _ => log_bessel_derivative x)
    intro x hx
    have h2 : (⟨2,2⟩ : RationalInterval).Contains (2 : ℝ) := by norm_num [RationalInterval.Contains]
    exact RationalInterval.contains_mul h2 (ht x (Ioo_subset_Icc_self hx))

#print axioms logBesselFunctionEnclosure
end BecknerOnofri.HighDim.ScalarCertificate
