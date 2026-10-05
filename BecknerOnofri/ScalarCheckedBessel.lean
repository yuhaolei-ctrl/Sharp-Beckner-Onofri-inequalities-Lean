module

public import BecknerOnofri.ScalarBesselRows
public import BecknerOnofri.ScalarReciprocalEnclosure
public import BecknerOnofri.CircleBesselRatioEnclosure

@[expose] public section

namespace BecknerOnofri.HighDim.ScalarCertificate
open CircleScalar Set

structure CheckedBessel where
  argument : ℚ
  order : ℕ
  value : RationalInterval
  sound : value.Contains (bessel order (argument : ℝ))

def checkedBesselOfRows (cs : List BesselRow) (hc : cs.all BesselRow.check=true)
    (i : Fin cs.length) : CheckedBessel where
  argument := (cs[i]).numerator / (cs[i]).denominator
  order := (cs[i]).order
  value := ⟨(cs[i]).lower / besselPrecision, (cs[i]).upper / besselPrecision⟩
  sound := by
    simpa only [RationalInterval.Contains,Rat.cast_div,Rat.cast_intCast,Rat.cast_natCast]
      using besselRows_sound cs hc i

structure CheckedMoment where
  argument : ℚ
  order : ℕ
  value : RationalInterval
  sound : value.Contains (besselMoment order (argument : ℝ))

def CheckedMoment.ofBessel (num den : CheckedBessel)
    (ha : num.argument=den.argument) (hn : den.order=0) (hp : 0<den.value.lower) :
    CheckedMoment where
  argument := num.argument
  order := num.order
  value := num.value.mul den.value.inv
  sound := by
    have hd : den.value.Contains (bessel 0 (num.argument : ℝ)) := by
      simpa only [hn,ha] using den.sound
    simpa only [besselMoment,div_eq_mul_inv] using
      RationalInterval.contains_mul num.sound (RationalInterval.contains_inv hp hd)

structure MeanBracket where
  mean : ℚ
  lower : ℚ
  upper : ℚ
  sound : ∀ t : ℝ, t=(mean : ℝ) → 0≤t → t<1 →
    (lower : ℝ)≤parameter t ∧ parameter t≤(upper : ℝ)

def meanBracketCheck (t : ℚ) (lo hi : CheckedMoment) : Bool :=
  decide (0≤t ∧ t<1 ∧ lo.order=1 ∧ hi.order=1 ∧
    lo.value.upper≤t ∧ t≤hi.value.lower)

def meanBracketOfMoments (t : ℚ) (lo hi : CheckedMoment)
    (hc : meanBracketCheck t lo hi=true) : MeanBracket where
  mean := t
  lower := lo.argument
  upper := hi.argument
  sound := by
    obtain ⟨ht,ht1,hlo,hhi,hl,hu⟩ := of_decide_eq_true hc
    intro x hx hx0 hx1
    subst x
    apply parameter_bracket _ _ _ hx0 hx1
    · have h := lo.sound.2
      rw [hlo] at h
      exact h.trans (by exact_mod_cast hl)
    · have h := hi.sound.1
      rw [hhi] at h
      exact (show (t : ℝ)≤hi.value.lower by exact_mod_cast hu).trans h

theorem parameter_monotoneOn : MonotoneOn parameter (Ico 0 1) := by
  intro a ha b hb hab
  apply besselMoment_first_strictMono.le_iff_le.mp
  rw [(parameter_mean ha.1 ha.2).1,(parameter_mean hb.1 hb.2).1]
  exact hab

theorem MeanBracket.interval {a b : MeanBracket}
    (ha0 : 0≤a.mean) (hb1 : b.mean<1) {t : ℝ}
    (ht : t∈Icc (a.mean : ℝ) (b.mean : ℝ)) :
    (a.lower : ℝ)≤parameter t ∧ parameter t≤(b.upper : ℝ) := by
  have hA : (0 : ℝ)≤a.mean := by exact_mod_cast ha0
  have hB : (b.mean : ℝ)<1 := by exact_mod_cast hb1
  have ht0 := hA.trans ht.1
  have ht1 := ht.2.trans_lt hB
  have hma : (a.mean : ℝ)<1 := ht.1.trans_lt ht1
  have hmb : (0 : ℝ)≤b.mean := ht0.trans ht.2
  exact ⟨(a.sound _ rfl hA hma).1.trans
      (parameter_monotoneOn ⟨hA,hma⟩ ⟨ht0,ht1⟩ ht.1),
    (parameter_monotoneOn ⟨ht0,ht1⟩ ⟨hmb,hB⟩ ht.2).trans
      (b.sound _ rfl hmb hB).2⟩

#print axioms meanBracketOfMoments
#print axioms MeanBracket.interval
end BecknerOnofri.HighDim.ScalarCertificate
