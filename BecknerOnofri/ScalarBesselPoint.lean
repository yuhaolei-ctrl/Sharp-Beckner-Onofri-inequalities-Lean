module

public import BecknerOnofri.ScalarMomentFunctionEnclosure
public import BecknerOnofri.ScalarRoundedEnclosure

@[expose] public section

namespace BecknerOnofri.HighDim.ScalarCertificate
open CircleScalar Set

structure BesselPoint where
  argument : ℚ
  values : Fin 5 → RationalInterval
  nonneg : 0≤argument
  basepos : 0<(values 0).lower
  sound : ∀ n,(values n).Contains (bessel n (argument : ℝ))

def besselPointCheck (h : ℚ) (cs : Fin 5 → CheckedBessel) : Bool :=
  decide (0≤h ∧ 0<(cs 0).value.lower ∧ ∀ n,(cs n).argument=h ∧ (cs n).order=n)

def besselPointOfChecked (h : ℚ) (cs : Fin 5 → CheckedBessel)
    (hc : besselPointCheck h cs=true) : BesselPoint where
  argument := h
  values := fun n => (cs n).value
  nonneg := (of_decide_eq_true hc).1
  basepos := (of_decide_eq_true hc).2.1
  sound := by
    intro n
    have he := (of_decide_eq_true hc).2.2 n
    have hs := (cs n).sound
    simpa only [he.1,he.2] using hs

def BesselPoint.momentValue (p : BesselPoint) (n : Fin 5) : RationalInterval :=
  ((p.values n).mul (p.values 0).inv).rounded scalarPrecision

theorem BesselPoint.moment_sound (p : BesselPoint) (n : Fin 5) :
    (p.momentValue n).Contains (besselMoment n (p.argument : ℝ)) := by
  have h := RationalInterval.contains_mul (p.sound n)
    (RationalInterval.contains_inv p.basepos (p.sound 0))
  have hr := RationalInterval.contains_rounded scalarPrecision (by norm_num [scalarPrecision]) h
  simpa only [BesselPoint.momentValue,besselMoment,Fin.val_zero,div_eq_mul_inv] using hr

def momentRange (l u : BesselPoint) (n : Fin 5) : RationalInterval :=
  ⟨(l.momentValue n).lower,(u.momentValue n).upper⟩

theorem momentRange_sound (l u : BesselPoint) (n : Fin 5) {x : ℝ}
    (hx : x∈Icc (l.argument : ℝ) (u.argument : ℝ)) :
    (momentRange l u n).Contains (besselMoment n x) := by
  have hl0 : (0 : ℝ)≤l.argument := by exact_mod_cast l.nonneg
  have hx0 := hl0.trans hx.1
  have hu0 := hx0.trans hx.2
  exact ⟨(l.moment_sound n).1.trans (besselMoment_mono n hl0 hx0 hx.1),
    (besselMoment_mono n hx0 hu0 hx.2).trans (u.moment_sound n).2⟩

noncomputable def firstMomentEnclosure (l u : BesselPoint) :
    FunctionEnclosure l.argument u.argument (besselMoment 1) :=
  momentFunctionEnclosure _ _ 1 (by omega) (momentRange l u 0) (momentRange l u 2)
    (momentRange l u 1) (momentRange l u 1)
    (fun _ hx => momentRange_sound l u 0 hx) (fun _ hx => momentRange_sound l u 2 hx)
    (fun _ hx => momentRange_sound l u 1 hx) (fun _ hx => momentRange_sound l u 1 hx)

noncomputable def secondMomentEnclosure (l u : BesselPoint) :
    FunctionEnclosure l.argument u.argument (besselMoment 2) :=
  momentFunctionEnclosure _ _ 2 (by omega) (momentRange l u 1) (momentRange l u 3)
    (momentRange l u 2) (momentRange l u 1)
    (fun _ hx => momentRange_sound l u 1 hx) (fun _ hx => momentRange_sound l u 3 hx)
    (fun _ hx => momentRange_sound l u 2 hx) (fun _ hx => momentRange_sound l u 1 hx)

noncomputable def thirdMomentEnclosure (l u : BesselPoint) :
    FunctionEnclosure l.argument u.argument (besselMoment 3) :=
  momentFunctionEnclosure _ _ 3 (by omega) (momentRange l u 2) (momentRange l u 4)
    (momentRange l u 3) (momentRange l u 1)
    (fun _ hx => momentRange_sound l u 2 hx) (fun _ hx => momentRange_sound l u 4 hx)
    (fun _ hx => momentRange_sound l u 3 hx) (fun _ hx => momentRange_sound l u 1 hx)

#print axioms firstMomentEnclosure
#print axioms thirdMomentEnclosure
end BecknerOnofri.HighDim.ScalarCertificate
