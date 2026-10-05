import BecknerOnofri.ScalarGammaBaseEnclosure

noncomputable section
namespace BecknerOnofri.HighDim.ScalarCertificate
open CircleScalar Set

structure GammaEnclosureData (a b : ℝ) where
  base : FunctionEnclosure a b gammaBaseAt
  first : FunctionEnclosure a b (besselMoment 1)
  second : FunctionEnclosure a b (besselMoment 2)
  third : FunctionEnclosure a b (besselMoment 3)
  weightOne : FunctionEnclosure a b (fun h => weight 1 (besselMoment 1 h))
  weightTwo : FunctionEnclosure a b (fun h => weight 2 (besselMoment 1 h))

def GammaEnclosureData.A {a b : ℝ} (_ : GammaEnclosureData a b) :
    FunctionEnclosure a b (fun _ => (633/2000 : ℝ)) :=
  (FunctionEnclosure.const a b (633/2000)).congr (fun _ => by norm_num)
def GammaEnclosureData.B {a b : ℝ} (d : GammaEnclosureData a b) :
    FunctionEnclosure a b (fun h => (27/40)*weight 1 (besselMoment 1 h)) :=
  (((FunctionEnclosure.const a b (27/40)).congr (fun _ => by norm_num)) :
    FunctionEnclosure a b (fun _ => (27/40 : ℝ))).rmul d.weightOne

def GammaEnclosureData.C {a b : ℝ} (d : GammaEnclosureData a b) :
    FunctionEnclosure a b (fun h => (27/40)*weight 2 (besselMoment 1 h)) :=
  (((FunctionEnclosure.const a b (27/40)).congr (fun _ => by norm_num)) :
    FunctionEnclosure a b (fun _ => (27/40 : ℝ))).rmul d.weightTwo

def GammaEnclosureData.D {a b : ℝ} (d : GammaEnclosureData a b) :
    FunctionEnclosure a b (fun h => 6-besselMoment 1 h) :=
  (((FunctionEnclosure.const a b 6).congr (fun _ => by norm_num)) :
    FunctionEnclosure a b (fun _ => (6 : ℝ))).rsub d.first

def GammaEnclosureData.L {a b : ℝ} (d : GammaEnclosureData a b) :
    FunctionEnclosure a b (fun h => 6*besselMoment 2 h-besselMoment 3 h) :=
  ((((FunctionEnclosure.const a b 6).congr (fun _ => by norm_num)) :
    FunctionEnclosure a b (fun _ => (6 : ℝ))).rmul d.second).rsub d.third

def GammaEnclosureData.check {a b : ℝ} (d : GammaEnclosureData a b) : Bool :=
  decide (0<(d.A.radd d.B).value.lower ∧
    0<((d.A.radd d.B).radd (d.C.rmul d.D.rsquare)).value.lower ∧ 0<d.D.value.lower)

def GammaEnclosureData.enclosure {a b : ℝ} (d : GammaEnclosureData a b)
    (hc : d.check=true) : FunctionEnclosure a b gammaAt := by
  have h := of_decide_eq_true hc
  have hAB := h.1
  have hABC := h.2.1
  have hD := h.2.2
  let e := candidateFunctionEnclosure d.A d.B d.C d.D d.L d.first.rsquare d.second hAB hABC hD
  exact d.base.radd e

/-- A completed scalar cell carries an actual inequality on every mean in
its interval. The numerical fields alone are never a scalar certificate. -/
structure CertifiedGammaCell where
  left : ℚ
  right : ℚ
  lower : ℚ
  sound : ∀ t : ℝ,t∈Icc (left : ℝ) (right : ℝ) → (lower : ℝ)≤gamma t

def gammaPanelCheck (a b : MeanBracket) (c L : ℚ)
    (whole : FunctionEnclosure a.lower b.upper gammaAt)
    (point : FunctionEnclosure c c gammaAt) : Bool :=
  decide (0≤a.mean ∧ b.mean<1 ∧ a.lower≤c ∧ c≤b.upper ∧
    L≤point.value.lower-max |whole.slope.lower| |whole.slope.upper| * max (c-a.lower) (b.upper-c))

def gammaCellOfEnclosures (a b : MeanBracket) (c L : ℚ)
    (whole : FunctionEnclosure a.lower b.upper gammaAt)
    (point : FunctionEnclosure c c gammaAt)
    (hc : gammaPanelCheck a b c L whole point=true) : CertifiedGammaCell where
  left := a.mean
  right := b.mean
  lower := L
  sound := by
    obtain ⟨ha,hb,hac,hcb,hL⟩ := of_decide_eq_true hc
    intro t ht
    have ht0 : 0≤t := (show (0 : ℝ)≤a.mean by exact_mod_cast ha).trans ht.1
    have ht1 : t<1 := ht.2.trans_lt (show (b.mean : ℝ)<1 by exact_mod_cast hb)
    have hp := MeanBracket.interval ha hb ht
    have hm : (c : ℝ)∈Icc (a.lower : ℝ) (b.upper : ℝ) := by
      constructor <;> assumption_mod_cast
    have h := gamma_lower_from_parameter_interval hm whole.slope_bounds
      (point.value_mem c ⟨le_rfl,le_rfl⟩).1 ht0 ht1 hp
    have hl := (Rat.cast_le (K := ℝ)).mpr hL
    push_cast at hl
    exact hl.trans h

#print axioms GammaEnclosureData.enclosure
#print axioms gammaCellOfEnclosures
end BecknerOnofri.HighDim.ScalarCertificate
