import BecknerOnofri.ScalarReciprocalEnclosure
import BecknerOnofri.EntropyExpCertificate

namespace BecknerOnofri.HighDim.ScalarCertificate
open EntropyTail.ExpCertificate Set

def RationalInterval.rounded (P : ℕ) (i : RationalInterval) : RationalInterval :=
  ⟨roundDown P i.lower,roundUp P i.upper⟩

theorem RationalInterval.contains_rounded (P : ℕ) (hP : 0<P)
    {i : RationalInterval} {x : ℝ} (hx : i.Contains x) : (i.rounded P).Contains x :=
  ⟨((Rat.cast_le (K := ℝ)).mpr (roundDown_le P hP _)).trans hx.1,
    hx.2.trans ((Rat.cast_le (K := ℝ)).mpr (le_roundUp P hP _))⟩

noncomputable def FunctionEnclosure.rounded (P : ℕ) (hP : 0<P)
    {a b : ℝ} {f : ℝ → ℝ} (ef : FunctionEnclosure a b f) : FunctionEnclosure a b f where
  value := ef.value.rounded P
  slope := ef.slope.rounded P
  value_mem := fun x hx => RationalInterval.contains_rounded P hP (ef.value_mem x hx)
  slope_bounds := ef.slope_bounds.widen
    ((Rat.cast_le (K := ℝ)).mpr (roundDown_le P hP _))
    ((Rat.cast_le (K := ℝ)).mpr (le_roundUp P hP _))

noncomputable def FunctionEnclosure.congr {a b : ℝ} {f g : ℝ → ℝ}
    (ef : FunctionEnclosure a b f) (h : ∀ x, f x=g x) : FunctionEnclosure a b g where
  value := ef.value
  slope := ef.slope
  value_mem := fun x hx => by rw [← h x]; exact ef.value_mem x hx
  slope_bounds := by simpa only [show f=g from funext h] using ef.slope_bounds

def scalarPrecision : ℕ := 10^40

noncomputable def FunctionEnclosure.round {a b : ℝ} {f : ℝ → ℝ}
    (ef : FunctionEnclosure a b f) : FunctionEnclosure a b f :=
  ef.rounded scalarPrecision (by norm_num [scalarPrecision])

noncomputable def FunctionEnclosure.radd {a b : ℝ} {f g : ℝ → ℝ}
    (ef : FunctionEnclosure a b f) (eg : FunctionEnclosure a b g) :
    FunctionEnclosure a b (fun x => f x+g x) := (ef.add eg).round

noncomputable def FunctionEnclosure.rmul {a b : ℝ} {f g : ℝ → ℝ}
    (ef : FunctionEnclosure a b f) (eg : FunctionEnclosure a b g) :
    FunctionEnclosure a b (fun x => f x*g x) := (ef.mul eg).round

noncomputable def FunctionEnclosure.rsub {a b : ℝ} {f g : ℝ → ℝ}
    (ef : FunctionEnclosure a b f) (eg : FunctionEnclosure a b g) :
    FunctionEnclosure a b (fun x => f x-g x) :=
  ((ef.add eg.neg).congr (fun _ => (sub_eq_add_neg ..).symm)).round

noncomputable def FunctionEnclosure.rsquare {a b : ℝ} {f : ℝ → ℝ}
    (ef : FunctionEnclosure a b f) : FunctionEnclosure a b (fun x => (f x)^2) :=
  ((ef.mul ef).congr (fun _ => (pow_two _).symm)).round

noncomputable def FunctionEnclosure.rdiv {a b : ℝ} {f g : ℝ → ℝ}
    (ef : FunctionEnclosure a b f) (eg : FunctionEnclosure a b g) (hg : 0<eg.value.lower) :
    FunctionEnclosure a b (fun x => f x/g x) :=
  ((ef.mul (eg.inv hg)).congr (fun _ => (div_eq_mul_inv ..).symm)).round

#print axioms FunctionEnclosure.rdiv
end BecknerOnofri.HighDim.ScalarCertificate
