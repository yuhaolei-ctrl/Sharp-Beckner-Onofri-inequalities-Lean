module

public import BecknerOnofri.ScalarGammaInterval
public import BecknerOnofri.ScalarDerivativeEnclosure
public import BecknerOnofri.ScalarLogBesselEnclosure

@[expose] public section

noncomputable section
namespace BecknerOnofri.HighDim.ScalarCertificate
open CircleScalar Set

noncomputable def identityFunctionEnclosure (a b : ℚ) : FunctionEnclosure a b (fun x : ℝ => x) where
  value := ⟨a,b⟩
  slope := ⟨1,1⟩
  value_mem := fun _ hx => hx
  slope_bounds := by intro x hx y hy hxy; simp

/-- Cancel the derivative of log I0 analytically before applying interval
arithmetic, exactly as in the source's scalar enclosure route. -/
noncomputable def gammaBaseFunctionEnclosure {a b : ℝ}
    (eh : FunctionEnclosure a b (fun h : ℝ => h))
    (et : FunctionEnclosure a b (besselMoment 1))
    (ez : FunctionEnclosure a b (fun h => Real.log (bessel 0 h)))
    (ep : FunctionEnclosure a b (fun h => Real.log (1+besselMoment 1 h)))
    (em : FunctionEnclosure a b (fun h => Real.log (1-besselMoment 1 h)))
    (ht : -1<et.value.lower) (ht1 : et.value.upper<1) :
    FunctionEnclosure a b gammaBaseAt := by
  let c := FunctionEnclosure.const a b
  let one : FunctionEnclosure a b (fun _ => (1 : ℝ)) := (c 1).congr (fun _ => Rat.cast_one)
  let two : FunctionEnclosure a b (fun _ => (2 : ℝ)) := (c 2).congr (fun _ => Rat.cast_ofNat 2)
  let c13 : FunctionEnclosure a b (fun _ => (33/100 : ℝ)) :=
    (c (33/100)).congr (fun _ => by norm_num)
  let c27 : FunctionEnclosure a b (fun _ => (67/100 : ℝ)) :=
    (c (67/100)).congr (fun _ => by norm_num)
  let d13 : FunctionEnclosure a b (fun _ => (13/20 : ℝ)) :=
    (c (13/20)).congr (fun _ => by norm_num)
  let d27 : FunctionEnclosure a b (fun _ => (27/20 : ℝ)) :=
    (c (27/20)).congr (fun _ => by norm_num)
  let ib2 := ((one.radd et).rmul ep).radd ((one.rsub et).rmul em)
  let raw := ((c13.rmul (((two.rmul eh).rmul et).rsub ez)).radd (c27.rmul et.rsquare)).rsub ib2
  let rawBase : FunctionEnclosure a b gammaBaseAt := raw.congr (fun h => by
    dsimp [gammaBaseAt,rateAt,Spin.binaryCost]
    ring)
  let factor := (((d13.rmul eh).radd (d27.rmul et)).rsub ep).radd em
  refine ⟨rawBase.value,et.slope.mul factor.value,rawBase.value_mem,?_⟩
  have bounds (h : ℝ) (hh : h∈Icc a b) : -1<besselMoment 1 h ∧ besselMoment 1 h<1 :=
    ⟨(show (-1 : ℝ)<et.value.lower by exact_mod_cast ht).trans_le (et.value_mem h hh).1,
      (et.value_mem h hh).2.trans_lt (by exact_mod_cast ht1)⟩
  apply slopeBounds_of_hasDerivAt
    (fun h hh => (gammaBaseAt_derivative h (bounds h hh).1 (bounds h hh).2).continuousAt.continuousWithinAt)
    (fun h hh => gammaBaseAt_derivative h (bounds h (Ioo_subset_Icc_self hh)).1
      (bounds h (Ioo_subset_Icc_self hh)).2)
  intro h hh
  have hd := et.derivative_mem hh (besselMoment_derivative 1 (by omega) h)
  norm_num only [Nat.sub_self,Nat.reduceAdd] at hd
  exact RationalInterval.contains_mul hd (factor.value_mem h (Ioo_subset_Icc_self hh))

#print axioms gammaBaseFunctionEnclosure
end BecknerOnofri.HighDim.ScalarCertificate
