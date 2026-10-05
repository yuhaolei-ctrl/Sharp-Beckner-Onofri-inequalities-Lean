import BecknerOnofri.ScalarCheckedWeight

noncomputable section
namespace BecknerOnofri.HighDim.ScalarCertificate
open Set CircleScalar EntropyLogCertificate

def FunctionEnclosure.revalue {a b : ℝ} {f : ℝ → ℝ}
    (ef : FunctionEnclosure a b f) (v : RationalInterval)
    (hv : ∀ x∈Icc a b,v.Contains (f x)) : FunctionEnclosure a b f where
  value := v
  slope := ef.slope
  value_mem := hv
  slope_bounds := ef.slope_bounds

def logComposeCheck {a b : ℝ} {f : ℝ → ℝ} (ef : FunctionEnclosure a b f)
    (l u : CheckedLog) : Bool :=
  decide (0<l.value ∧ l.value≤u.value ∧ l.value≤ef.value.lower ∧ ef.value.upper≤u.value)

def logCompose {a b : ℝ} {f : ℝ → ℝ} (ef : FunctionEnclosure a b f)
    (l u : CheckedLog) (hc : logComposeCheck ef l u=true) :
    FunctionEnclosure a b (fun h => Real.log (f h)) := by
  have h := of_decide_eq_true hc
  have hp := h.1
  have hlu := h.2.1
  have hl := h.2.2.1
  have hu := h.2.2.2
  let ef' := ef.revalue ⟨l.value,u.value⟩ (fun x hx =>
    ⟨(show (l.value : ℝ)≤ef.value.lower by exact_mod_cast hl).trans (ef.value_mem x hx).1,
      (ef.value_mem x hx).2.trans (show (ef.value.upper : ℝ)≤u.value by exact_mod_cast hu)⟩)
  let eg := logFunctionEnclosure l u hp
  have hpos : 0<u.value := hp.trans_le hlu
  have hs : eg.slope.lower≤eg.slope.upper := (inv_le_inv₀ hpos hp).mpr hlu
  exact ef'.comp eg hs

def weightComposeCheck {a b : ℝ} {f : ℝ → ℝ} (ef : FunctionEnclosure a b f)
    (n : ℕ) (l u : CheckedWeight) : Bool :=
  decide (l.order=n ∧ u.order=n ∧ 0<l.argument ∧ u.argument<1 ∧ l.argument≤u.argument ∧
    l.argument≤ef.value.lower ∧ ef.value.upper≤u.argument) &&
      weightDerivativeCheck ⟨l.argument,u.argument⟩

def weightCompose {a b : ℝ} {f : ℝ → ℝ} (ef : FunctionEnclosure a b f)
    (n : ℕ) (hn : n=1 ∨ n=2) (l u : CheckedWeight)
    (hc : weightComposeCheck ef n l u=true) :
    FunctionEnclosure a b (fun h => weight n (f h)) := by
  have hnum := (Bool.and_eq_true_iff.mp hc).1
  have hder := (Bool.and_eq_true_iff.mp hc).2
  have h := of_decide_eq_true hnum
  have ho := h.1
  have ho' := h.2.1
  have hp := h.2.2.1
  have hu1 := h.2.2.2.1
  have hlu := h.2.2.2.2.1
  have hl := h.2.2.2.2.2.1
  have hu := h.2.2.2.2.2.2
  let ef' := ef.revalue ⟨l.argument,u.argument⟩ (fun x hx =>
    ⟨(show (l.argument : ℝ)≤ef.value.lower by exact_mod_cast hl).trans (ef.value_mem x hx).1,
      (ef.value_mem x hx).2.trans (show (ef.value.upper : ℝ)≤u.argument by exact_mod_cast hu)⟩)
  let eg := weightFunctionEnclosure n hn l u ho ho' hp hu1 hder
  have hm : (l.argument : ℝ)∈Icc (l.argument : ℝ) (u.argument : ℝ) :=
    ⟨le_rfl,by exact_mod_cast hlu⟩
  have hs' := weightDerivativeInterval_sound n ⟨l.argument,u.argument⟩
    ⟨l.value.lower,u.value.upper⟩ hder hm (eg.value_mem l.argument hm)
  have hs : eg.slope.lower≤eg.slope.upper := (Rat.cast_le (K := ℝ)).mp (hs'.1.trans hs'.2)
  exact ef'.comp eg hs

#print axioms logCompose
#print axioms weightCompose
end BecknerOnofri.HighDim.ScalarCertificate
