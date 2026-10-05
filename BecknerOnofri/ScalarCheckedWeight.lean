import BecknerOnofri.CircleWeightDerivative
import BecknerOnofri.ScalarCompositionEnclosure

namespace BecknerOnofri.HighDim.ScalarCertificate
open CircleScalar EntropyLogCertificate Set
open scoped BigOperators

structure CheckedWeight where
  argument : ℚ
  order : ℕ
  value : RationalInterval
  sound : value.Contains (weight order (argument : ℝ))

def weightLogCheck (t : ℚ) (l : CheckedLog) : Bool :=
  decide (0<t ∧ t<1 ∧ l.value=1-t^2)

def checkedWeightOfLog (n : ℕ) (t : ℚ) (l : CheckedLog)
    (hc : weightLogCheck t l=true) : CheckedWeight where
  argument := t
  order := n
  value :=
    let s := ∑ j∈Finset.range n,t^(2*(j+1))/(j+1 : ℚ)
    ⟨(-l.upper-s)/t^(2*n+2),(-l.lower-s)/t^(2*n+2)⟩
  sound := by
    obtain ⟨ht,ht1,hv⟩ := of_decide_eq_true hc
    have htR : (0 : ℝ)<t := by exact_mod_cast ht
    have ht1R : (t : ℝ)<1 := by exact_mod_cast ht1
    have hl := l.sound
    have he : (l.value : ℝ)=1-(t : ℝ)^2 := by exact_mod_cast hv
    rw [he] at hl
    rw [weight_closed_form n t htR ht1R]
    simp only [RationalInterval.Contains,Rat.cast_div,Rat.cast_sub,Rat.cast_neg,
      Rat.cast_pow,Rat.cast_sum,Rat.cast_add,Rat.cast_natCast,Rat.cast_one]
    constructor
    · exact div_le_div_of_nonneg_right (sub_le_sub_right (neg_le_neg hl.2) _) (by positivity)
    · exact div_le_div_of_nonneg_right (sub_le_sub_right (neg_le_neg hl.1) _) (by positivity)

theorem weight_interval (n : ℕ) (l u : CheckedWeight)
    (hl : l.order=n) (hu : u.order=n) (hpos : 0≤l.argument) (hlt : u.argument<1)
    {x : ℝ} (hx : x∈Icc (l.argument : ℝ) (u.argument : ℝ)) :
    (l.value.lower : ℝ)≤weight n x ∧ weight n x≤(u.value.upper : ℝ) := by
  have hl0 : (0 : ℝ)≤l.argument := by exact_mod_cast hpos
  have hu1 : (u.argument : ℝ)<1 := by exact_mod_cast hlt
  have hx0 := hl0.trans hx.1
  have hx1 := hx.2.trans_lt hu1
  have hlo := l.sound.1
  have hup := u.sound.2
  rw [hl] at hlo
  rw [hu] at hup
  exact ⟨hlo.trans (weight_mono n hl0 hx.1 hx1),
    (weight_mono n hx0 hx.2 hu1).trans hup⟩

def weightDerivativeInterval (n : ℕ) (t w : RationalInterval) : RationalInterval :=
  let one : RationalInterval := ⟨1,1⟩
  let two : RationalInterval := ⟨2,2⟩
  let coeff : RationalInterval := ⟨2*n+2,2*n+2⟩
  (two.mul (t.mul (one.add (t.mul t).neg)).inv).add ((coeff.mul (w.mul t.inv)).neg)

def weightDerivativeCheck (t : RationalInterval) : Bool :=
  decide (0<t.lower ∧ 0<(t.mul ((⟨1,1⟩ : RationalInterval).add (t.mul t).neg)).lower)

theorem weightDerivativeInterval_sound (n : ℕ) (ti wi : RationalInterval)
    (hc : weightDerivativeCheck ti=true) {t w : ℝ}
    (ht : ti.Contains t) (hw : wi.Contains w) :
    (weightDerivativeInterval n ti wi).Contains (2/(t*(1-t^2))-(2*n+2)*w/t) := by
  obtain ⟨hp,hp'⟩ := of_decide_eq_true hc
  have h1 : (⟨1,1⟩ : RationalInterval).Contains (1 : ℝ) := by norm_num [RationalInterval.Contains]
  have h2 : (⟨2,2⟩ : RationalInterval).Contains (2 : ℝ) := by norm_num [RationalInterval.Contains]
  have hn : (⟨2*n+2,2*n+2⟩ : RationalInterval).Contains (2*n+2 : ℝ) := by
    simp [RationalInterval.Contains]
  have hden := RationalInterval.contains_mul ht
    (RationalInterval.contains_add h1 (RationalInterval.contains_neg (RationalInterval.contains_mul ht ht)))
  have h := RationalInterval.contains_add
    (RationalInterval.contains_mul h2 (RationalInterval.contains_inv hp' hden))
    (RationalInterval.contains_neg (RationalInterval.contains_mul hn
      (RationalInterval.contains_mul hw (RationalInterval.contains_inv hp ht))))
  simpa only [weightDerivativeInterval,pow_two,div_eq_mul_inv,sub_eq_add_neg,mul_assoc] using h

noncomputable def weightFunctionEnclosure (n : ℕ) (hn : n=1 ∨ n=2)
    (l u : CheckedWeight) (hl : l.order=n) (hu : u.order=n)
    (hpos : 0<l.argument) (hlt : u.argument<1)
    (hc : weightDerivativeCheck ⟨l.argument,u.argument⟩=true) :
    FunctionEnclosure l.argument u.argument (weight n) where
  value := ⟨l.value.lower,u.value.upper⟩
  slope := weightDerivativeInterval n ⟨l.argument,u.argument⟩ ⟨l.value.lower,u.value.upper⟩
  value_mem := fun _ hx => weight_interval n l u hl hu hpos.le hlt hx
  slope_bounds := by
    have hd (x : ℝ) (hx : x∈Icc (l.argument : ℝ) (u.argument : ℝ)) :
        HasDerivAt (weight n) (2/(x*(1-x^2))-(2*n+2)*weight n x/x) x := by
      have hx0 : 0<x := (show (0 : ℝ)<l.argument by exact_mod_cast hpos).trans_le hx.1
      have hx1 : x<1 := hx.2.trans_lt (by exact_mod_cast hlt)
      rcases hn with rfl|rfl
      · convert weight_one_derivative x hx0 hx1 using 1 <;> norm_num
      · convert weight_two_derivative x hx0 hx1 using 1 <;> norm_num
    apply slopeBounds_of_hasDerivAt
      (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
      (fun x hx => hd x (Ioo_subset_Icc_self hx))
    intro x hx
    exact weightDerivativeInterval_sound n _ _ hc (Ioo_subset_Icc_self hx)
      (weight_interval n l u hl hu hpos.le hlt (Ioo_subset_Icc_self hx))

#print axioms checkedWeightOfLog
#print axioms weightFunctionEnclosure
end BecknerOnofri.HighDim.ScalarCertificate
