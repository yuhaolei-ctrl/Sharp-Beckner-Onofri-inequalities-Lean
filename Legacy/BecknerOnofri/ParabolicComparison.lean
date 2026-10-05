module

public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Order.LeftRightNhds
public import Mathlib.Tactic

@[expose] public section

/-! A one-dimensional parabolic comparison principle proved by the compact minimum argument.
Only interior values of the nonnegative potential are used; it may be singular at the endpoints.
The temporal derivative is a genuine derivative within the closed time interval.
-/
noncomputable section
open Set Filter
open scoped Topology
namespace Legacy.BecknerOnofri.ParabolicComparison

def rectangle (T a b : ℝ) : Set (ℝ × ℝ) := Icc 0 T ×ˢ Icc a b

/-- At a minimum over a time interval, a genuine left-compatible derivative is nonpositive.
This includes the final time and does not assume a two-sided temporal neighborhood. -/
theorem time_derivative_nonpos {f : ℝ → ℝ} {T t d : ℝ}
    (ht : 0 < t) (htT : t ≤ T) (hmin : IsMinOn f (Icc 0 T) t)
    (hd : HasDerivWithinAt f d (Icc 0 T) t) : d ≤ 0 := by
  have hseg : segment ℝ t 0 ⊆ Icc 0 T :=
    (convex_Icc (𝕜:=ℝ) 0 T).segment_subset ⟨ht.le,htT⟩ ⟨le_rfl,ht.le.trans htT⟩
  have hy := sub_mem_posTangentConeAt_of_segment_subset hseg
  have hh := hmin.localize.hasFDerivWithinAt_nonneg hd.hasFDerivWithinAt hy
  change 0 ≤ (0-t)*d at hh
  nlinarith

/-- The necessary second-derivative condition is derived from a derivative slope and the MVT.
No continuity of the second derivative is required. -/
theorem second_derivative_nonneg {f g : ℝ → ℝ} {a b x d : ℝ}
    (hx : x ∈ Ioo a b) (hc : ContinuousOn f (Icc a b))
    (hmin : IsMinOn f (Icc a b) x)
    (hd : ∀ y ∈ Ioo a b, HasDerivAt f (g y) y)
    (hdd : HasDerivAt g d x) : 0 ≤ d := by
  have hgx : g x = 0 :=
    (hmin.isLocalMin (Icc_mem_nhds hx.1 hx.2)).hasDerivAt_eq_zero (hd x hx)
  by_contra! hneg
  have hslope : ∀ᶠ y in 𝓝[>] x, slope g x y < 0 :=
    (hasDerivAt_iff_tendsto_slope_left_right.mp hdd).2
      (IsOpen.mem_nhds isOpen_Iio hneg)
  have hgneg : ∀ᶠ y in 𝓝[>] x, g y < 0 := by
    filter_upwards [hslope,self_mem_nhdsWithin] with y hy hxy
    rw [slope_def_field,hgx,sub_zero] at hy
    simpa only [zero_mul] using (div_lt_iff₀ (sub_pos.mpr hxy)).mp hy
  obtain ⟨u,hu,hgu⟩ := (mem_nhdsGT_iff_exists_mem_Ioc_Ioo_subset hx.2).mp hgneg
  have hsub : Icc x u ⊆ Icc a b := fun z hz => ⟨hx.1.le.trans hz.1,hz.2.trans hu.2⟩
  obtain ⟨c,hcx,he⟩ := exists_hasDerivAt_eq_slope f g hu.1 (hc.mono hsub)
    (fun z hz => hd z ⟨hx.1.trans hz.1,hz.2.trans_le hu.2⟩)
  have hgc := hgu hcx
  change g c < 0 at hgc
  have hfu : f x ≤ f u := hmin (hsub ⟨hu.1.le,le_rfl⟩)
  have hge : 0 ≤ (f u-f x)/(u-x) := div_nonneg (sub_nonneg.mpr hfu) (sub_pos.mpr hu.1).le
  linarith

/-- A strictly positive parabolic supersolution with nonnegative initial and lateral data. -/
theorem nonnegative_of_strict
    (w wt wx wxx : ℝ → ℝ → ℝ) (V : ℝ → ℝ) (T a b : ℝ)
    (hc : ContinuousOn (fun z : ℝ × ℝ => w z.1 z.2) (rectangle T a b))
    (htime : ∀ t ∈ Ioc 0 T, ∀ x ∈ Ioo a b,
      HasDerivWithinAt (fun s => w s x) (wt t x) (Icc 0 T) t)
    (hspace : ∀ t ∈ Ioc 0 T, ∀ x ∈ Ioo a b, HasDerivAt (w t) (wx t x) x)
    (hsecond : ∀ t ∈ Ioc 0 T, ∀ x ∈ Ioo a b, HasDerivAt (wx t) (wxx t x) x)
    (hV : ∀ x ∈ Ioo a b, 0 ≤ V x)
    (hpde : ∀ t ∈ Ioc 0 T, ∀ x ∈ Ioo a b, 0 < wt t x-wxx t x+V x*w t x)
    (hzero : ∀ x ∈ Icc a b, 0 ≤ w 0 x)
    (hleft : ∀ t ∈ Icc 0 T, 0 ≤ w t a)
    (hright : ∀ t ∈ Icc 0 T, 0 ≤ w t b) :
    ∀ t ∈ Icc 0 T, ∀ x ∈ Icc a b, 0 ≤ w t x := by
  intro t ht x hx
  by_contra! hneg
  obtain ⟨⟨s,y⟩,⟨hs,hy⟩,hmin⟩ := (isCompact_Icc.prod isCompact_Icc).exists_isMinOn
    (show (rectangle T a b).Nonempty from ⟨(t,x),ht,hx⟩) hc
  have hwy : w s y < 0 := (hmin (show (t,x) ∈ rectangle T a b from ⟨ht,hx⟩)).trans_lt hneg
  have hspos : 0 < s := by
    by_contra! hn
    have he : s = 0 := le_antisymm hn hs.1
    rw [he] at hwy
    exact not_lt_of_ge (hzero y hy) hwy
  have hya : a < y := by
    by_contra! hn
    have he : y = a := le_antisymm hn hy.1
    have hz := hleft s hs
    rw [he] at hwy
    linarith
  have hyb : y < b := by
    by_contra! hn
    have he : y = b := le_antisymm hy.2 hn
    have hz := hright s hs
    rw [he] at hwy
    linarith
  have hsi : s ∈ Ioc 0 T := ⟨hspos,hs.2⟩
  have hyi : y ∈ Ioo a b := ⟨hya,hyb⟩
  have htmin : IsMinOn (fun r => w r y) (Icc 0 T) s :=
    fun r hr => hmin (show (r,y) ∈ rectangle T a b from ⟨hr,hy⟩)
  have hxMin : IsMinOn (w s) (Icc a b) y :=
    fun z hz => hmin (show (s,z) ∈ rectangle T a b from ⟨hs,hz⟩)
  have hcx : ContinuousOn (w s) (Icc a b) :=
    hc.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun z hz => show (s,z) ∈ rectangle T a b from ⟨hs,hz⟩)
  have hwt := time_derivative_nonpos hspos hs.2 htmin (htime s hsi y hyi)
  have hwxx := second_derivative_nonneg hyi hcx hxMin (hspace s hsi) (hsecond s hsi y hyi)
  have hvw : V y*w s y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (hV y hyi) hwy.le
  linarith [hpde s hsi y hyi]

/-- Weak parabolic supersolutions are nonnegative, by the genuine perturbation `epsilon*(t+1)`. -/
theorem nonnegative
    (w wt wx wxx : ℝ → ℝ → ℝ) (V : ℝ → ℝ) (T a b : ℝ)
    (hc : ContinuousOn (fun z : ℝ × ℝ => w z.1 z.2) (rectangle T a b))
    (htime : ∀ t ∈ Ioc 0 T, ∀ x ∈ Ioo a b,
      HasDerivWithinAt (fun s => w s x) (wt t x) (Icc 0 T) t)
    (hspace : ∀ t ∈ Ioc 0 T, ∀ x ∈ Ioo a b, HasDerivAt (w t) (wx t x) x)
    (hsecond : ∀ t ∈ Ioc 0 T, ∀ x ∈ Ioo a b, HasDerivAt (wx t) (wxx t x) x)
    (hV : ∀ x ∈ Ioo a b, 0 ≤ V x)
    (hpde : ∀ t ∈ Ioc 0 T, ∀ x ∈ Ioo a b, 0 ≤ wt t x-wxx t x+V x*w t x)
    (hzero : ∀ x ∈ Icc a b, 0 ≤ w 0 x)
    (hleft : ∀ t ∈ Icc 0 T, 0 ≤ w t a)
    (hright : ∀ t ∈ Icc 0 T, 0 ≤ w t b) :
    ∀ t ∈ Icc 0 T, ∀ x ∈ Icc a b, 0 ≤ w t x := by
  have hpert : ∀ ε : ℝ, 0 < ε → ∀ t ∈ Icc 0 T, ∀ x ∈ Icc a b,
      0 ≤ w t x+ε*(t+1) := by
    intro ε hε
    apply nonnegative_of_strict (fun t x => w t x+ε*(t+1))
      (fun t x => wt t x+ε) wx wxx V T a b
    · exact hc.add (by fun_prop)
    · intro t ht x hx
      convert! (htime t ht x hx).add
        ((((hasDerivAt_id t).add_const 1).const_mul ε).hasDerivWithinAt) using 1 <;> ring
    · intro t ht x hx
      exact (hspace t ht x hx).add_const _
    · exact hsecond
    · exact hV
    · intro t ht x hx
      have hh := hpde t ht x hx
      have hp : 0 ≤ V x*(ε*(t+1)) := mul_nonneg (hV x hx)
        (mul_nonneg hε.le (by linarith [ht.1]))
      nlinarith
    · intro x hx
      have hh := hzero x hx
      nlinarith
    · intro t ht
      have hh := hleft t ht
      have hp : 0 ≤ ε*(t+1) := mul_nonneg hε.le (by linarith [ht.1])
      linarith
    · intro t ht
      have hh := hright t ht
      have hp : 0 ≤ ε*(t+1) := mul_nonneg hε.le (by linarith [ht.1])
      linarith
  intro t ht x hx
  by_contra! hw
  have htp : 0 < t+1 := by linarith [ht.1]
  have hε : 0 < -w t x/(2*(t+1)) := div_pos (by linarith) (by positivity)
  have hh := hpert (-w t x/(2*(t+1))) hε t ht x hx
  have he : (-w t x/(2*(t+1)))*(t+1) = -w t x/2 := by field_simp
  rw [he] at hh
  linarith

#print axioms time_derivative_nonpos
#print axioms second_derivative_nonneg
#print axioms nonnegative
end Legacy.BecknerOnofri.ParabolicComparison
