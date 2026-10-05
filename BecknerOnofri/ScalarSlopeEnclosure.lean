import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

/-! Signed slope enclosures, including min/max junctions. This is the
analytic rule behind bounding the four scalar candidates on whole mesh
intervals; no differentiability of their minimum is assumed. -/
namespace BecknerOnofri.HighDim.ScalarCertificate
open Set

def SlopeBounds (s : Set ℝ) (f : ℝ → ℝ) (l u : ℝ) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, x≤y → l*(y-x)≤f y-f x ∧ f y-f x≤u*(y-x)

theorem SlopeBounds.widen {s : Set ℝ} {f : ℝ → ℝ} {l u l' u' : ℝ}
    (h : SlopeBounds s f l u) (hl : l'≤l) (hu : u≤u') : SlopeBounds s f l' u' := by
  intro x hx y hy hxy
  have hh := h x hx y hy hxy
  exact ⟨(mul_le_mul_of_nonneg_right hl (sub_nonneg.mpr hxy)).trans hh.1,
    hh.2.trans (mul_le_mul_of_nonneg_right hu (sub_nonneg.mpr hxy))⟩

theorem SlopeBounds.add {s : Set ℝ} {f g : ℝ → ℝ} {lf uf lg ug : ℝ}
    (hf : SlopeBounds s f lf uf) (hg : SlopeBounds s g lg ug) :
    SlopeBounds s (fun x => f x+g x) (lf+lg) (uf+ug) := by
  intro x hx y hy hxy
  have h1 := hf x hx y hy hxy
  have h2 := hg x hx y hy hxy
  constructor <;> nlinarith [h1.1,h1.2,h2.1,h2.2]

theorem SlopeBounds.neg {s : Set ℝ} {f : ℝ → ℝ} {l u : ℝ}
    (hf : SlopeBounds s f l u) : SlopeBounds s (fun x => -f x) (-u) (-l) := by
  intro x hx y hy hxy
  have h := hf x hx y hy hxy
  constructor <;> nlinarith [h.1,h.2]

theorem slopeBounds_const (s : Set ℝ) (c : ℝ) : SlopeBounds s (fun _ => c) 0 0 := by
  intro x hx y hy hxy
  simp

theorem SlopeBounds.pointwise_min {s : Set ℝ} {f g : ℝ → ℝ} {lf uf lg ug : ℝ}
    (hf : SlopeBounds s f lf uf) (hg : SlopeBounds s g lg ug) :
    SlopeBounds s (fun x => min (f x) (g x)) (min lf lg) (max uf ug) := by
  have hf' := hf.widen (min_le_left lf lg) (le_max_left uf ug)
  have hg' := hg.widen (min_le_right lf lg) (le_max_right uf ug)
  intro x hx y hy hxy
  have h1 := hf' x hx y hy hxy
  have h2 := hg' x hx y hy hxy
  by_cases hx' : f x≤g x <;> by_cases hy' : f y≤g y
  · simp only [min_eq_left hx', min_eq_left hy']; exact h1
  · simp only [min_eq_left hx', min_eq_right (le_of_not_ge hy')]
    constructor <;> linarith [h1.1,h1.2,h2.1,h2.2]
  · simp only [min_eq_right (le_of_not_ge hx'), min_eq_left hy']
    constructor <;> linarith [h1.1,h1.2,h2.1,h2.2]
  · simp only [min_eq_right (le_of_not_ge hx'), min_eq_right (le_of_not_ge hy')]; exact h2

theorem SlopeBounds.pointwise_max {s : Set ℝ} {f g : ℝ → ℝ} {lf uf lg ug : ℝ}
    (hf : SlopeBounds s f lf uf) (hg : SlopeBounds s g lg ug) :
    SlopeBounds s (fun x => max (f x) (g x)) (min lf lg) (max uf ug) := by
  have h := (hf.neg.pointwise_min hg.neg).neg
  simpa only [min_neg_neg, max_neg_neg, neg_neg] using h

theorem SlopeBounds.lower_from_point {a b l u x L : ℝ} {f : ℝ → ℝ}
    (hf : SlopeBounds (Icc a b) f l u) (hx : x∈Icc a b) (hL : L≤f x) :
    ∀ t ∈ Icc a b, L-max (|l|) (|u|)*max (x-a) (b-x)≤f t := by
  intro t ht
  have hdist : 0≤max (x-a) (b-x) := le_trans (sub_nonneg.mpr hx.1) (le_max_left _ _)
  have hM : 0≤max |l| |u| := (abs_nonneg _).trans (le_max_left _ _)
  have hml : -max |l| |u|≤l := (neg_le_neg (le_max_left _ _)).trans (neg_abs_le _)
  have hmu : u≤max |l| |u| := (le_abs_self _).trans (le_max_right _ _)
  by_cases hxt : x≤t
  · have h := (hf.widen hml hmu) x hx t ht hxt
    have hd : t-x≤max (x-a) (b-x) := (sub_le_sub_right ht.2 x).trans (le_max_right _ _)
    nlinarith [mul_le_mul_of_nonneg_left hd hM]
  · have htx : t≤x := le_of_not_ge hxt
    have h := (hf.widen hml hmu) t ht x hx htx
    have hd : x-t≤max (x-a) (b-x) := (sub_le_sub_left ht.1 x).trans (le_max_left _ _)
    nlinarith [mul_le_mul_of_nonneg_left hd hM]


theorem slopeBounds_of_hasDerivAt {a b l u : ℝ} {f f' : ℝ → ℝ}
    (hc : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hbound : ∀ x ∈ Ioo a b, l≤f' x ∧ f' x≤u) :
    SlopeBounds (Icc a b) f l u := by
  have hdiff : DifferentiableOn ℝ f (interior (Icc a b)) := by
    rw [interior_Icc]
    exact fun x hx => (hd x hx).differentiableAt.differentiableWithinAt
  have hl : ∀ x ∈ interior (Icc a b), l≤deriv f x := by
    simp only [interior_Icc]
    intro x hx
    rw [(hd x hx).deriv]
    exact (hbound x hx).1
  have hu : ∀ x ∈ interior (Icc a b), deriv f x≤u := by
    simp only [interior_Icc]
    intro x hx
    rw [(hd x hx).deriv]
    exact (hbound x hx).2
  intro x hx y hy hxy
  exact ⟨(convex_Icc a b).mul_sub_le_image_sub_of_le_deriv hc hdiff hl x hx y hy hxy,
    (convex_Icc a b).image_sub_le_mul_sub_of_deriv_le hc hdiff hu x hx y hy hxy⟩

#print axioms SlopeBounds.pointwise_min
#print axioms SlopeBounds.lower_from_point
end BecknerOnofri.HighDim.ScalarCertificate
