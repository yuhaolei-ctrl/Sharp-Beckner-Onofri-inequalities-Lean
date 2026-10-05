module

public import BecknerOnofri.SpinSecondOrderSupport

@[expose] public section

/-! The second-order support estimate on the complete feasible simplex,
including zero coordinates at the target endpoint. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open Set
namespace BecknerOnofri.HighDim.Spin

theorem feasible_segment {p q : Count → ℝ} (hp : Feasible p) (hq : Feasible q)
    {t : ℝ} (ht : t ∈ Icc 0 1) : Feasible (p+t•(q-p)) := by
  refine ⟨?_,?_,?_⟩
  · intro j
    change 0≤p j+t*(q j-p j)
    nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (hp.1 j),mul_nonneg ht.1 (hq.1 j)]
  · simp [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum,hp.2.1,hq.2.1]
  · change p 0+t*(q 0-p 0)≤1/4096
    have h1 := mul_le_mul_of_nonneg_left hp.2.2 (sub_nonneg.mpr ht.2)
    have h2 := mul_le_mul_of_nonneg_left hq.2.2 ht.1
    nlinarith

theorem segment_positive {p q : Count → ℝ} (hp : ∀ j,0<p j) (hq : Feasible q)
    {t : ℝ} (ht0 : 0≤t) (ht1 : t<1) : ∀ j,0<p j+t*(q j-p j) := by
  intro j
  have h1 := mul_pos (sub_pos.mpr ht1) (hp j)
  have h2 := mul_nonneg ht0 (hq.1 j)
  nlinarith

theorem variance_controls_l1 {p v : Count → ℝ}
    (hp : Feasible p) (hpos : ∀ j,0<p j) :
    (l1 v)^2≤∑ j : Count,v j^2/p j := by
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.univ : Finset Count)
    (r:=fun j => |v j|) (f:=fun j => v j^2/p j) (g:=p)
    (fun j _ => div_nonneg (sq_nonneg _) (hpos j).le) (fun j _ => (hpos j).le)
    (fun j _ => by rw [sq_abs,div_mul_cancel₀ _ (hpos j).ne'])
  simpa [hp.2.1,l1] using h

/-- The full strong support inequality underlying the global parabolas. -/
theorem functional_support_remainder {p q : Count → ℝ}
    (hp : Feasible p) (hpos : ∀ j,0<p j) (hq : Feasible q) :
    functional p+functionalSlope p (q-p) 0-
      350*(mean q-mean p)^2+(l1 (q-p))^2/20≤functional q := by
  have hv : (∑ j : Count,(q-p) j)=0 := by
    simp [Finset.sum_sub_distrib,hp.2.1,hq.2.1]
  have h0 := functional_segment_derivative p (q-p) 0 (by simpa using hpos)
  have h1 (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :=
    functional_segment_derivative p (q-p) t (segment_positive hpos hq ht.1.le ht.2)
  have h2 (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :=
    functional_segment_second_derivative p (q-p) t (segment_positive hpos hq ht.1.le ht.2)
  have hb (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :
      (l1 (q-p))^2/10-700*(mean (q-p))^2≤functionalHessian p (q-p) t := by
    have hr := feasible_segment hp hq ⟨ht.1.le,ht.2.le⟩
    have hrpos : ∀ j,0<(p+t•(q-p)) j := segment_positive hpos hq ht.1.le ht.2
    have hc := all_mean_curvature hr hrpos hv
    have hl := variance_controls_l1 (v:=q-p) hr hrpos
    change quadratic (q-p)≤(19/20)*entropyHessian p (q-p) t+350*(mean (q-p))^2 at hc
    change (l1 (q-p))^2≤entropyHessian p (q-p) t at hl
    unfold functionalHessian
    linarith
  have h := second_order_support (functional_segment_continuous p (q-p)).continuousOn h0 h1 h2 hb
  have he : p+(1:ℝ)•(q-p)=q := by module
  simp only [zero_smul,add_zero,he,mean_sub] at h
  linarith

#print axioms functional_support_remainder
end BecknerOnofri.HighDim.Spin
