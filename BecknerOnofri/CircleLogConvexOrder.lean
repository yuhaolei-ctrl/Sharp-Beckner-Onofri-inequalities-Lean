import BecknerOnofri.CircleConvexCrossings

/-! Convex order from a continuous convex logarithmic density ratio and
matching zeroth and first moments. No external crossing theorem is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
namespace BecknerOnofri.HighDim.CircleScalar

theorem log_convex_order {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (z q g : X → ℝ) (F φ : ℝ → ℝ) (hc : Continuous F)
    (hF : ConvexOn ℝ (Icc (-1:ℝ) 1) F) (hφ : ConvexOn ℝ (Icc (-1:ℝ) 1) φ)
    (hz : ∀ᵐ x ∂μ,z x ∈ Icc (-1:ℝ) 1) (hq : ∀ᵐ x ∂μ,0≤q x)
    (hg : ∀ᵐ x ∂μ,g x=q x*(Real.exp (F (z x))-1))
    (hi : Integrable g μ) (hzi : Integrable (fun x => z x*g x) μ)
    (hφi : Integrable (fun x => φ (z x)*g x) μ)
    (hmass : (∫ x,g x ∂μ)=0) (hmean : (∫ x,z x*g x ∂μ)=0) :
    0≤∫ x,φ (z x)*g x ∂μ := by
  by_cases hn : ∃ y ∈ Icc (-1:ℝ) 1,F y<0
  · obtain ⟨a,b,ha,hb,hab,hin,hout⟩ := convex_negative_crossings F hc hF hn
    apply two_sign_change_convex_test μ z g φ a b ha hb hab hφ hz ?_ ?_ hi hzi hφi hmass hmean
    · filter_upwards [hq,hg] with x hqx hgx
      intro hax hxb
      rw [hgx]
      exact mul_nonpos_of_nonneg_of_nonpos hqx (sub_nonpos.mpr (Real.exp_le_one_iff.mpr (hin _ hax hxb).le))
    · filter_upwards [hz,hq,hg] with x hzx hqx hgx
      intro hx
      rw [hgx]
      exact mul_nonneg hqx (sub_nonneg.mpr (Real.one_le_exp_iff.mpr (hout _ hzx hx)))
  · push_neg at hn
    have hnon : ∀ᵐ x ∂μ,0≤g x := by
      filter_upwards [hz,hq,hg] with x hzx hqx hgx
      rw [hgx]
      exact mul_nonneg hqx (sub_nonneg.mpr (Real.one_le_exp_iff.mpr (hn _ hzx)))
    have hzero := (integral_eq_zero_iff_of_nonneg_ae hnon hi).mp hmass
    have he : (fun x => φ (z x)*g x)=ᵐ[μ](fun _ => 0) := by
      filter_upwards [hzero] with x hx
      simp [hx]
    rw [integral_congr_ae he,integral_zero]

#print axioms log_convex_order
end BecknerOnofri.HighDim.CircleScalar
