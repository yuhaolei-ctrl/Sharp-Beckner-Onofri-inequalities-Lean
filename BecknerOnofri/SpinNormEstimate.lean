import BecknerOnofri.SpinCorrectedNorm

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace BecknerOnofri.HighDim.Spin

theorem mean_sub (q r : Count → ℝ) : mean (q-r)=mean q-mean r := by
  simp [mean,mul_sub,Finset.sum_sub_distrib]
theorem mean_smul (a : ℝ) (q : Count → ℝ) : mean (a•q)=a*mean q := by
  simp [mean,Finset.mul_sum,mul_left_comm,mul_assoc]

theorem corrected_l1_bound (q : Count → ℝ) :
    l1 (q-q 0•correctionV-mean q•correctionZ) ≤
      (∑ j ∈ Finset.univ.erase (0:Count),|q j|)+(13/11)*|q 0|+(12/11)*|mean q| := by
  let r := q-q 0•correctionV-mean q•correctionZ
  have hr0 : r 0=0 := by simp [r,correcting_real_constraints.1,correcting_real_constraints.2.1]
  have he : l1 r=∑ j ∈ Finset.univ.erase (0:Count),|r j| := by
    have h := Finset.sum_erase_add Finset.univ (f:=fun j => |r j|) (Finset.mem_univ (0:Count))
    simpa [l1,hr0] using h.symm
  change l1 r≤_
  rw [he]
  calc
    _ ≤ ∑ j ∈ Finset.univ.erase (0:Count),
        (|q j|+|q 0| * |correctionV j|+|mean q| * |correctionZ j|) := by
      apply Finset.sum_le_sum
      intro j _
      have h1 := abs_add_le (q j-q 0*correctionV j) (-(mean q*correctionZ j))
      have h2 := abs_add_le (q j) (-(q 0*correctionV j))
      simp only [← sub_eq_add_neg,abs_neg,abs_mul] at h1 h2
      change |q j-q 0*correctionV j-mean q*correctionZ j|≤_
      linarith
    _ = _ := by
      rw [Finset.sum_add_distrib,Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum,
        correcting_offzero_l1.1,correcting_offzero_l1.2]
      ring

/-- The seminorm inequality immediately before the curvature constants in
the manuscript. It holds for every mass-zero vector. -/
theorem corrected_seminorm_bound (q : Count → ℝ) (hmass : (∑ j : Count,q j)=0) :
    Real.sqrt (quadratic q) ≤
      Real.sqrt (7/8)*(∑ j ∈ Finset.univ.erase (0:Count),|q j|)+
        (35/11)*|q 0|+(56/11)*|mean q| := by
  let r := q-q 0•correctionV-mean q•correctionZ
  obtain ⟨hv0,hz0,hvm,hvx,hzm,hzx⟩ := correcting_real_constraints
  have hr0 : r 0=0 := by simp [r,hv0,hz0]
  have hrm : (∑ j : Count,r j)=0 := by
    simp [r,Finset.sum_sub_distrib,← Finset.mul_sum,hmass,hvm,hzm]
  have hrx : mean r=0 := by
    dsimp [r]
    rw [mean_sub,mean_sub,mean_smul,mean_smul,hvx,hzx]
    ring
  have hnr := zero_coordinate_seminorm_bound hr0 hrm hrx
  have hl := corrected_l1_bound q
  change l1 r≤_ at hl
  have hdecomp : q=r+q 0•correctionV+mean q•correctionZ := by dsimp [r]; module
  have htri : ‖featureMap q‖≤‖featureMap r‖+
      |q 0| * ‖featureMap correctionV‖+|mean q| * ‖featureMap correctionZ‖ := by
    conv_lhs => rw [hdecomp,map_add,map_add,map_smul,map_smul]
    have h1 := norm_add_le (featureMap r+q 0•featureMap correctionV)
      (mean q•featureMap correctionZ)
    have h2 := norm_add_le (featureMap r) (q 0•featureMap correctionV)
    simp only [norm_smul,Real.norm_eq_abs] at h1 h2 ⊢
    linarith
  have hv := mul_le_mul_of_nonneg_left correcting_real_norms.1 (abs_nonneg (q 0))
  have hz := mul_le_mul_of_nonneg_left correcting_real_norms.2 (abs_nonneg (mean q))
  have hs : Real.sqrt (7/8)≤1 := by
    apply (Real.sqrt_le_iff).mpr
    norm_num
  have hs0 := Real.sqrt_nonneg (7/8)
  have hr := mul_le_mul_of_nonneg_left hl hs0
  rw [featureMap_norm] at htri
  nlinarith [mul_nonneg (sub_nonneg.mpr hs) (abs_nonneg (q 0)),
    mul_nonneg (sub_nonneg.mpr hs) (abs_nonneg (mean q))]

#print axioms corrected_seminorm_bound
end BecknerOnofri.HighDim.Spin
