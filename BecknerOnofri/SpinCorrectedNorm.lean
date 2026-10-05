import BecknerOnofri.SpinPolytopeBound

/-! Correcting arbitrary tangent vectors by the two explicit vectors from
Lemma 5.18, and the resulting seminorm estimate. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace BecknerOnofri.HighDim.Spin

theorem l1_smul (a : ℝ) (q : Count → ℝ) : l1 (a•q)=|a| * l1 q := by
  simp [l1,abs_mul,Finset.mul_sum]

theorem l1_eq_zero_iff (q : Count → ℝ) : l1 q=0 ↔ q=0 := by
  constructor
  · intro h
    ext j
    have hj := coordinate_le_l1 q j
    rw [h] at hj
    exact abs_eq_zero.mp (le_antisymm hj (abs_nonneg _))
  · rintro rfl
    simp [l1]

theorem zero_coordinate_seminorm_bound {q : Count → ℝ}
    (hq0 : q 0=0) (hmass : (∑ j : Count,q j)=0) (hmean : mean q=0) :
    ‖featureMap q‖≤Real.sqrt (7/8)*l1 q := by
  by_cases hl : l1 q=0
  · rw [(l1_eq_zero_iff q).mp hl]
    simp [l1]
  have hp : 0<l1 q := lt_of_le_of_ne (l1_nonneg q) (Ne.symm hl)
  let r := (1/l1 q)•q
  have hr : r ∈ tangentPolytope := by
    refine ⟨by simp [r,hq0],by simp [r,← Finset.mul_sum,hmass],?_,?_⟩
    · have h := mean_linear_combination q q (1/l1 q) 0
      simpa [r,hmean] using h
    · change l1 ((1/l1 q)•q)≤1
      rw [l1_smul,abs_of_pos (by positivity),one_div_mul_cancel hl]
  have hb := tangentPolytope_quadratic_bound r hr
  have hnorm : ‖featureMap r‖≤Real.sqrt (7/8) := by
    rw [featureMap_norm]
    exact Real.sqrt_le_sqrt hb
  have he : q=l1 q•r := by
    dsimp [r]
    rw [smul_smul,mul_one_div_cancel hl,one_smul]
  calc
    ‖featureMap q‖ = l1 q*‖featureMap r‖ := by
      conv_lhs => rw [he,map_smul,norm_smul,Real.norm_eq_abs,abs_of_pos hp]
    _ ≤ l1 q*Real.sqrt (7/8) := mul_le_mul_of_nonneg_left hnorm hp.le
    _ = _ := mul_comm _ _

def correctionV : Count → ℝ := fun j => (correctionVQ j : ℝ)
def correctionZ : Count → ℝ := fun j => (correctionZQ j : ℝ)

theorem correcting_real_constraints :
    correctionV 0=1 ∧ correctionZ 0=0 ∧
    (∑ j : Count,correctionV j)=0 ∧ mean correctionV=0 ∧
    (∑ j : Count,correctionZ j)=0 ∧ mean correctionZ=1 := by
  refine ⟨by norm_num [correctionV,correctionVQ],by norm_num [correctionZ,correctionZQ]; decide,?_,?_,?_,?_⟩
  · unfold correctionV
    exact_mod_cast correcting_vectors_constraints.1
  · unfold mean meanCoordinate correctionV
    exact_mod_cast correcting_vectors_constraints.2.1
  · unfold correctionZ
    exact_mod_cast correcting_vectors_constraints.2.2.1
  · unfold mean meanCoordinate correctionZ
    exact_mod_cast correcting_vectors_constraints.2.2.2

theorem correcting_real_norms : ‖featureMap correctionV‖≤2 ∧ ‖featureMap correctionZ‖≤4 := by
  have hv : quadratic correctionV<4 := by
    unfold correctionV
    rw [quadratic_cast]
    exact_mod_cast correcting_vectors_bounds.1
  have hz : quadratic correctionZ<16 := by
    unfold correctionZ
    rw [quadratic_cast]
    exact_mod_cast correcting_vectors_bounds.2
  constructor
  · nlinarith [featureMap_norm_sq correctionV,norm_nonneg (featureMap correctionV)]
  · nlinarith [featureMap_norm_sq correctionZ,norm_nonneg (featureMap correctionZ)]

theorem correcting_offzero_l1 :
    (∑ j ∈ Finset.univ.erase (0:Count),|correctionV j|)=13/11 ∧
    (∑ j ∈ Finset.univ.erase (0:Count),|correctionZ j|)=12/11 := by
  have h : (∑ j ∈ Finset.univ.erase (0:Count),|correctionVQ j|)=(13/11:ℚ) ∧
      (∑ j ∈ Finset.univ.erase (0:Count),|correctionZQ j|)=(12/11:ℚ) := by decide +kernel
  have hv := congrArg (fun x : ℚ => (x:ℝ)) h.1
  have hz := congrArg (fun x : ℚ => (x:ℝ)) h.2
  push_cast at hv hz
  exact ⟨hv,hz⟩

#print axioms zero_coordinate_seminorm_bound
end BecknerOnofri.HighDim.Spin
