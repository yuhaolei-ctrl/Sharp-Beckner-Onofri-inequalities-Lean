import BecknerOnofri.CircleScalarDefinitions
import Mathlib.Tactic

/-! Soundness of the four scalar candidates used in the manuscript's
interval enclosure of γ. All domain boundaries and junctions are included. -/
noncomputable section
namespace BecknerOnofri.HighDim.CircleScalar

theorem quadratic_center_comparison (K E V x y : ℝ) (hK : 0<K)
    (hxy : (y-E/K)^2≤(x-E/K)^2) :
    K*y^2-2*E*y+V≤K*x^2-2*E*x+V := by
  have he (z : ℝ) : K*z^2-2*E*z+V=K*(z-E/K)^2+V-E^2/K := by
    field_simp [hK.ne']
    <;> ring
  rw [he,he]
  have h := mul_le_mul_of_nonneg_left hxy hK.le
  linarith

theorem squared_distance_left (v y x : ℝ) (hvy : v≤y) (hyx : y≤x) :
    (y-v)^2≤(x-v)^2 := by nlinarith

theorem squared_distance_right (x y v : ℝ) (hxy : x≤y) (hyv : y≤v) :
    (y-v)^2≤(x-v)^2 := by nlinarith

theorem candidate_dominates_point (A B C D L r m x : ℝ)
    (hA : 0<A) (hB : 0≤B) (hC : 0≤C) (hD : 0<D) (hm : m≤x) :
    ∃ y : ℝ, (y=m ∨ y=max m (B*r/(A+B)) ∨
      y=max m ((B*r+C*D*L)/(A+B+C*D^2)) ∨ y=max m (L/D)) ∧
      m≤y ∧ cost A B C D L r y≤cost A B C D L r x := by
  let j := L/D
  let u := B*r/(A+B)
  let v := (B*r+C*D*L)/(A+B+C*D^2)
  have hK : 0<A+B := by linarith
  have hK' : 0<A+B+C*D^2 := by positivity
  have hinactive (z : ℝ) (hz : j≤z) : cost A B C D L r z=
      (A+B)*z^2-2*(B*r)*z+B*r^2 := by
    have hh : L-D*z≤0 := by
      have := (div_le_iff₀ hD).mp hz
      nlinarith
    rw [cost,max_eq_left hh]
    ring
  have hactive (z : ℝ) (hz : z≤j) : cost A B C D L r z=
      (A+B+C*D^2)*z^2-2*(B*r+C*D*L)*z+(B*r^2+C*L^2) := by
    have hh : 0≤L-D*z := by
      have := (le_div_iff₀ hD).mp hz
      nlinarith
    rw [cost,max_eq_right hh]
    ring
  by_cases hxj : j≤x
  · let z := max m j
    have hzx : z≤x := max_le hm hxj
    by_cases huz : u≤z
    · refine ⟨z,Or.inr (Or.inr (Or.inr rfl)),le_max_left _ _,?_⟩
      rw [hinactive z (le_max_right _ _),hinactive x hxj]
      exact quadratic_center_comparison _ _ _ _ _ hK (squared_distance_left u z x huz hzx)
    · have hzu : z≤u := le_of_lt (lt_of_not_ge huz)
      have hmu : m≤u := (le_max_left _ _).trans hzu
      have hju : j≤u := (le_max_right _ _).trans hzu
      refine ⟨u,Or.inr (Or.inl (max_eq_right hmu).symm),hmu,?_⟩
      rw [hinactive u hju,hinactive x hxj]
      apply quadratic_center_comparison _ _ _ _ _ hK
      change (u-u)^2≤(x-u)^2
      simpa using sq_nonneg (x-u)
  · have hxj' : x≤j := le_of_lt (lt_of_not_ge hxj)
    have hmj : m≤j := hm.trans hxj'
    by_cases hvm : v≤m
    · refine ⟨m,Or.inl rfl,le_rfl,?_⟩
      rw [hactive m hmj,hactive x hxj']
      exact quadratic_center_comparison _ _ _ _ _ hK' (squared_distance_left v m x hvm hm)
    · have hmv : m≤v := le_of_lt (lt_of_not_ge hvm)
      by_cases hjv : j≤v
      · refine ⟨j,Or.inr (Or.inr (Or.inr (max_eq_right hmj).symm)),hmj,?_⟩
        rw [hactive j le_rfl,hactive x hxj']
        exact quadratic_center_comparison _ _ _ _ _ hK' (squared_distance_right x j v hxj' hjv)
      · have hvj : v≤j := le_of_lt (lt_of_not_ge hjv)
        refine ⟨v,Or.inr (Or.inr (Or.inl (max_eq_right hmv).symm)),hmv,?_⟩
        rw [hactive v hvj,hactive x hxj']
        apply quadratic_center_comparison _ _ _ _ _ hK'
        change (v-v)^2≤(x-v)^2
        simpa using sq_nonneg (x-v)

/-- The finite minimum is a global lower bound over the full half-line. -/
theorem candidateMinimum_le (A B C D L r m x : ℝ)
    (hA : 0<A) (hB : 0≤B) (hC : 0≤C) (hD : 0<D) (hm : m≤x) :
    candidateMinimum A B C D L r m≤cost A B C D L r x := by
  obtain ⟨y,hy,_,hle⟩ := candidate_dominates_point A B C D L r m x hA hB hC hD hm
  apply le_trans (b:=cost A B C D L r y) _ hle
  rcases hy with rfl|rfl|rfl|rfl
  · exact (min_le_left _ _).trans (min_le_left _ _)
  · exact (min_le_left _ _).trans (min_le_right _ _)
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · exact (min_le_right _ _).trans (min_le_right _ _)

/-- Each of the four input values is feasible; thus the finite minimum is
attained on the half-line and equals its true constrained minimum. -/
theorem candidateMinimum_attained (A B C D L r m : ℝ) :
    ∃ x : ℝ, m≤x ∧ cost A B C D L r x=candidateMinimum A B C D L r m := by
  unfold candidateMinimum
  by_cases h : min (cost A B C D L r m) (cost A B C D L r (max m (B*r/(A+B))))≤
      min (cost A B C D L r (max m ((B*r+C*D*L)/(A+B+C*D^2))))
        (cost A B C D L r (max m (L/D)))
  · rw [min_eq_left h]
    by_cases h' : cost A B C D L r m≤cost A B C D L r (max m (B*r/(A+B)))
    · exact ⟨m,le_rfl,(min_eq_left h').symm⟩
    · exact ⟨max m (B*r/(A+B)),le_max_left _ _,(min_eq_right (le_of_not_ge h')).symm⟩
  · rw [min_eq_right (le_of_not_ge h)]
    by_cases h' : cost A B C D L r (max m ((B*r+C*D*L)/(A+B+C*D^2)))≤
        cost A B C D L r (max m (L/D))
    · exact ⟨max m ((B*r+C*D*L)/(A+B+C*D^2)),le_max_left _ _,(min_eq_left h').symm⟩
    · exact ⟨max m (L/D),le_max_left _ _,(min_eq_right (le_of_not_ge h')).symm⟩

#print axioms candidateMinimum_le
#print axioms candidateMinimum_attained
end BecknerOnofri.HighDim.CircleScalar
