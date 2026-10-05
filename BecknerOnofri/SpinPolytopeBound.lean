module

public import BecknerOnofri.SpinSparseVertices

@[expose] public section

/-! The vertex computation is promoted to a bound on the entire tangent
polytope, with no finite-support or optimizer hypothesis left over. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open Set
namespace BecknerOnofri.HighDim.Spin

def vertex (i j k : Count) : Count → ℝ := fun r => (vertexQ i j k r : ℝ)

theorem vertex_apply (i j k r : Count) (hik : i<k) : vertex i j k r=
    if r=i then ((k.val:ℝ)-j.val)/(2*((k.val:ℝ)-i.val))
    else if r=j then -1/2
    else if r=k then ((j.val:ℝ)-i.val)/(2*((k.val:ℝ)-i.val)) else 0 := by
  have hki : (k.val:ℝ)-(i.val:ℝ)≠0 := by
    have h : (i.val:ℝ)<k.val := by exact_mod_cast hik
    linarith
  have hki2 : (k.val:ℝ)*2-(i.val:ℝ)*2≠0 := by
    convert mul_ne_zero hki (by norm_num : (2:ℝ)≠0) using 1 <;> ring
  have hki' : -(i.val:ℝ)+k.val≠0 := by simpa [sub_eq_add_neg,add_comm] using hki
  unfold vertex vertexQ meanCoordinateQ
  split_ifs <;> push_cast <;> field_simp [hki,hki2] <;> ring_nf <;>
    field_simp [hki,hki2,hki'] <;> ring_nf <;> field_simp [hki,hki'] <;> ring

theorem sparse_eq_smul_vertex {q : Count → ℝ} {i j k : Count}
    (hij : i<j) (hjk : j<k)
    (hs : ∀ r,r ≠ i → r ≠ j → r ≠ k → q r=0)
    (hmass : (∑ r : Count,q r)=0) (hmean : mean q=0) :
    q=(-2*q j)•vertex i j k := by
  obtain ⟨hm,hx⟩ := sparse_mass_moment hij hjk hs hmass hmean
  have hki : (k.val:ℝ)-(i.val:ℝ) ≠ 0 := by
    have h : (i.val:ℝ)<k.val := by exact_mod_cast hij.trans hjk
    linarith
  ext r
  simp only [Pi.smul_apply,smul_eq_mul,vertex_apply i j k r (hij.trans hjk)]
  by_cases hi : r=i
  · subst r
    simp only [if_true]
    field_simp
    nlinarith
  by_cases hj : r=j
  · subst r
    simp [hi]
    <;> ring
  by_cases hk : r=k
  · subst r
    simp only [if_neg hi,if_neg hj,if_true]
    field_simp
    nlinarith
  simp [hi,hj,hk,hs r hi hj hk]

theorem sparse_scale_bound {q : Count → ℝ} {i j k : Count}
    (hij : i<j) (hjk : j<k)
    (hs : ∀ r,r ≠ i → r ≠ j → r ≠ k → q r=0)
    (hmass : (∑ r : Count,q r)=0) (hl1 : l1 q≤1) : |-2*q j|≤1 := by
  have hm := sum_supported_three q hij hjk hs
  have hl := sum_supported_three (fun r => |q r|) hij hjk
    (by intro r hi hj hk; rw [hs r hi hj hk,abs_zero])
  change (∑ r : Count,|q r|)≤1 at hl1
  have he : q i+q k= -q j := by linarith
  have htri := abs_add_le (q i) (q k)
  rw [he,abs_neg] at htri
  rw [abs_mul]
  norm_num
  linarith

theorem quadratic_smul (a : ℝ) (q : Count → ℝ) : quadratic (a•q)=a^2*quadratic q := by
  rw [← featureMap_norm_sq,map_smul,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,
    featureMap_norm_sq]

theorem quadratic_vertex_bound {i j k : Count} (hi : 1 ≤ i.val) (hij : i<j) (hjk : j<k) :
    quadratic (vertex i j k)≤7/8 := by
  have h := (vertex_energy_bound i j k hi hij hjk).trans vertex_energy_lt_seven_eighths.le
  rw [← vertex_energy_eq hij hjk] at h
  change quadratic (fun r => (vertexQ i j k r : ℝ))≤7/8
  rw [quadratic_cast]
  have hc := Rat.cast_le (K:=ℝ).mpr h
  norm_num only [Rat.cast_div,Rat.cast_ofNat] at hc
  exact hc

/-- The complete polytope maximum bound, including the analytic passage from
arbitrary vectors to the finitely checked vertices. -/
theorem tangentPolytope_quadratic_bound :
    ∀ q ∈ tangentPolytope,quadratic q≤7/8 := by
  apply quadratic_bound_of_extreme
  intro q hq
  obtain ⟨i,j,k,hi,hij,hjk,hs⟩ := extreme_support_three hq
  have hrep := sparse_eq_smul_vertex hij hjk hs hq.1.2.1 hq.1.2.2.1
  have hscale := sparse_scale_bound hij hjk hs hq.1.2.1 hq.1.2.2.2
  have hsq : (-2*q j)^2≤1 := by nlinarith [sq_abs (-2*q j),abs_nonneg (-2*q j)]
  have hb := quadratic_vertex_bound hi hij hjk
  have hn := quadratic_nonneg (vertex i j k)
  rw [hrep,quadratic_smul]
  nlinarith [mul_nonneg (sub_nonneg.mpr hsq) hn]

#print axioms tangentPolytope_quadratic_bound
end BecknerOnofri.HighDim.Spin
