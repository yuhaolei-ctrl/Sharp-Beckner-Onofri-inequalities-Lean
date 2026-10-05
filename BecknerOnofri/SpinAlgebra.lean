module

public import BecknerOnofri.SpinDefinitions
public import Mathlib.Tactic

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace BecknerOnofri.HighDim.Spin

theorem quadraticQ_eq_sum (q : Count → ℚ) :
    quadraticQ q = ∑ s : Order,weightQ s*(∑ j : Count,momentQ s j*q j)^2 := by
  simp only [quadraticQ,interactionQ,Finset.mul_sum,Finset.sum_mul,pow_two]
  conv_lhs =>
    arg 2
    ext i
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem interaction_eq (i j : Count) :
    interaction i j = ∑ s : Order,weight s*moment s i*moment s j := by
  simp [interaction,interactionQ,weight,moment]

theorem quadratic_eq_sum (q : Count → ℝ) :
    quadratic q = ∑ s : Order,weight s*(∑ j : Count,moment s j*q j)^2 := by
  simp only [quadratic,interaction_eq,Finset.mul_sum,Finset.sum_mul,pow_two]
  conv_lhs =>
    arg 2
    ext i
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem weightQ_nonneg (s : Order) : 0≤weightQ s := by
  unfold weightQ
  positivity

theorem weight_nonneg (s : Order) : 0≤weight s := by
  unfold weight
  exact_mod_cast weightQ_nonneg s

theorem quadratic_nonneg (q : Count → ℝ) : 0≤quadratic q := by
  rw [quadratic_eq_sum]
  exact Finset.sum_nonneg (fun s _ => mul_nonneg (weight_nonneg s) (sq_nonneg _))

theorem interaction_symmetric (i j : Count) : interaction i j=interaction j i := by
  simp only [interaction_eq]
  apply Finset.sum_congr rfl
  intro s _
  ring

theorem quadratic_cast (q : Count → ℚ) :
    quadratic (fun j => (q j:ℝ))=(quadraticQ q:ℝ) := by
  simp [quadratic,quadraticQ,interaction]

theorem reference_mass : (∑ j : Count,reference j)=1 := by
  have h : (∑ j : Count,referenceQ j)=1 := by decide +kernel
  unfold reference
  exact_mod_cast h

theorem reference_pos (j : Count) : 0<reference j := by
  have h : ∀ j : Count,0<referenceQ j := by decide +kernel
  unfold reference
  exact_mod_cast h j

theorem reference_feasible : Feasible reference := by
  refine ⟨fun j => (reference_pos j).le,reference_mass,?_⟩
  norm_num [reference,referenceQ]

theorem vertexQ_sum (i j k : Count) (hij : i≠j) (hik : i≠k) (hjk : j≠k) (r : Count) :
    vertexQ i j k r =
      (if r=i then (meanCoordinateQ k-meanCoordinateQ j)/(2*(meanCoordinateQ k-meanCoordinateQ i)) else 0)+
      (if r=j then (-1/2:ℚ) else 0)+
      (if r=k then (meanCoordinateQ j-meanCoordinateQ i)/(2*(meanCoordinateQ k-meanCoordinateQ i)) else 0) := by
  unfold vertexQ
  split_ifs <;> simp_all

theorem vertex_energy_eq {i j k : Count} (hij : i<j) (hjk : j<k) :
    quadraticQ (vertexQ i j k)=vertexEnergyQ i j k := by
  rw [quadraticQ_eq_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [show (∑ r : Count,momentQ s r*vertexQ i j k r)=
      momentQ s i*((meanCoordinateQ k-meanCoordinateQ j)/(2*(meanCoordinateQ k-meanCoordinateQ i)))+
      momentQ s j*(-1/2)+
      momentQ s k*((meanCoordinateQ j-meanCoordinateQ i)/(2*(meanCoordinateQ k-meanCoordinateQ i))) by
    simp_rw [vertexQ_sum i j k hij.ne (hij.trans hjk).ne hjk.ne,
      mul_add,Finset.sum_add_distrib,mul_ite,mul_zero]
    simp]
  have hki : (k.val:ℚ)-(i.val:ℚ)≠0 := by
    have h : (i.val:ℚ)<k.val := by exact_mod_cast hij.trans hjk
    linarith
  congr 2
  unfold meanCoordinateQ
  have hki2 : (k.val:ℚ)*2-(i.val:ℚ)*2≠0 := by
    convert mul_ne_zero hki (by norm_num : (2:ℚ)≠0) using 1 <;> ring
  field_simp [hki,hki2]
  <;> ring_nf
  <;> field_simp [hki,hki2]
  <;> ring

#print axioms quadratic_nonneg
#print axioms vertex_energy_eq
end BecknerOnofri.HighDim.Spin
