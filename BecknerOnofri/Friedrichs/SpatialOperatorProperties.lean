module

public import BecknerOnofri.Friedrichs.SpatialClosability

@[expose] public section

/-! Positivity, symmetry and single-valuedness of the spatial graph relation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped ContDiff
namespace BecknerOnofri.Friedrichs.SpatialForm
open Legacy.BecknerOnofri.JacobiAngular
open Legacy.BecknerOnofri.JacobiEigenfunctions (polynomial eigenfunction eigenvector eigenvector_ae_eq)

lemma angularLift_eigenvector {m : ℕ} (hm : 0<m) (n : ℕ) :
    (angularLift hm (polynomial_contDiff (polynomial m n))).1=eigenvector m n := by
  apply Lp.ext
  exact (continuous_memLp (angular_smooth m (polynomial_contDiff (polynomial m n))).continuous).coeFn_toLp.trans
    (eigenvector_ae_eq m n).symm

theorem operatorGraph_nonneg {m : ℕ} {f g : H} (h : operatorGraph m f g) :
    0 ≤ inner ℝ g f := by
  obtain ⟨p,v,hc,he⟩ := operatorGraph_energy h
  rw [← he]
  positivity

theorem operatorGraph_symmetric {m : ℕ} {f g h k : H}
    (hfg : operatorGraph m f g) (hhk : operatorGraph m h k) :
    inner ℝ g h=inner ℝ f k := by
  obtain ⟨p,v,hc,ht⟩ := (operatorGraph_iff_closed_tests m f g).mp hfg
  obtain ⟨q,w,hc',ht'⟩ := (operatorGraph_iff_closed_tests m h k).mp hhk
  rw [← ht _ hc',formPairing_comm,ht' _ hc,real_inner_comm]

theorem operatorGraph_unique {m : ℕ} (hm : 0<m) {f g h : H}
    (hfg : operatorGraph m f g) (hfh : operatorGraph m f h) : g=h := by
  obtain ⟨p,v,hc,ht⟩ := (operatorGraph_iff_closed_tests m f g).mp hfg
  obtain ⟨q,w,hc',ht'⟩ := (operatorGraph_iff_closed_tests m f h).mp hfh
  have hp := derivative_component_unique hc hc' rfl
  have hv := potential_component_unique hc hc' rfl
  change p=q at hp
  change v=w at hv
  subst q
  subst w
  apply sub_eq_zero.mp
  apply Legacy.BecknerOnofri.JacobiEigenfunctions.eq_zero_of_orthogonal_eigenvector (g-h) m
  intro n
  have hg := ht _ (angular_mem_formClosure hm (polynomial_contDiff (polynomial m n)))
  have hh := ht' _ (angular_mem_formClosure hm (polynomial_contDiff (polynomial m n)))
  rw [angularLift_eigenvector hm n] at hg hh
  rw [inner_sub_left,← hg,← hh,sub_self]

#print axioms operatorGraph_unique
end BecknerOnofri.Friedrichs.SpatialForm
