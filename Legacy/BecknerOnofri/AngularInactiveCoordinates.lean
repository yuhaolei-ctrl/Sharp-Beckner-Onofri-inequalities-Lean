module

public import Legacy.BecknerOnofri.AngularCubeOrder
public import Legacy.BecknerOnofri.ProfilePartialSymmetry

@[expose] public section

/-! Inactive first angular directions annihilate every actual higher mixed
derivative that contains them. -/
noncomputable section
namespace Legacy.BecknerOnofri.AngularInactiveCoordinates
open MeasureTheory Legacy.TorusEndpoint RadialWiener AngularMixedTerms AngularMixedL2 FiniteDifferences

theorem vector_zero_of_partial_zero {d : ℕ} (a : Frequency d → ℂ)
    (ha : ∀ m : ℕ, RadialSummable a m) (is : List (Fin d))
    (hz : ∀ y ∈ closedCube d,
      mixedPartial is (fun z => ChebyshevProfile.profile a (CubeProfileMonotone.fromUnitCube z)) y = 0) :
    vector a is = 0 := by
  apply Lp.ext
  filter_upwards [vector_ae a ha is, Lp.coeFn_zero ℝ 2 (JacobiTensor.measure d)] with x he h0
  rw [he, hz _ (angularCube_mem x), mul_zero, h0]
  rfl

theorem vector_eq_zero_iff {d : ℕ} (a : Frequency d → ℂ)
    (ha : ∀ m : ℕ, RadialSummable a m) (is : List (Fin d)) :
    vector a is = 0 ↔ ∀ y ∈ closedCube d,
      mixedPartial is (fun z => ChebyshevProfile.profile a (CubeProfileMonotone.fromUnitCube z)) y = 0 :=
  ⟨AngularCubeOrder.mixedPartial_zero_of_vector a ha is, vector_zero_of_partial_zero a ha is⟩

theorem vector_zero_of_inactive_first {d : ℕ} (a : Frequency d → ℂ)
    (ha : ∀ m : ℕ, RadialSummable a m) (i : Fin d) (hi : vector a [i] = 0)
    (is : List (Fin d)) (his : i ∈ is) : vector a is = 0 := by
  apply vector_zero_of_partial_zero a ha is
  intro y hy
  exact ProfilePartialSymmetry.inactive_coordinate a ha i
    (AngularCubeOrder.mixedPartial_zero_of_vector a ha [i] hi) is his hy

#print axioms vector_zero_of_inactive_first
end Legacy.BecknerOnofri.AngularInactiveCoordinates
