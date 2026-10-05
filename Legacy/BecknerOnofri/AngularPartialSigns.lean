import Legacy.BecknerOnofri.AngularSpectralIntertwining
import Legacy.BecknerOnofri.EulerUnitProfiles
import Legacy.BecknerOnofri.PositiveOperatorNeumann

/-! Genuine nonnegativity of the first angular Jacobi vectors, with the
coefficient sequence and the real L2 representatives identified. -/
noncomputable section
namespace Legacy.BecknerOnofri.AngularPartialSigns
open MeasureTheory Set Legacy.TorusEndpoint TorusSobolev RadialWiener AngularMixedTerms AngularMixedL2
open SubcriticalAttainment SubcriticalEuler SmoothFourier WienerFourier SteinerSelection

theorem weight_pos {d : ℕ} (is : List (Fin d)) {x : Fin d → ℝ}
    (hx : ∀ i, x i ∈ Ioo 0 Real.pi) : 0 < weight is x := by
  apply Finset.prod_pos
  intro i _
  exact pow_pos (Real.sin_pos_of_pos_of_lt_pi (hx i).1 (hx i).2) _

theorem vector_nonnegative {d : ℕ} (a : Frequency d → ℂ)
    (ha : ∀ m : ℕ, RadialSummable a m) (is : List (Fin d))
    (hpos : ∀ y ∈ FiniteDifferences.closedCube d, 0 ≤ FiniteDifferences.mixedPartial is
      (fun z => ChebyshevProfile.profile a (CubeProfileMonotone.fromUnitCube z)) y) :
    PositiveOperatorNeumann.Nonnegative (JacobiTensor.measure d) (vector a is) := by
  filter_upwards [vector_ae a ha is, JacobiTensor.ae_mem_box d] with x he hx
  rw [he]
  exact mul_nonneg (weight_pos is hx).le (hpos _ (angularCube_mem x))

theorem first_potential_nonnegative {d : ℕ} (hd : 0 < d) {b Ab A : ℝ}
    (hR : RoughExponentialBound d b Ab) (hA : 0 < A) {u : TorusL2 d} (hu : Admissible u)
    (hmax : ∀ v : TorusL2 d, Admissible v → functional A v ≤ functional A u)
    (hSt : Steiner (fun x => (representative u x).re)) (i : Fin d) :
    PositiveOperatorNeumann.Nonnegative (JacobiTensor.measure d) (vector (fourierIsometry d u) [i]) :=
  vector_nonnegative _ (maximizer_radialSummable hd hR hA hu hmax) [i]
    (fun _ hy => EulerUnitProfiles.potential_first_nonneg hd hR hA hu hmax hSt i hy)

theorem first_density_nonnegative {d : ℕ} (hd : 0 < d) {b Ab A : ℝ}
    (hR : RoughExponentialBound d b Ab) (hA : 0 < A) {u : TorusL2 d} (hu : Admissible u)
    (hmax : ∀ v : TorusL2 d, Admissible v → functional A v ≤ functional A u)
    (hSt : Steiner (smoothGibbsValue u)) (i : Fin d) :
    PositiveOperatorNeumann.Nonnegative (JacobiTensor.measure d)
      (vector (densityFourier (gibbsValue u)) [i]) :=
  vector_nonnegative _ (maximizer_density_radialSummable hd hR hA hu hmax) [i]
    (fun _ hy => EulerUnitProfiles.density_first_nonneg hd hR hA hu hmax hSt i hy)

#print axioms first_potential_nonnegative
#print axioms first_density_nonnegative
end Legacy.BecknerOnofri.AngularPartialSigns
