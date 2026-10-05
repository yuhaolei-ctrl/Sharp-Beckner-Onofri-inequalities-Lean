module

public import Legacy.BecknerOnofri.CubeProfileMonotone
public import Legacy.BecknerOnofri.PositiveCosineRepresentation
public import Legacy.BecknerOnofri.BernsteinPositiveCoefficients
public import Legacy.BecknerOnofri.MixedExponentialPolynomial

@[expose] public section

/-! The actual selected Euler profiles in the unit-cube coordinates used by
the positive Taylor and mixture endpoint theorems. -/
noncomputable section
namespace Legacy.BecknerOnofri.EulerUnitProfiles
open Legacy.TorusEndpoint TorusSobolev SubcriticalAttainment SubcriticalEuler SmoothFourier
open WienerFourier SteinerSelection ChebyshevProfile CubeProfileMonotone
open scoped ContDiff

def potential {d : ℕ} (u : TorusL2 d) (y : Fin d → ℝ) : ℝ :=
  profile (fourierIsometry d u) (fromUnitCube y)

def density {d : ℕ} (u : TorusL2 d) (y : Fin d → ℝ) : ℝ :=
  profile (densityFourier (gibbsValue u)) (fromUnitCube y)

theorem quotient_surjective (d : ℕ) : Function.Surjective (@quotient d) := by
  intro x
  choose y hy using fun i => QuotientAddGroup.mk_surjective (x i)
  exact ⟨y, funext hy⟩

theorem positive_coordinate_coe (t : ℝ) :
    PositiveCosineRepresentation.coordinate (t : UnitAddCircle) =
      (1 + Real.cos (2*Real.pi*t))/2 := by
  have hn : Complex.normSq (fourier 1 (t : UnitAddCircle)) = 1 := by
    have hn' : ‖fourier 1 (t : UnitAddCircle)‖ = 1 := Circle.norm_coe _
    rw [Complex.normSq_eq_norm_sq, hn']
    norm_num
  rw [PositiveCosineRepresentation.coordinate, Complex.normSq_add]
  simp only [Complex.normSq_one, hn, one_mul, Complex.conj_re]
  have hc := CosineMomentWeight.circleCos_coe t
  change (fourier 1 (t : UnitAddCircle)).re = Real.cos (2*Real.pi*t) at hc
  rw [hc]
  ring

theorem cube_fromUnitCube_quotient {d : ℕ} (x : Fin d → ℝ) :
    fromUnitCube (fun i => ((PositiveCosineRepresentation.cube (quotient x) i : unitInterval) : ℝ)) =
      cosinePoint x := by
  funext i
  change 2*PositiveCosineRepresentation.coordinate (x i : UnitAddCircle)-1 = _
  rw [positive_coordinate_coe]
  dsimp [cosinePoint]
  ring

variable {d : ℕ} (hd : 0 < d) {b Ab A : ℝ}
  (hR : RoughExponentialBound d b Ab) (hA : 0 < A) {u : TorusL2 d}
  (hu : Admissible u)
  (hmax : ∀ v : TorusL2 d, Admissible v → functional A v ≤ functional A u)

include hd hR hA hu hmax

theorem potential_contDiffOn (hSt : Steiner (fun x => (representative u x).re)) :
    ContDiffOn ℝ ∞ (potential u) (FiniteDifferences.closedCube d) :=
  unit_profile_contDiffOn (EulerCosineProfile.potential_profile hd hR hA hu hmax hSt).1

theorem density_contDiffOn (hSt : Steiner (smoothGibbsValue u)) :
    ContDiffOn ℝ ∞ (density u) (FiniteDifferences.closedCube d) :=
  unit_profile_contDiffOn (EulerCosineProfile.density_profile hd hR hA hu hmax hSt).1

theorem potential_first_nonneg (hSt : Steiner (fun x => (representative u x).re))
    (i : Fin d) {y : Fin d → ℝ} (hy : y ∈ FiniteDifferences.closedCube d) :
    0 ≤ FiniteDifferences.coordinateDerivative i (potential u) y := by
  obtain ⟨hs, he⟩ := EulerCosineProfile.potential_profile hd hR hA hu hmax hSt
  exact first_derivative_nonneg_of_steiner hs hSt he i hy

theorem density_first_nonneg (hSt : Steiner (smoothGibbsValue u))
    (i : Fin d) {y : Fin d → ℝ} (hy : y ∈ FiniteDifferences.closedCube d) :
    0 ≤ FiniteDifferences.coordinateDerivative i (density u) y := by
  obtain ⟨hs, he⟩ := EulerCosineProfile.density_profile hd hR hA hu hmax hSt
  exact first_derivative_nonneg_of_steiner hs hSt he i hy

theorem density_eq_exp (hStU : Steiner (fun x => (representative u x).re))
    (hStR : Steiner (smoothGibbsValue u)) {y : Fin d → ℝ}
    (hy : y ∈ FiniteDifferences.closedCube d) :
    density u y = Real.exp (potential u y) / partition u :=
  profile_gibbs_identity u (EulerCosineProfile.potential_profile hd hR hA hu hmax hStU).2
    (EulerCosineProfile.density_profile hd hR hA hu hmax hStR).2 (fromUnitCube_mapsTo d hy)

theorem density_pos (hSt : Steiner (smoothGibbsValue u)) {y : Fin d → ℝ}
    (hy : y ∈ FiniteDifferences.closedCube d) : 0 < density u y := by
  have he := (EulerCosineProfile.density_profile hd hR hA hu hmax hSt).2
    (inverseCos (fromUnitCube y))
  rw [cosinePoint_inverseCos (fromUnitCube_mapsTo d hy)] at he
  change 0 < profile (densityFourier (gibbsValue u)) (fromUnitCube y)
  rw [← he]
  exact smoothGibbsValue_pos hR hu _

theorem density_representation (hSt : Steiner (smoothGibbsValue u)) (x : Torus d) :
    smoothGibbsValue u x = BernsteinPositiveCoefficients.restriction (density u)
      (PositiveCosineRepresentation.cube x) := by
  obtain ⟨z, rfl⟩ := quotient_surjective d x
  change smoothGibbsValue u (quotient z) = profile (densityFourier (gibbsValue u))
    (fromUnitCube (fun i => (PositiveCosineRepresentation.cube (quotient z) i : ℝ)))
  rw [cube_fromUnitCube_quotient]
  exact (EulerCosineProfile.density_profile hd hR hA hu hmax hSt).2 z

theorem potential_representation (hSt : Steiner (fun x => (representative u x).re)) (x : Torus d) :
    (representative u x).re = BernsteinPositiveCoefficients.restriction (potential u)
      (PositiveCosineRepresentation.cube x) := by
  obtain ⟨z, rfl⟩ := quotient_surjective d x
  change (representative u (quotient z)).re = profile (fourierIsometry d u)
    (fromUnitCube (fun i => (PositiveCosineRepresentation.cube (quotient z) i : ℝ)))
  rw [cube_fromUnitCube_quotient]
  exact (EulerCosineProfile.potential_profile hd hR hA hu hmax hSt).2 z

#print axioms density_eq_exp
#print axioms potential_first_nonneg
#print axioms density_representation
end Legacy.BecknerOnofri.EulerUnitProfiles
