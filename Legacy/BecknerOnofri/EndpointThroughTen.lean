module

public import Legacy.BecknerOnofri.EulerCriticalComparison
public import Legacy.BecknerOnofri.EulerHigherPartialSigns
public import Legacy.BecknerOnofri.SteinerEndpointReduction

@[expose] public section

/-! The unconditional finite-entropy Beckner endpoint through dimension ten.
Every analytic input to the high-order Steiner derivative induction is now
proved for the actual Jacobi operators, and the strict-counterexample
reduction closes the endpoint for the full finite-entropy class. -/
noncomputable section
namespace Legacy.BecknerOnofri
open MeasureTheory Legacy.TorusEndpoint TorusSobolev SubcriticalAttainment SubcriticalEuler
open WienerFourier SmoothFourier SteinerSelection FiniteDifferences
open AngularMixedTerms JacobiTensor JacobiTensorSpectrum EulerWeightedEquation

/-- All nonempty actual mixed derivatives of a Steiner Euler maximizer are
nonnegative on the entire closed unit cube, including its boundary. -/
theorem steiner_maximizer_mixedPartials {d : ℕ} (hd : 0 < d) {b Ab A : ℝ}
    (hR : RoughExponentialBound d b Ab) (hA : 0 < A) {u : TorusL2 d}
    (hu : SubcriticalAttainment.Admissible u)
    (hmax : ∀ v : TorusL2 d, SubcriticalAttainment.Admissible v → functional A v ≤ functional A u)
    (hStR : Steiner (smoothGibbsValue u))
    (hStU : Steiner (fun x => (representative u x).re))
    (is : List (Fin d)) (his : is ≠ []) :
    ∀ y ∈ closedCube d, 0 ≤ mixedPartial is (EulerUnitProfiles.potential u) y :=
  EulerHigherPartialSigns.mixedPartials_nonnegative hd hR hA hu hmax hStR hStU
    (fun js hjs => EulerCriticalComparison.criticalInverse_positive (countIndex js)
      (AngularSpectralIntertwining.countIndex_ne_zero js hjs))
    (EulerCriticalComparison.higher_norm_lt_one hd hR hA hu hmax hStR hStU) is his

theorem higherSteinerEulerPartials {d : ℕ} (hd : 0 < d) (hd10 : d ≤ 10) :
    SteinerEndpointReduction.HigherSteinerEulerPartials d := by
  intro A hA u hu hmax hStR hStU is hlong
  have hC : 0 < endpointConstant d := div_pos (Nat.cast_pos.mpr hd) (endpointSigma_pos hd)
  have hA0 : 0 < A := (by positivity : 0 < 1/(4*endpointConstant d)).trans hA
  have hR := roughExponentialBound hd (by positivity : 0 < endpointConstant d/2)
    (by linarith : endpointConstant d/2 < endpointConstant d)
  exact steiner_maximizer_mixedPartials hd hR hA0 hu hmax hStR hStU is (by
    intro he
    simp [he] at hlong)

/-- The genuine endpoint for every finite-entropy probability density in
dimensions one through ten, including convergence of the Fourier energy. -/
theorem endpoint_through_ten : EndpointThroughTen :=
  SteinerEndpointReduction.throughTen_of_higher_partials
    (fun d hd2 hd10 => higherSteinerEulerPartials (by omega) hd10)

theorem endpoint_of_dimension {d : ℕ} (hd : 1 ≤ d) (hd10 : d ≤ 10) : Endpoint d :=
  endpoint_through_ten d hd hd10

/-- The endpoint coefficient is the largest valid entropy-energy coefficient. -/
theorem endpoint_isGreatest {d : ℕ} (hd : 1 ≤ d) (hd10 : d ≤ 10) :
    IsGreatest {C : ℝ | ∀ rho : ProbabilityDensity d, rho.FiniteEntropy →
      C * fourierEnergy rho ≤ densityEntropy rho.value} (endpointConstant d) :=
  ⟨fun rho hr => (endpoint_through_ten d hd hd10 rho hr).2,
    fun C hC => coefficient_le_endpointConstant (by omega) C hC⟩

/-- The paper's normalized entropy form, Ent(rho) >= d * G_d(rho). -/
theorem normalized_entropy_endpoint {d : ℕ} (hd : 1 ≤ d) (hd10 : d ≤ 10)
    (rho : ProbabilityDensity d) (hr : rho.FiniteEntropy) :
    (d : ℝ) * densitySpectralEnergy rho ≤ densityEntropy rho.value := by
  have h := (endpoint_through_ten d hd hd10 rho hr).2
  rw [normalized_energy]
  convert h using 1
  unfold endpointConstant
  ring

#print axioms steiner_maximizer_mixedPartials
#print axioms endpoint_through_ten
#print axioms endpoint_isGreatest
#print axioms normalized_entropy_endpoint
end Legacy.BecknerOnofri
