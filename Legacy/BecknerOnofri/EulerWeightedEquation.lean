module

public import Legacy.BecknerOnofri.EulerWeightedProfiles
public import Legacy.BecknerOnofri.AngularCubeOrder

@[expose] public section

/-! Exact weighted Euler equations in the actual angular L2 space. The first
mixed derivative is an eigenvector; all higher remainders are concrete Bell
polynomials in lower derivatives, transported through the genuine inverse. -/
noncomputable section
open Set MeasureTheory
namespace Legacy.BecknerOnofri.EulerWeightedEquation
open Legacy.TorusEndpoint TorusSobolev SubcriticalAttainment SubcriticalEuler
open WienerFourier SmoothFourier SteinerSelection FiniteDifferences
open AngularMixedTerms AngularMixedL2 JacobiTensor JacobiTensorSpectrum
open BoundedL2Multiplier MixedExponentialDerivatives PositiveOperatorNeumann

variable {d : ℕ} (hd : 0 < d) {b Ab A : ℝ}
  (hR : RoughExponentialBound d b Ab) (hA : 0 < A) {u : TorusL2 d}
  (hu : SubcriticalAttainment.Admissible u)
  (hmax : ∀ v : TorusL2 d, SubcriticalAttainment.Admissible v → functional A v ≤ functional A u)
  (hStR : Steiner (smoothGibbsValue u))

def W (is : List (Fin d)) : TensorL2 d :=
  (sqrtDensityWeight hd hR hA hu hmax hStR).operator (vector (fourierIsometry d u) is)

def S (is : List (Fin d)) (his : is ≠ []) : PositiveOperatorNeumann.Operator (JacobiTensor.measure d) :=
  (sqrtDensityWeight hd hR hA hu hmax hStR).conjugate (1/(2*A))
    (criticalInverse (countIndex is) (AngularSpectralIntertwining.countIndex_ne_zero is his))

def remainderVector (is : List (Fin d)) : TensorL2 d :=
  vector (densityFourier (gibbsValue u)) is -
    (sqrtDensityWeight hd hR hA hu hmax hStR).operator (W hd hR hA hu hmax hStR is)

include hd hR hA hu hmax hStR

theorem W_ae (is : List (Fin d)) :
    W hd hR hA hu hmax hStR is =ᵐ[JacobiTensor.measure d] fun x =>
      sqrtDensity u x * (weight is x * mixedPartial is (EulerUnitProfiles.potential u) (angularCube x)) := by
  filter_upwards [(sqrtDensityWeight hd hR hA hu hmax hStR).operator_ae (vector (fourierIsometry d u) is),
    vector_ae (fourierIsometry d u) (maximizer_radialSummable hd hR hA hu hmax) is] with x hw hv
  change ((sqrtDensityWeight hd hR hA hu hmax hStR).operator (vector (fourierIsometry d u) is)) x = _
  rw [hw,hv]
  rfl

theorem remainderVector_ae (hStU : Steiner (fun x => (representative u x).re))
    (is : List (Fin d)) (his : is ≠ []) :
    remainderVector hd hR hA hu hmax hStR is =ᵐ[JacobiTensor.measure d] fun x =>
      weight is x * rhoAngular u x *
        evalTerms (EulerUnitProfiles.potential u) (remainderTerms is) (angularCube x) := by
  filter_upwards [Lp.coeFn_sub (vector (densityFourier (gibbsValue u)) is)
      ((sqrtDensityWeight hd hR hA hu hmax hStR).operator (W hd hR hA hu hmax hStR is)),
    vector_ae (densityFourier (gibbsValue u)) (maximizer_density_radialSummable hd hR hA hu hmax) is,
    (sqrtDensityWeight hd hR hA hu hmax hStR).operator_ae (W hd hR hA hu hmax hStR is),
    W_ae hd hR hA hu hmax hStR is] with x hs hv ho hw
  change (vector (densityFourier (gibbsValue u)) is -
    (sqrtDensityWeight hd hR hA hu hmax hStR).operator (W hd hR hA hu hmax hStR is)) x = _
  rw [hs]
  change vector (densityFourier (gibbsValue u)) is x -
    ((sqrtDensityWeight hd hR hA hu hmax hStR).operator (W hd hR hA hu hmax hStR is)) x = _
  rw [hv,ho,hw]
  change weight is x * mixedPartial is (EulerUnitProfiles.density u) (angularCube x) -
    sqrtDensity u x * (sqrtDensity u x * (weight is x * mixedPartial is (EulerUnitProfiles.potential u) (angularCube x))) = _
  rw [normalized_gibbs_mixed hd hR hA hu hmax hStR hStU is his (angularCube_mem x)]
  change weight is x * (rhoAngular u x * (_ + _)) - _ = _
  have hs := sqrtDensity_sq hd hR hA hu hmax hStR x
  linear_combination -(weight is x * mixedPartial is (EulerUnitProfiles.potential u) (angularCube x))*hs

/-- The actual weighted Euler equation, including its complete lower-order Bell remainder. -/
theorem weighted_remainder_equation (is : List (Fin d)) (his : is ≠ []) :
    W hd hR hA hu hmax hStR is - S hd hR hA hu hmax hStR is his (W hd hR hA hu hmax hStR is) =
      (1/(2*A)) • (sqrtDensityWeight hd hR hA hu hmax hStR).operator
        (criticalInverse (countIndex is) (AngularSpectralIntertwining.countIndex_ne_zero is his)
          (remainderVector hd hR hA hu hmax hStR is)) := by
  have he := congrArg (sqrtDensityWeight hd hR hA hu hmax hStR).operator
    (AngularSpectralIntertwining.maximizer_inverse_equation hd hR hA hu hmax is his)
  rw [map_smul] at he
  change W hd hR hA hu hmax hStR is = _ at he
  rw [remainderVector,map_sub,map_sub,smul_sub]
  rw [← he]
  rfl

theorem remainderVector_single (hStU : Steiner (fun x => (representative u x).re)) (i : Fin d) :
    remainderVector hd hR hA hu hmax hStR [i] = 0 := by
  apply Lp.ext
  filter_upwards [remainderVector_ae hd hR hA hu hmax hStR hStU [i] (by simp),
    Lp.coeFn_zero ℝ 2 (JacobiTensor.measure d)] with x hx hz
  rw [hx,hz]
  simp [remainderTerms_single,evalTerms]

/-- The first angular mixed derivative satisfies the genuine eigenvalue-one equation. -/
theorem first_eigen_equation (hStU : Steiner (fun x => (representative u x).re)) (i : Fin d) :
    S hd hR hA hu hmax hStR [i] (by simp) (W hd hR hA hu hmax hStR [i]) =
      W hd hR hA hu hmax hStR [i] := by
  have h := weighted_remainder_equation hd hR hA hu hmax hStR [i] (by simp)
  rw [remainderVector_single hd hR hA hu hmax hStR hStU i,map_zero,map_zero,smul_zero] at h
  exact (sub_eq_zero.mp h).symm

theorem remainderVector_nonnegative (hStU : Steiner (fun x => (representative u x).re))
    (is : List (Fin d)) (his : is ≠ [])
    (hlower : ∀ js : List (Fin d), 0 < js.length → js.length < is.length →
      ∀ y ∈ closedCube d, 0 ≤ mixedPartial js (EulerUnitProfiles.potential u) y) :
    Nonnegative (JacobiTensor.measure d) (remainderVector hd hR hA hu hmax hStR is) := by
  filter_upwards [remainderVector_ae hd hR hA hu hmax hStR hStU is his,ae_mem_box d] with x he hx
  rw [he]
  exact mul_nonneg (mul_nonneg (angularWeight_nonnegative is hx)
    (rhoAngular_pos hd hR hA hu hmax hStR x).le)
    (bell_remainder_nonneg _ is _ (fun js hj hn => hlower js hj hn _ (angularCube_mem x)))

theorem weighted_remainder_nonnegative (hStU : Steiner (fun x => (representative u x).re))
    (is : List (Fin d)) (his : is ≠ [])
    (hlower : ∀ js : List (Fin d), 0 < js.length → js.length < is.length →
      ∀ y ∈ closedCube d, 0 ≤ mixedPartial js (EulerUnitProfiles.potential u) y)
    (hInv : Positive (JacobiTensor.measure d)
      (criticalInverse (countIndex is) (AngularSpectralIntertwining.countIndex_ne_zero is his))) :
    Nonnegative (JacobiTensor.measure d)
      (W hd hR hA hu hmax hStR is - S hd hR hA hu hmax hStR is his (W hd hR hA hu hmax hStR is)) := by
  rw [weighted_remainder_equation hd hR hA hu hmax hStR is his]
  have hw : ∀ᵐ x ∂JacobiTensor.measure d, 0 ≤ (sqrtDensityWeight hd hR hA hu hmax hStR).value x :=
    ae_of_all _ (fun x => (sqrtDensity_pos hd hR hA hu hmax hStR x).le)
  have hp := (sqrtDensityWeight hd hR hA hu hmax hStR).operator_positive hw _
    (hInv _ (remainderVector_nonnegative hd hR hA hu hmax hStR hStU is his hlower))
  filter_upwards [hp, Lp.coeFn_smul (1/(2*A))
    ((sqrtDensityWeight hd hR hA hu hmax hStR).operator
      (criticalInverse (countIndex is) (AngularSpectralIntertwining.countIndex_ne_zero is his)
        (remainderVector hd hR hA hu hmax hStR is)))] with x hx he
  rw [he]
  exact mul_nonneg (by positivity) hx

theorem W_first_nonnegative (hStU : Steiner (fun x => (representative u x).re)) (i : Fin d) :
    Nonnegative (JacobiTensor.measure d) (W hd hR hA hu hmax hStR [i]) := by
  filter_upwards [W_ae hd hR hA hu hmax hStR [i],ae_mem_box d] with x he hx
  rw [he]
  apply mul_nonneg (sqrtDensity_pos hd hR hA hu hmax hStR x).le
  apply mul_nonneg (angularWeight_nonnegative [i] hx)
  exact EulerUnitProfiles.potential_first_nonneg hd hR hA hu hmax hStU i (angularCube_mem x)


theorem S_compact (is : List (Fin d)) (his : is ≠ []) :
    IsCompactOperator (S hd hR hA hu hmax hStR is his) :=
  (sqrtDensityWeight hd hR hA hu hmax hStR).conjugate_compact _
    (criticalInverse_compact (countIndex is) (AngularSpectralIntertwining.countIndex_ne_zero is his))

theorem S_positive (is : List (Fin d)) (his : is ≠ [])
    (hInv : Positive (JacobiTensor.measure d)
      (criticalInverse (countIndex is) (AngularSpectralIntertwining.countIndex_ne_zero is his))) :
    Positive (JacobiTensor.measure d) (S hd hR hA hu hmax hStR is his) :=
  (sqrtDensityWeight hd hR hA hu hmax hStR).conjugate_positive (by positivity)
    (ae_of_all _ (fun x => (sqrtDensity_pos hd hR hA hu hmax hStR x).le)) hInv


theorem S_symmetric (is : List (Fin d)) (his : is ≠ []) :
    (S hd hR hA hu hmax hStR is his).IsSymmetric :=
  (sqrtDensityWeight hd hR hA hu hmax hStR).conjugate_symmetric _
    (inversePower_symmetric (countIndex is) (AngularSpectralIntertwining.countIndex_ne_zero is his) _ _)

theorem vector_nonnegative_of_W (is : List (Fin d))
    (hW : Nonnegative (JacobiTensor.measure d) (W hd hR hA hu hmax hStR is)) :
    Nonnegative (JacobiTensor.measure d) (vector (fourierIsometry d u) is) :=
  (sqrtDensityWeight hd hR hA hu hmax hStR).nonnegative_of_operator
    (ae_of_all _ (sqrtDensity_pos hd hR hA hu hmax hStR)) hW

theorem mixedPartial_nonnegative_of_W (is : List (Fin d))
    (hW : Nonnegative (JacobiTensor.measure d) (W hd hR hA hu hmax hStR is)) :
    ∀ y ∈ closedCube d, 0 ≤ mixedPartial is (EulerUnitProfiles.potential u) y :=
  AngularCubeOrder.mixedPartial_nonnegative_of_vector (fourierIsometry d u)
    (maximizer_radialSummable hd hR hA hu hmax) is
    (vector_nonnegative_of_W hd hR hA hu hmax hStR is hW)

theorem sqrtDensity_operator_injective :
    Function.Injective (sqrtDensityWeight hd hR hA hu hmax hStR).operator := by
  intro f g he
  apply Lp.ext
  filter_upwards [(sqrtDensityWeight hd hR hA hu hmax hStR).operator_ae f,
    (sqrtDensityWeight hd hR hA hu hmax hStR).operator_ae g] with x hf hg
  have h := congrArg (fun v : TensorL2 d => v x) he
  rw [hf,hg] at h
  exact mul_left_cancel₀ (sqrtDensity_pos hd hR hA hu hmax hStR x).ne' h

theorem W_eq_zero_iff (is : List (Fin d)) :
    W hd hR hA hu hmax hStR is = 0 ↔ vector (fourierIsometry d u) is = 0 := by
  change (sqrtDensityWeight hd hR hA hu hmax hStR).operator (vector (fourierIsometry d u) is) = 0 ↔ _
  exact map_eq_zero_iff _ (sqrtDensity_operator_injective hd hR hA hu hmax hStR)

#print axioms first_eigen_equation
#print axioms weighted_remainder_equation
#print axioms weighted_remainder_nonnegative
end Legacy.BecknerOnofri.EulerWeightedEquation
