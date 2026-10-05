import Legacy.BecknerOnofri.ChebyshevMixedSeries

/-! Actual mixed partials of the closed cosine profile depend only on the
coordinate multiplicities. A coordinate that is identically inactive stays
zero in every higher derivative containing that coordinate. -/
noncomputable section
namespace Legacy.BecknerOnofri.ProfilePartialSymmetry
open Set Legacy.TorusEndpoint RadialWiener FiniteDifferences ChebyshevMixedSeries

theorem term_perm {d : ℕ} (a : Frequency d → ℂ) {is js : List (Fin d)}
    (hp : is.Perm js) (k : Frequency d) (y : Space d) : term a is k y = term a js k y := by
  have he : TensorPolynomialDerivatives.iteratePolynomials (polynomials k) is =
      TensorPolynomialDerivatives.iteratePolynomials (polynomials k) js := by
    funext i
    simp only [TensorPolynomialDerivatives.iteratePolynomials, hp.count_eq]
  simp only [term, hp.length_eq, he]

theorem mixedPartial_perm {d : ℕ} (a : Frequency d → ℂ)
    (ha : ∀ m : ℕ, RadialSummable a m) {is js : List (Fin d)} (hp : is.Perm js)
    {y : Space d} (hy : y ∈ closedCube d) :
    mixedPartial is (fun z => ChebyshevProfile.profile a (CubeProfileMonotone.fromUnitCube z)) y =
      mixedPartial js (fun z => ChebyshevProfile.profile a (CubeProfileMonotone.fromUnitCube z)) y := by
  rw [mixedPartial_profile a ha is hy, mixedPartial_profile a ha js hy]
  exact tsum_congr (fun k => term_perm a hp k y)

theorem mixedPartial_zero {d : ℕ} (is : List (Fin d)) :
    mixedPartial is (fun _ : Space d => (0 : ℝ)) = fun _ => 0 := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    change mixedPartial is (coordinateDerivative i (fun _ => 0)) = _
    have he : coordinateDerivative i (fun _ : Space d => (0 : ℝ)) = fun _ => 0 :=
      funext (fun y => MixedExponentialDerivatives.coordinateDerivative_const i 0 y)
    rw [he, ih]

theorem inactive_coordinate {d : ℕ} (a : Frequency d → ℂ)
    (ha : ∀ m : ℕ, RadialSummable a m) (i : Fin d)
    (hi : ∀ y ∈ closedCube d, coordinateDerivative i
      (fun z => ChebyshevProfile.profile a (CubeProfileMonotone.fromUnitCube z)) y = 0)
    (is : List (Fin d)) (his : i ∈ is) {y : Space d} (hy : y ∈ closedCube d) :
    mixedPartial is (fun z => ChebyshevProfile.profile a (CubeProfileMonotone.fromUnitCube z)) y = 0 := by
  rw [mixedPartial_perm a ha (List.perm_cons_erase his) hy, mixedPartial_cons]
  rw [NormalizedExponentialPartials.mixedPartial_congr (is.erase i) hi hy, mixedPartial_zero]

#print axioms mixedPartial_perm
#print axioms inactive_coordinate
end Legacy.BecknerOnofri.ProfilePartialSymmetry
