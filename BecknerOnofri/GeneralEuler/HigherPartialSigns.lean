import BecknerOnofri.GeneralEuler.Regularity
import BecknerOnofri.GeneralEuler.WeightedEquation
import Legacy.BecknerOnofri.AngularInactiveCoordinates

/-! Strong induction for actual mixed derivatives of a smooth Steiner Euler pair.
The inactive-coordinate case is settled by equality of actual derivatives.
The active case uses the positive Neumann inverse of the actual weighted
operator. Operator positivity and strict norm estimates are explicit inputs
to this assembly lemma and are supplied by Mellin kernel comparison. -/
noncomputable section
open MeasureTheory
open Legacy.BecknerOnofri
namespace BecknerOnofri.GeneralEuler.HigherPartialSigns
open Legacy.TorusEndpoint TorusSobolev SubcriticalAttainment SubcriticalEuler
open WienerFourier SmoothFourier SteinerSelection FiniteDifferences
open AngularMixedTerms AngularMixedL2 JacobiTensor JacobiTensorSpectrum
open BecknerOnofri.GeneralEuler.WeightedEquation PositiveOperatorNeumann

variable {d : ℕ} (hd : 0 < d) {b Ab A : ℝ}
  (hR : RoughExponentialBound d b Ab) (hA : 0 < A) {u : TorusL2 d}
  (hu : SubcriticalAttainment.Admissible u)
  (hE : Regularity.Data A u)
  (hStR : Steiner (smoothGibbsValue u))
  (hStU : Steiner (fun x => (representative u x).re))

include hd hR hA hu hE hStR
theorem W_zero_of_inactive_first (i : Fin d)
    (hi : W hd hR hA hu hE hStR [i] = 0) (is : List (Fin d)) (his : i ∈ is) :
    W hd hR hA hu hE hStR is = 0 := by
  apply (W_eq_zero_iff hd hR hA hu hE hStR is).mpr
  exact AngularInactiveCoordinates.vector_zero_of_inactive_first (fourierIsometry d u)
    (Regularity.radialSummable hd hR hA hu hE) i
    ((W_eq_zero_iff hd hR hA hu hE hStR [i]).mp hi) is his

include hStU
theorem mixedPartials_nonnegative
    (hInv : ∀ (is : List (Fin d)) (his : is ≠ []),
      Positive (JacobiTensor.measure d)
        (criticalInverse (countIndex is) (BecknerOnofri.GeneralEuler.SpectralIntertwining.countIndex_ne_zero is his)))
    (hnorm : ∀ (is : List (Fin d)) (his : is ≠ []), 1 < is.length →
      ∀ i ∈ is, W hd hR hA hu hE hStR [i] ≠ 0 →
        ‖S hd hR hA hu hE hStR is his‖ < 1)
    (is : List (Fin d)) (his : is ≠ []) :
    ∀ y ∈ closedCube d, 0 ≤ mixedPartial is (BecknerOnofri.GeneralEuler.UnitProfiles.potential u) y := by
  have h : ∀ n : ℕ, ∀ js : List (Fin d), js.length = n → js ≠ [] →
      ∀ y ∈ closedCube d, 0 ≤ mixedPartial js (BecknerOnofri.GeneralEuler.UnitProfiles.potential u) y := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro js hlen hjs
      cases js with
      | nil => exact (hjs rfl).elim
      | cons i ks =>
        cases ks with
        | nil =>
          intro y hy
          exact BecknerOnofri.GeneralEuler.UnitProfiles.potential_first_nonneg hd hR hA hu hE hStU i hy
        | cons j ls =>
          let js := i :: j :: ls
          have hjs0 : js ≠ [] := by simp [js]
          have hlong : 1 < js.length := by simp [js]
          have hi : i ∈ js := by simp [js]
          apply mixedPartial_nonnegative_of_W hd hR hA hu hE hStR js
          by_cases hzero : W hd hR hA hu hE hStR [i] = 0
          · rw [W_zero_of_inactive_first hd hR hA hu hE hStR i hzero js hi]
            filter_upwards [Lp.coeFn_zero ℝ 2 (JacobiTensor.measure d)] with x hx
            simp only [hx, Pi.zero_apply, le_refl]
          · apply nonnegative_of_sub (JacobiTensor.measure d)
              (S_positive hd hR hA hu hE hStR js hjs0 (hInv js hjs0))
              (hnorm js hjs0 hlong i hi hzero)
              (W hd hR hA hu hE hStR js)
            apply weighted_remainder_nonnegative hd hR hA hu hE hStR hStU js hjs0
            · intro ks hkpos hklen y hy
              apply ih ks.length (by simpa only [← hlen] using hklen) ks rfl
              · intro he
                simp [he] at hkpos
              · exact hy
            · exact hInv js hjs0
  exact h is.length is rfl his

#print axioms W_zero_of_inactive_first
#print axioms mixedPartials_nonnegative
end BecknerOnofri.GeneralEuler.HigherPartialSigns
