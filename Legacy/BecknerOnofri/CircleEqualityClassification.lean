module

public import Legacy.BecknerOnofri.CircleEqualityReverseData
public import Legacy.BecknerOnofri.CircleMilinParseval
public import Legacy.BecknerOnofri.CircleEqualityPaper
public import Legacy.BecknerOnofri.EndpointEqualityCorrespondence
public import Legacy.BecknerOnofri.LowDimensionOnofri

@[expose] public section

/-! Complete reverse equality classification on the circle.  The actual
Sobolev Fourier series is connected to the convergent exponential word
series, so equality of the integrals forces the coefficient recurrence. -/
noncomputable section
open MeasureTheory Legacy.TorusEndpoint Filter
open scoped BigOperators ComplexConjugate
namespace Legacy.BecknerOnofri.CircleEquality
open TorusSobolev SubcriticalAttainment SubcriticalEuler CircleMilin
set_option maxHeartbeats 1200000

theorem analyticSeries_real_ae {u : TorusL2 1} (hu : Admissible u)
    (hs : Summable (fun k => ‖fourierIsometry 1 u k‖)) :
    (fun x => (u x).re) =ᵐ[torusMeasure 1]
      fun x => 2*(analyticSeries (positiveFourier u) x).re := by
  filter_upwards [series_positiveFourier_ae hu.1 hs] with x hx
  have h := congrArg Complex.re hx
  rw [series_eq _ (positiveFourier_summable hs) x] at h
  simpa [positiveFourier_zero hu, analyticSeries, two_mul] using h.symm

theorem partition_eq_bCoeff_sum {u : TorusL2 1} (hu : Admissible u)
    (hs : Summable (fun k => ‖fourierIsometry 1 u k‖)) :
    partition u = ∑' n, ‖bCoeff (positiveFourier u) n‖^2 := by
  calc
    partition u = ∫ x, Real.exp (2*(analyticSeries (positiveFourier u) x).re)
        ∂torusMeasure 1 := by
      apply integral_congr_ae
      filter_upwards [analyticSeries_real_ae hu hs] with x hx
      rw [hx]
    _ = _ := exponential_parseval _ (positiveFourier_zero hu) (positiveFourier_summable hs)

theorem potential_of_equality {u : TorusL2 1} (hu : Admissible u)
    (he : Real.log (partition u) = EndpointPotential.coefficient 1*criticalEnergy u) :
    ∃ z : ℂ, ∃ hz : ‖z‖ < 1, u = potential z hz := by
  have hR := EndpointPotential.rough_of_endpoint (by decide : 0<1) endpoint_one
  have hA := EndpointPotential.coefficient_pos (by decide : 0<1)
  have hmax := EndpointPotential.maximizer_of_equality (by decide : 0<1) endpoint_one hu he
  have hs := maximizer_fourier_summable (by decide : 0<1) hR hA hu hmax
  have hdata := equality_positiveFourier_data endpoint_one hu he
  let a := positiveFourier u
  have hp := pCoeff_hasSum a (weighted_positiveFourier_summable hu.2)
  have hb := bCoeff_sq_summable a (positiveFourier_zero hu) hdata.1
  have hm : (∑' n, pCoeff a n) = ∑' n, ‖bCoeff a n‖^2 := by
    rw [hp.tsum_eq, ← onofri_energy_eq hu, ← he,
      Real.exp_log (SubcriticalAttainment.partition_pos hR hu)]
    exact partition_eq_bCoeff_sum hu hs
  obtain ⟨hz, hcoeff⟩ := coefficients_of_equal_mass a hp.summable hb hm hdata.2
  refine ⟨a 1, hz, ?_⟩
  have ha : a = logarithmicCoefficient (a 1) := by
    funext n
    by_cases hn : n=0
    · subst n
      simp [a, positiveFourier_zero hu, logarithmicCoefficient]
    · exact hcoeff n (Nat.pos_of_ne_zero hn)
  apply (fourierIsometry 1).injective
  apply lp.ext
  funext k
  rw [fourier_eq_coefficient hu.1, potential_fourier hz]
  change coefficient a k = _
  exact congrArg (fun b => coefficient b k) ha

theorem potential_equality_iff {u : TorusL2 1} (hu : Admissible u) :
    Real.log (partition u) = EndpointPotential.coefficient 1*criticalEnergy u ↔
      ∃ z : ℂ, ∃ hz : ‖z‖ < 1, u = potential z hz := by
  refine ⟨potential_of_equality hu, ?_⟩
  rintro ⟨z, hz, rfl⟩
  exact potential_equality hz

#print axioms potential_of_equality
#print axioms potential_equality_iff
end Legacy.BecknerOnofri.CircleEquality
