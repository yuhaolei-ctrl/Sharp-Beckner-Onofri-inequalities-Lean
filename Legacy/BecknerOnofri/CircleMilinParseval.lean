module

public import Legacy.BecknerOnofri.CircleMilinSeries

@[expose] public section

/-! Parseval for the genuine one-sided analytic exponential, including its
Lebesgue integral and the complete finite-word coefficients. -/
noncomputable section
open MeasureTheory Legacy.TorusEndpoint
open scoped BigOperators
namespace Legacy.BecknerOnofri.CircleMilin
set_option maxHeartbeats 1200000

theorem exponential_continuous (a : ℕ → ℂ) (ha : Summable (fun j => ‖a j‖)) :
    Continuous (fun x => Complex.exp (analyticSeries a x)) := by
  have hh : (fun x => Complex.exp (analyticSeries a x)) =
      absoluteFourierSeries (fullExponentialCoefficient a) := funext (fun x => (exponential_series a ha x).symm)
  rw [hh]
  exact absoluteFourierSeries_continuous _ (fullExponentialCoefficient_summable a ha)

def exponentialMap (a : ℕ → ℂ) (ha : Summable (fun j => ‖a j‖)) : C(Torus 1,ℂ) :=
  ⟨_,exponential_continuous a ha⟩

theorem full_exponential_parseval (a : ℕ → ℂ) (ha : Summable (fun j => ‖a j‖)) :
    HasSum (fun k => ‖fullExponentialCoefficient a k‖^2)
      (∫ x, Real.exp (2*(analyticSeries a x).re) ∂torusMeasure 1) := by
  let f := exponentialMap a ha
  let v := f.toLp 2 (torusMeasure 1) ℂ
  have hp : HasSum (fun k : Frequency 1 => ‖UnitAddTorus.mFourierCoeff v k‖^2)
      (∫ x, ‖v x‖^2 ∂torusMeasure 1) := UnitAddTorus.hasSum_sq_mFourierCoeff v
  have heq : v =ᵐ[torusMeasure 1] (fun x => Complex.exp (analyticSeries a x)) :=
    ContinuousMap.coeFn_toLp _ _
  have he : (fun k => ‖UnitAddTorus.mFourierCoeff v k‖^2) =
      (fun k => ‖fullExponentialCoefficient a k‖^2) := by
    funext k
    have hcoeff : UnitAddTorus.mFourierCoeff v k =
        UnitAddTorus.mFourierCoeff (fun x => Complex.exp (analyticSeries a x)) k := by
      apply integral_congr_ae
      filter_upwards [heq] with x hx
      rw [hx]
    rw [hcoeff, exponential_fourier a ha]
  have hi : (∫ x, ‖v x‖^2 ∂torusMeasure 1) =
      ∫ x, Real.exp (2*(analyticSeries a x).re) ∂torusMeasure 1 := by
    apply integral_congr_ae
    filter_upwards [heq] with x hx
    rw [hx,Complex.norm_exp,← Real.exp_nat_mul]
    norm_num
  rw [← hi]
  exact hp.congr_fun (fun k => (congrFun he k).symm)

theorem bCoeff_sq_summable (a : ℕ → ℂ) (ha0 : a 0 = 0)
    (ha : Summable (fun j => ‖a j‖)) : Summable (fun n => ‖bCoeff a n‖^2) := by
  have hn : Function.Injective (fun n : ℕ => CircleEquality.frequency (n : ℤ)) := by
    intro i j h
    exact Int.ofNat.inj (congrFun h 0)
  have hh := (full_exponential_parseval a ha).summable.comp_injective hn
  simpa only [Function.comp_def, fullExponentialCoefficient_nat a ha0] using hh

theorem exponential_parseval (a : ℕ → ℂ) (ha0 : a 0 = 0)
    (ha : Summable (fun j => ‖a j‖)) :
    (∫ x, Real.exp (2*(analyticSeries a x).re) ∂torusMeasure 1) = ∑' n, ‖bCoeff a n‖^2 := by
  rw [← (full_exponential_parseval a ha).tsum_eq]
  rw [← CosineMixtureAxis.frequencyOneEquivInt.symm.tsum_eq (fun k => ‖fullExponentialCoefficient a k‖^2)]
  change (∑' j : ℤ, ‖fullExponentialCoefficient a (CircleEquality.frequency j)‖^2) = _
  have hp : Summable (fun n : ℕ => ‖fullExponentialCoefficient a (CircleEquality.frequency n)‖^2) := by
    simpa only [fullExponentialCoefficient_nat a ha0] using bCoeff_sq_summable a ha0 ha
  have hn : Summable (fun n : ℕ => ‖fullExponentialCoefficient a (CircleEquality.frequency (-(n+1 : ℤ)))‖^2) := by
    simp only [fullExponentialCoefficient_negative,norm_zero,zero_pow (by decide : 2 ≠ 0)]
    exact summable_zero
  rw [tsum_of_nat_of_neg_add_one hp hn]
  simp only [fullExponentialCoefficient_nat a ha0,fullExponentialCoefficient_negative,
    norm_zero,zero_pow (by decide : 2 ≠ 0),tsum_zero,add_zero]

theorem exponential_parseval_hasSum (a : ℕ → ℂ) (ha0 : a 0 = 0)
    (ha : Summable (fun j => ‖a j‖)) :
    HasSum (fun n => ‖bCoeff a n‖^2) (∫ x, Real.exp (2*(analyticSeries a x).re) ∂torusMeasure 1) := by
  rw [exponential_parseval a ha0 ha]
  exact (bCoeff_sq_summable a ha0 ha).hasSum

theorem exponential_integrable (a : ℕ → ℂ) (ha : Summable (fun j => ‖a j‖)) :
    Integrable (fun x => Real.exp (2*(analyticSeries a x).re)) (torusMeasure 1) := by
  have hh : (fun x => Real.exp (2*(analyticSeries a x).re)) =
      (fun x => ‖Complex.exp (analyticSeries a x)‖^2) := by
    funext x
    rw [Complex.norm_exp,← Real.exp_nat_mul]
    norm_num
  rw [hh]
  exact ((exponential_continuous a ha).norm.pow 2).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

#print axioms exponential_parseval
#print axioms exponential_parseval_hasSum
#print axioms exponential_integrable
end Legacy.BecknerOnofri.CircleMilin
