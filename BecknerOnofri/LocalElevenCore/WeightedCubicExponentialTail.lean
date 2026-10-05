module

public import BecknerOnofri.WeightedExponentialTaylorTail
public import BecknerOnofri.LocalElevenCore.WeightedExponentialRemainder

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped BigOperators
namespace BecknerOnofri.HighDim.LocalEleven.WeightedCubicExponentialTail
open ContinuousGibbs ContinuousFirstShell GraphRegularity WeightedExponentialRemainder
open Legacy.TorusEndpoint Legacy.BecknerOnofri.WienerFourier
open Legacy.BecknerOnofri.WeightedWiener Legacy.BecknerOnofri.RadialWiener
open BecknerOnofri.OnsetWienerBounds

lemma series_eq {d : ℕ} (u : Space d) (hu : Summable (fun k => ‖coefficient k u‖)) :
    absoluteFourierSeries (fun k => coefficient k u) = fun x => (u x : ℂ) := by
  haveI : (Legacy.TorusEndpoint.torusMeasure d).IsOpenPosMeasure := by
    rw [Legacy.TorusEndpoint.torusMeasure_explicit]
    infer_instance
  exact Measure.eq_of_ae_eq
    ((representative_ae_eq (toL2 d u) hu).trans (toL2_ae u))
    (representative_continuous (toL2 d u) hu) (Complex.continuous_ofReal.comp u.continuous)

lemma coefficient_power {d : ℕ} (u : Space d) (hu : Summable (fun k => ‖coefficient k u‖))
    (n : ℕ) (k : Frequency d) : coefficient k (u^n)=
      convolutionPower (fun k => coefficient k u) n k := by
  have he : absoluteFourierSeries (convolutionPower (fun k => coefficient k u) n)=
      fun x => ((u x:ℂ)^n) := by
    funext x
    rw [convolutionPower_series _ hu,series_eq u hu]
  rw [← absoluteFourierSeries_coefficient _ (convolutionPower_norm_summable _ hu n),he,
    coefficient_integral]
  simp only [UnitAddTorus.mFourierCoeff,smul_eq_mul,ContinuousMap.pow_apply,Complex.ofReal_pow]
  rfl

def tailThree {d : ℕ} (u : Space d) : Space d := exponential u-1-u-(1/2:ℝ) • u^2

lemma coefficient_tailThree {d : ℕ} (u : Space d)
    (hu : Summable (fun k => ‖coefficient k u‖)) (k : Frequency d) :
    coefficient k (tailThree u)=
      BecknerOnofri.WeightedExponentialTaylorTail.tailCoefficients 3 (fun k => coefficient k u) k := by
  rw [BecknerOnofri.WeightedExponentialTaylorTail.tailCoefficients_eq 3 _ hu,
    tailThree,map_sub,map_sub,map_sub,map_smul,coefficient_exponential u hu,
    coefficient_one,coefficient_power u hu]
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,
    BecknerOnofri.WeightedExponentialRemainder.convolutionPower_one _ hu,
    show convolutionPower (fun k => coefficient k u) 0 k=(if k=0 then 1 else 0) from rfl]
  norm_num [Complex.real_smul]
  ring

lemma tailThree_radial {d : ℕ} (m : ℕ) (u : Space d) (hu : Radial m u) :
    Radial m (tailThree u) := by
  have h0 := summable_norm (radialWeight_isWeight m) hu
  simpa only [Radial,RadialSummable,coefficient_tailThree u h0] using
    BecknerOnofri.WeightedExponentialTaylorTail.tail_weighted_summable 3 (radialWeight_isWeight m)
      (fun k => coefficient k u) hu

lemma tailThree_radial_bound {d : ℕ} (m : ℕ) (u : Space d) (hu : Radial m u)
    (hM : radialSize m (fun k => coefficient k u)≤1) :
    radialSize m (fun k => coefficient k (tailThree u))≤
      (radialSize m (fun k => coefficient k u))^3 := by
  let M := radialSize m (fun k => coefficient k u)
  have h0 : 0≤M := radialSize_nonneg _ _
  have hu0 := summable_norm (radialWeight_isWeight m) hu
  have h := BecknerOnofri.WeightedExponentialTaylorTail.tail_weighted_sum_le 3
    (radialWeight_isWeight m) (fun k => coefficient k u) hu
  have hb := Real.exp_bound (x := M) (by simpa only [abs_of_nonneg h0] using hM)
    (n := 3) (by norm_num)
  have he : radialSize m (fun k => coefficient k (tailThree u))≤
      Real.exp M-(1+M+M^2/2) := by
    simpa [radialSize,coefficient_tailThree u hu0,Finset.sum_range_succ,M,div_eq_mul_inv,mul_comm] using h
  norm_num [Finset.sum_range_succ,abs_of_nonneg h0] at hb
  have hh := le_abs_self (Real.exp M-(1+M+M^2/2))
  nlinarith [pow_nonneg h0 3]

#print axioms tailThree_radial_bound
end BecknerOnofri.HighDim.LocalEleven.WeightedCubicExponentialTail
