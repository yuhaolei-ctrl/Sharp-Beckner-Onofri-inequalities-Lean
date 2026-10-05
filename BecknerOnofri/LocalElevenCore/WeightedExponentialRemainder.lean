module

public import BecknerOnofri.LocalElevenContinuousInverse
public import BecknerOnofri.QuarticSignsEleven
public import BecknerOnofri.WeightedExponentialRemainder
public import BecknerOnofri.WeightedExponentialTail
public import BecknerOnofri.LocalElevenCore.GraphRegularity
public import BecknerOnofri.OnsetWienerBounds

@[expose] public section

/-! The actual continuous Gibbs remainder is quadratic in every radial Wiener norm. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open MeasureTheory
open scoped BigOperators
namespace BecknerOnofri.HighDim.LocalEleven.WeightedExponentialRemainder

open BecknerOnofri.HighDim.WeightedExponentialRemainder hiding coefficient_exponential coefficient_exponentialTail coefficient_one exponentialTail exponentialTail_radial exponentialTail_radialSize_le mean_le_radialSize nonlinearRemainder_tail nonlinear_radial nonlinear_radialSize_le nonlinear_radialSize_le_quadratic partition_ge_one radial_unit_hasSum
open BecknerOnofri.HighDim.GraphRegularity hiding Radial green_radial_step green_radial_zero inSobolev_of_radial normalized_coefficient_legacy normalized_radial potential_regular radial_of_same_complement radial_smul reconstruction_radial reconstruction_regular same_complement_of_projected smooth_of_radial toL2_real
open ContinuousGibbs ContinuousFirstShell GraphRegularity

open Legacy.BecknerOnofri.WienerFourier Legacy.BecknerOnofri.WeightedWiener

open Legacy.BecknerOnofri.RadialWiener OnsetWienerBounds

open BecknerOnofri.WeightedExponentialRemainder

def exponentialTail {d : ℕ} (u : Space d) : Space d := exponential u - 1 - u

theorem coefficient_exponential {d : ℕ} (u : Space d)
    (hu : Summable (fun k => ‖coefficient k u‖)) (k : Frequency d) :
    coefficient k (exponential u) = exponentialCoefficients (fun k => coefficient k u) k := by
  have hh := real_exp_coefficient (toL2 d u) hu (toL2_real u) k
  change Legacy.TorusEndpoint.densityFourier (fun x => Real.exp ((toL2 d u) x).re) k =
    exponentialCoefficients (fun k => coefficient k u) k at hh
  rw [← hh, coefficient_integral]
  apply integral_congr_ae
  filter_upwards [toL2_ae u] with x hx
  rw [hx]
  simp only [Complex.ofReal_re, exponential_apply]

theorem coefficient_one {d : ℕ} (k : Frequency d) :
    coefficient k (1 : Space d) = if k=0 then 1 else 0 := by
  change coefficient k (ContinuousMap.const (Torus d) 1) = _
  simp only [coefficient_const, Complex.ofReal_one]

theorem coefficient_exponentialTail {d : ℕ} (u : Space d)
    (hu : Summable (fun k => ‖coefficient k u‖)) (k : Frequency d) :
    coefficient k (exponentialTail u) = tailCoefficients (fun k => coefficient k u) k := by
  rw [exponentialTail, map_sub, map_sub, coefficient_exponential u hu, coefficient_one,
    tailCoefficients_eq _ hu]

theorem exponentialTail_radial {d : ℕ} (m : ℕ) (u : Space d) (hu : Radial m u) :
    Radial m (exponentialTail u) := by
  have h0 := summable_norm (radialWeight_isWeight m) hu
  simpa only [Radial, RadialSummable, coefficient_exponentialTail u h0] using
    tail_weighted_summable (radialWeight_isWeight m) (fun k => coefficient k u) hu

theorem exponentialTail_radialSize_le {d : ℕ} (m : ℕ) (u : Space d) (hu : Radial m u) :
    radialSize m (fun k => coefficient k (exponentialTail u)) ≤
      Real.exp (radialSize m (fun k => coefficient k u)) - 1 - radialSize m (fun k => coefficient k u) := by
  have h0 := summable_norm (radialWeight_isWeight m) hu
  simpa only [radialSize, coefficient_exponentialTail u h0] using
    tail_weighted_sum_le (radialWeight_isWeight m) (fun k => coefficient k u) hu

theorem nonlinear_radial {d : ℕ} (m : ℕ) (u : Space d) (hu : Radial m u) :
    Radial m (nonlinearRemainder u) := by
  have hN := normalized_radial u m hu
  have hs : Summable (fun k => radialWeight m k * ‖coefficient k (normalized u) - coefficient k u‖) := by
    apply (hN.add hu).of_nonneg_of_le
      (fun k => mul_nonneg ((radialWeight_isWeight m).nonneg k) (norm_nonneg _))
    intro k
    exact (mul_le_mul_of_nonneg_left (norm_sub_le _ _) ((radialWeight_isWeight m).nonneg k)).trans_eq (mul_add _ _ _)
  apply hs.congr_cofinite
  filter_upwards [(Set.finite_singleton (0 : Frequency d)).compl_mem_cofinite] with k hk
  have hk0 : k ≠ 0 := by simpa using hk
  have hc : coefficient k (center d u) = coefficient k u := by
    change coefficient k (u - ContinuousMap.const (Torus d) (mean d u)) = _
    rw [map_sub, coefficient_const, if_neg hk0, sub_zero]
  simp only [nonlinearRemainder, map_sub, coefficient_one, if_neg hk0, sub_zero, hc]

theorem partition_ge_one {d : ℕ} (u : Space d) (hm : mean d u = 0) : 1 ≤ partition u := by
  have hh : mean d (1+u) ≤ mean d (exponential u) := by
    apply integral_mono (ContinuousGibbs.integrable d _) (ContinuousGibbs.integrable d _)
    intro x
    simpa only [ContinuousMap.add_apply, ContinuousMap.one_apply, exponential_apply, add_comm] using
      Real.add_one_le_exp (u x)
  simpa only [map_add, mean_one, hm, add_zero, partition] using hh

theorem nonlinearRemainder_tail {d : ℕ} (u : Space d) (hm : mean d u = 0) :
    nonlinearRemainder u = (partition u)⁻¹ •
      (exponentialTail u - mean d (exponentialTail u) • (1+u)) := by
  have ht : mean d (exponentialTail u) = partition u - 1 := by
    simp only [exponentialTail, map_sub, hm, mean_one, sub_zero, partition]
  have hc : center d u = u := by ext x; simp only [center_apply, hm, sub_zero]
  rw [ht]
  ext x
  simp only [nonlinearRemainder, normalized, exponentialTail, hc, ContinuousMap.sub_apply,
    ContinuousMap.smul_apply, ContinuousMap.add_apply, ContinuousMap.one_apply, smul_eq_mul]
  have hZ := (partition_pos u).ne'
  field_simp
  ring

theorem radial_unit_hasSum {d : ℕ} (m : ℕ) :
    HasSum (fun k : Frequency d => radialWeight m k * ‖coefficient k (1 : Space d)‖) 1 := by
  classical
  convert! (hasSum_ite_eq (0 : Frequency d) (1:ℝ)) using 1
  funext k
  by_cases hk : k=0 <;> simp [coefficient_one, hk, (radialWeight_isWeight m).zero]

theorem mean_le_radialSize {d : ℕ} (m : ℕ) (f : Space d) (hf : Radial m f) :
    |mean d f| ≤ radialSize m (fun k => coefficient k f) := by
  have hh := hf.le_tsum (0 : Frequency d) (fun k _ => mul_nonneg ((radialWeight_isWeight m).nonneg k) (norm_nonneg _))
  simpa only [(radialWeight_isWeight m).zero, one_mul, coefficient_zero, Complex.norm_real,
    Real.norm_eq_abs, radialSize] using hh

/-- The exact normalized remainder bound follows from the unnormalized exponential tail. -/
theorem nonlinear_radialSize_le {d : ℕ} (m : ℕ) (u : Space d) (hu : Radial m u)
    (hm : mean d u = 0) :
    radialSize m (fun k => coefficient k (nonlinearRemainder u)) ≤
      (2 + radialSize m (fun k => coefficient k u)) *
        (Real.exp (radialSize m (fun k => coefficient k u)) - 1 - radialSize m (fun k => coefficient k u)) := by
  let T := exponentialTail u
  let M := radialSize m (fun k => coefficient k u)
  let A := radialSize m (fun k => coefficient k T)
  have hT : Radial m T := exponentialTail_radial m u hu
  have hmean : |mean d T| ≤ A := mean_le_radialSize m T hT
  have hM : 0 ≤ M := radialSize_nonneg _ _
  have hmajor : Summable (fun k => radialWeight m k * ‖coefficient k T‖ +
      |mean d T| * (radialWeight m k * ‖coefficient k (1 : Space d)‖ +
        radialWeight m k * ‖coefficient k u‖)) :=
    hT.add (((radial_unit_hasSum m).summable.add hu).mul_left _)
  have hpoint (k : Frequency d) : radialWeight m k * ‖coefficient k (nonlinearRemainder u)‖ ≤
      radialWeight m k * ‖coefficient k T‖ + |mean d T| *
        (radialWeight m k * ‖coefficient k (1 : Space d)‖ + radialWeight m k * ‖coefficient k u‖) := by
    rw [nonlinearRemainder_tail u hm, map_smul, map_sub, map_smul, map_add, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr (partition_pos u).le)]
    have hz : (partition u)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (partition_ge_one u hm)
    have hnorm : ‖coefficient k T - mean d T • (coefficient k (1 : Space d)+coefficient k u)‖ ≤
        ‖coefficient k T‖ + |mean d T| *(‖coefficient k (1 : Space d)‖+‖coefficient k u‖) := by
      calc
        _ ≤ ‖coefficient k T‖ + ‖mean d T • (coefficient k (1 : Space d)+coefficient k u)‖ := norm_sub_le _ _
        _ ≤ _ := by
          simp only [norm_smul, Real.norm_eq_abs]
          exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (norm_add_le _ _) (abs_nonneg _))
    calc
      _ ≤ radialWeight m k * (‖coefficient k T‖ + |mean d T| *(‖coefficient k (1 : Space d)‖+‖coefficient k u‖)) := by
        apply mul_le_mul_of_nonneg_left _ ((radialWeight_isWeight m).nonneg k)
        exact (mul_le_of_le_one_left (norm_nonneg _) hz).trans hnorm
      _ = _ := by ring
  have hR := hmajor.of_nonneg_of_le
    (fun k => mul_nonneg ((radialWeight_isWeight m).nonneg k) (norm_nonneg _)) hpoint
  have hsum := Summable.tsum_le_tsum hpoint hR hmajor
  rw [Summable.tsum_add hT (((radial_unit_hasSum m).summable.add hu).mul_left _), tsum_mul_left,
    Summable.tsum_add (radial_unit_hasSum m).summable hu, (radial_unit_hasSum m).tsum_eq] at hsum
  change radialSize m (fun k => coefficient k (nonlinearRemainder u)) ≤ A + |mean d T| *(1+M) at hsum
  have htail : A ≤ Real.exp M-1-M := exponentialTail_radialSize_le m u hu
  calc
    _ ≤ A + |mean d T| *(1+M) := hsum
    _ ≤ A*(2+M) := by nlinarith [mul_le_mul_of_nonneg_right hmean (show 0≤1+M by positivity)]
    _ ≤ (2+M)*(Real.exp M-1-M) := by nlinarith [mul_le_mul_of_nonneg_right htail (show 0≤2+M by positivity)]

/-- A numerical local quadratic bound, uniform in the actual continuous potential. -/
theorem nonlinear_radialSize_le_quadratic {d : ℕ} (m : ℕ) (u : Space d) (hu : Radial m u)
    (hm : mean d u = 0) (hM : radialSize m (fun k => coefficient k u) ≤ 1) :
    radialSize m (fun k => coefficient k (nonlinearRemainder u)) ≤
      (9/4:ℝ)*(radialSize m (fun k => coefficient k u))^2 := by
  let M := radialSize m (fun k => coefficient k u)
  have h0 : 0 ≤ M := radialSize_nonneg _ _
  have hb := Real.exp_bound (x := M) (by simpa only [abs_of_nonneg h0] using hM) (n := 2) (by norm_num)
  norm_num [Finset.sum_range_succ, abs_of_nonneg h0] at hb
  have ht : Real.exp M-1-M ≤ (3/4:ℝ)*M^2 := by
    have := (le_abs_self (Real.exp M-(1+M))).trans hb
    linarith
  have hh := nonlinear_radialSize_le m u hu hm
  change _ ≤ (2+M)*(Real.exp M-1-M) at hh
  have hh' := mul_le_mul_of_nonneg_left ht (show 0≤2+M by positivity)
  have hh'' := mul_le_mul_of_nonneg_right hM (sq_nonneg M)
  nlinarith

#print axioms nonlinear_radialSize_le
#print axioms nonlinear_radialSize_le_quadratic
end BecknerOnofri.HighDim.LocalEleven.WeightedExponentialRemainder
