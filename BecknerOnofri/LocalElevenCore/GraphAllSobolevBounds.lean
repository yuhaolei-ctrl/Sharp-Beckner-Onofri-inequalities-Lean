import BecknerOnofri.LocalElevenContinuousInverse
import BecknerOnofri.QuarticSignsEleven
import BecknerOnofri.GraphAllSobolevBounds
import BecknerOnofri.LocalElevenCore.GraphWienerBounds

/-! Uniform quadratic bounds in every fixed physical Sobolev norm, for the
actual analytic complementary graph. -/
noncomputable section

open MeasureTheory Filter Asymptotics
open scoped BigOperators Topology
namespace BecknerOnofri.HighDim.LocalEleven.GraphAllSobolevBounds

open BecknerOnofri.HighDim.GraphAllSobolevBounds hiding correction_inSobolev correction_sobolev_quadratic inSobolev_of_wiener potential_sobolev_linear sobolevNorm_le_wiener sobolevTerm_le_wiener
open BecknerOnofri.HighDim.GreenLocalBranch hiding correction correction_analytic correction_axis correction_base correction_derivative_zero correction_quadratic correction_solves correction_unique exists_analytic_complement green_assembly green_first_complement_zero linearPart_eq zero_axis_of_unique
open BecknerOnofri.HighDim.ReducedEquation hiding complementMap_assembly complementMap_reconstruction coordinates_complement coordinates_green coordinates_one coordinates_reconstruction full full_complement full_coordinates full_mean full_zero_iff graph_full_iff_reduced local_full_iff_reduced meanZero_zero_iff mean_green potential potential_analytic reduced reduced_analytic
open ContinuousGibbs ContinuousFirstShell ContinuousComplement GreenLocalBranch ReducedEquation
open BecknerOnofri.HighDim.GraphRegularity hiding Radial green_radial_step green_radial_zero inSobolev_of_radial normalized_coefficient_legacy normalized_radial potential_regular radial_of_same_complement radial_smul reconstruction_radial reconstruction_regular same_complement_of_projected smooth_of_radial toL2_real
open BecknerOnofri.HighDim.GraphWienerBounds hiding continuousFourier_norm_le correction_coefficient_green_bound correction_radial correction_wiener_quadratic correction_wiener_step_bound correction_wiener_step_quadratic correction_wiener_zero_bound correction_wiener_zero_quadratic nonlinear_wiener_quadratic_of_potential potential_wiener_linear potential_wiener_linear_of_correction radial_add radial_assembly radial_finset_sum radial_synthesis radial_zero wienerSize wienerSize_add_le wienerSize_assembly_le wienerSize_finset_sum_le wienerSize_mono wienerSize_synthesis_le
open GraphRegularity GraphWienerBounds BecknerOnofri.OnsetWienerBounds

open Legacy.BecknerOnofri.RadialWiener

theorem sobolevTerm_le_wiener {d : ℕ} {s : ℝ} {m : ℕ} (hs : s≤(m:ℝ))
    (u : Space d) (hu : Radial m u) (k : Frequency d) :
    sobolevTerm s u k ≤ ((1+2*Real.pi)^(2*m)*wienerSize m u)*
      (radialWeight m k*‖coefficient k u‖) := by
  have hpoint := hu.le_tsum k (fun j _ =>
    mul_nonneg ((radialWeight_isWeight m).nonneg j) (norm_nonneg _))
  change radialWeight m k*‖coefficient k u‖ ≤ wienerSize m u at hpoint
  have ha : 0 ≤ radialWeight m k*‖coefficient k u‖ :=
    mul_nonneg ((radialWeight_isWeight m).nonneg k) (norm_nonneg _)
  have hweight := BecknerOnofri.OnsetSobolev.physical_weight_le_radial hs k
  unfold sobolevTerm
  rw [← coefficient_eq_fourierCoeff]
  calc
    _ ≤ ((1+2*Real.pi)^(2*m)*radialWeight (2*m) k)*‖coefficient k u‖^2 :=
      mul_le_mul_of_nonneg_right hweight (sq_nonneg _)
    _ = (1+2*Real.pi)^(2*m)*(radialWeight m k*‖coefficient k u‖)^2 := by
      simp only [radialWeight, mul_pow, ← pow_mul, Nat.mul_comm]
      ring
    _ ≤ (1+2*Real.pi)^(2*m)*(wienerSize m u*(radialWeight m k*‖coefficient k u‖)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith [mul_le_mul_of_nonneg_right hpoint ha]
    _ = _ := by ring

theorem inSobolev_of_wiener {d : ℕ} {s : ℝ} {m : ℕ} (hs : s≤(m:ℝ))
    (u : Space d) (hu : Radial m u) : InSobolev s u := by
  refine ⟨u.continuous.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _), ?_⟩
  apply (hu.mul_left ((1+2*Real.pi)^(2*m)*wienerSize m u)).of_nonneg_of_le
  · intro k
    unfold sobolevTerm
    positivity
  · exact sobolevTerm_le_wiener hs u hu

/-- Direct conversion from the actual radial Wiener norm to the trusted
physical Sobolev norm, with its precise 2π normalization. -/
theorem sobolevNorm_le_wiener {d : ℕ} {s : ℝ} {m : ℕ} (hs : s≤(m:ℝ))
    (u : Space d) (hu : Radial m u) :
    sobolevNorm s u ≤ (1+2*Real.pi)^m*wienerSize m u := by
  have hsum := hasSum_le (sobolevTerm_le_wiener hs u hu)
    (inSobolev_of_wiener hs u hu).2.hasSum
    (hu.hasSum.mul_left ((1+2*Real.pi)^(2*m)*wienerSize m u))
  change (∑' k, sobolevTerm s u k) ≤ ((1+2*Real.pi)^(2*m)*wienerSize m u)*wienerSize m u at hsum
  unfold sobolevNorm
  apply (Real.sqrt_le_iff).mpr
  refine ⟨mul_nonneg (by positivity) (radialSize_nonneg _ _), ?_⟩
  convert hsum using 1
  rw [mul_pow, ← pow_mul, Nat.mul_comm m 2]
  ring

/-- No regularity assumption is added: actual graph solutions have finite
Sobolev energy and a uniform quadratic correction in every fixed H^s. -/
theorem correction_sobolev_quadratic {d : ℕ} (hd : 11 ≤ d) (s : ℝ) :
    (fun x => sobolevNorm s (correction hd x : Space d))
      =O[𝓝 (1,(0 : Coordinates d))] (fun x => ‖x.2‖^2) := by
  obtain ⟨m, hm⟩ := exists_nat_ge s
  have hb : (fun x => sobolevNorm s (correction hd x : Space d))
      =O[𝓝 (1,(0 : Coordinates d))] (fun x => wienerSize m (correction hd x : Space d)) := by
    apply IsBigO.of_bound ((1+2*Real.pi)^m)
    filter_upwards [correction_solves hd] with x hx
    rw [Real.norm_of_nonneg (show 0 ≤ sobolevNorm s (correction hd x : Space d) from Real.sqrt_nonneg _), Real.norm_of_nonneg (radialSize_nonneg _ _)]
    exact sobolevNorm_le_wiener hm _
      (correction_radial (by omega) x.1 x.2 (correction hd x) hx m)
  exact hb.trans (correction_wiener_quadratic hd m)

theorem correction_inSobolev {d : ℕ} (hd : 11 ≤ d) (s : ℝ) :
    ∀ᶠ x in 𝓝 (1,(0 : Coordinates d)), InSobolev s (correction hd x : Space d) := by
  obtain ⟨m, hm⟩ := exists_nat_ge s
  filter_upwards [correction_solves hd] with x hx
  exact inSobolev_of_wiener hm _
    (correction_radial (by omega) x.1 x.2 (correction hd x) hx m)

theorem potential_sobolev_linear {d : ℕ} (hd : 11 ≤ d) (s : ℝ) :
    (fun x => sobolevNorm s (potential hd x))
      =O[𝓝 (1,(0 : Coordinates d))] (fun x => ‖x.2‖) := by
  obtain ⟨m, hm⟩ := exists_nat_ge s
  have hb : (fun x => sobolevNorm s (potential hd x))
      =O[𝓝 (1,(0 : Coordinates d))] (fun x => wienerSize m (potential hd x)) := by
    apply IsBigO.of_bound ((1+2*Real.pi)^m)
    filter_upwards [correction_solves hd] with x hx
    rw [Real.norm_of_nonneg (show 0 ≤ sobolevNorm s (potential hd x) from Real.sqrt_nonneg _), Real.norm_of_nonneg (radialSize_nonneg _ _)]
    exact sobolevNorm_le_wiener hm _
      (reconstruction_radial (by omega) x.1 x.2 (correction hd x) hx m)
  exact hb.trans (potential_wiener_linear hd m)

#print axioms correction_sobolev_quadratic
#print axioms correction_inSobolev
#print axioms potential_sobolev_linear
end BecknerOnofri.HighDim.LocalEleven.GraphAllSobolevBounds
