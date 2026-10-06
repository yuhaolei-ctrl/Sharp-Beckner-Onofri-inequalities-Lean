module

public import BecknerOnofri.ReducedEquation
public import BecknerOnofri.ContinuousGibbsTaylor

@[expose] public section

/-! The quadratic Taylor term of the actual implicit complement correction. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter Asymptotics
open scoped Topology
namespace BecknerOnofri.HighDim.QuadraticSlaving
open ContinuousGibbs ContinuousFirstShell ContinuousComplement GreenLocalBranch ReducedEquation

theorem pow_down {E : Type*} [NormedAddCommGroup E] :
    (fun x : E => ‖x‖^2) =O[𝓝 0] (fun x => ‖x‖) := by
  apply IsBigO.of_bound 1
  filter_upwards [Metric.ball_mem_nhds (0:E) (by norm_num : (0:ℝ)<1)] with x hx
  have hx' : ‖x‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hx
  simp only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖x‖), abs_norm, one_mul]
  nlinarith [norm_nonneg x]

def sliceCorrection {d : ℕ} (hd : 12 ≤ d) (z : Coordinates d) : complement d := correction hd (1,z)
def slicePotential {d : ℕ} (hd : 12 ≤ d) (z : Coordinates d) : Space d := potential hd (1,z)

theorem slice_tendsto (d : ℕ) :
    Tendsto (fun z : Coordinates d => ((1:ℝ),z)) (𝓝 0) (𝓝 (1,0)) :=
  (continuous_const.prodMk continuous_id).continuousAt

theorem sliceCorrection_quadratic {d : ℕ} (hd : 12 ≤ d) :
    sliceCorrection hd =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖^2) := by
  convert! (correction_quadratic hd).comp_tendsto (slice_tendsto d) using 1
  funext z
  simp only [Function.comp_def, sub_self, abs_zero, zero_mul, add_zero]

theorem sliceCorrection_coe_quadratic {d : ℕ} (hd : 12 ≤ d) :
    (fun z => (sliceCorrection hd z : Space d)) =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖^2) :=
  ((complement d).subtypeL.isBigO_comp _ _).trans (sliceCorrection_quadratic hd)

theorem slicePotential_linear {d : ℕ} (hd : 12 ≤ d) :
    slicePotential hd =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖) := by
  exact (((assembly d).isBigO_id (𝓝 0)).norm_right).add ((sliceCorrection_coe_quadratic hd).trans pow_down)

theorem slicePotential_tendsto {d : ℕ} (hd : 12 ≤ d) :
    Tendsto (slicePotential hd) (𝓝 0) (𝓝 0) := by
  have h := (potential_analytic hd).continuousAt.tendsto.comp (slice_tendsto d)
  convert! h using 1
  simp [potential, correction_base]

@[simp] theorem mean_slicePotential {d : ℕ} (hd : 12 ≤ d) (z : Coordinates d) :
    mean d (slicePotential hd z) = 0 := mean_reconstruction _

/-- The actual complement Green restriction followed by the proven inverse. -/
def inverseGreen {d : ℕ} (hd : 12 ≤ d) : Space d →L[ℝ] complement d :=
  (continuousComplementContinuousLinearEquiv hd (by norm_num : (0:ℝ)≤1)
    (by norm_num : (1:ℝ)≤2)).symm.toContinuousLinearMap.comp
      ((complementMap d).comp (greenContinuous d))

def quadraticCorrection {d : ℕ} (hd : 12 ≤ d) (z : Coordinates d) : complement d :=
  inverseGreen hd (quadraticTerm (assembly d z))

theorem quadraticTerm_difference_cubic {d : ℕ} (hd : 12 ≤ d) :
    (fun z => quadraticTerm (slicePotential hd z) - quadraticTerm (assembly d z))
      =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖^3) := by
  have hv : (assembly d) =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖) :=
    ((assembly d).isBigO_id (𝓝 0)).norm_right
  have hw := sliceCorrection_coe_quadratic hd
  have hw1 := hw.trans pow_down
  have hprod : (fun z => (assembly d z) * (sliceCorrection hd z : Space d))
      =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖^3) := by
    simpa only [← pow_succ'] using hv.mul hw
  have hsq : (fun z => (sliceCorrection hd z : Space d)^2)
      =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖^3) := by
    convert! hw.mul hw1 using 1 <;> (ext z; simp [pow_succ])
  have hh := (hprod.const_smul_left (2:ℝ)).add hsq
  have hcenter := (((center d).isBigO_comp _ _).trans hh).const_smul_left (1/2:ℝ)
  apply hcenter.congr_left
  intro z
  rw [quadraticTerm_of_mean_zero (mean_slicePotential hd z),
    quadraticTerm_of_mean_zero (mean_assembly z), ← smul_sub, ← map_sub]
  change (1/2:ℝ) • center d ((2:ℝ) • (assembly d z * (sliceCorrection hd z : Space d)) +
    (sliceCorrection hd z : Space d)^2) = _
  congr 2
  change (2:ℝ) • (assembly d z * (sliceCorrection hd z : Space d)) +
    (sliceCorrection hd z : Space d)^2 =
      (assembly d z + (sliceCorrection hd z : Space d))^2 - (assembly d z)^2
  ext x
  simp only [ContinuousMap.add_apply, ContinuousMap.sub_apply, ContinuousMap.mul_apply,
    ContinuousMap.pow_apply, ContinuousMap.smul_apply, smul_eq_mul]
  ring

theorem normalized_error_cubic {d : ℕ} (hd : 12 ≤ d) :
    (fun z => normalized (slicePotential hd z) - quadraticPolynomial (slicePotential hd z))
      =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖^3) := by
  have hh := (normalized_quadratic_remainder d).comp_tendsto (slicePotential_tendsto hd)
  have hpow := (slicePotential_linear hd).norm_left.pow 3
  exact hh.trans hpow

theorem nonlinear_error_cubic {d : ℕ} (hd : 12 ≤ d) :
    (fun z => nonlinearRemainder (slicePotential hd z) - quadraticTerm (assembly d z))
      =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖^3) := by
  apply ((normalized_error_cubic hd).add (quadraticTerm_difference_cubic hd)).congr_left
  intro z
  simp only [quadraticPolynomial, nonlinearRemainder]
  abel

/-- Exact inverse equation along the critical parameter slice. -/
theorem sliceCorrection_inverse {d : ℕ} (hd : 12 ≤ d) :
    ∀ᶠ z in 𝓝 (0 : Coordinates d), sliceCorrection hd z =
      inverseGreen hd (nonlinearRemainder (slicePotential hd z)) := by
  have hh := (slice_tendsto d).eventually (correction_solves hd)
  filter_upwards [hh] with z hz
  rw [projectedEquation_eq (greenContinuous d) (green_first_complement_zero (by omega))] at hz
  simp only [ComplementImplicit.equation, one_smul, sub_eq_zero] at hz
  let e := continuousComplementContinuousLinearEquiv hd (by norm_num : (0:ℝ)≤1)
    (by norm_num : (1:ℝ)≤2)
  have he : e (sliceCorrection hd z) =
      complementMap d (greenContinuous d (nonlinearRemainder (slicePotential hd z))) := by
    have heq := continuousComplementContinuousLinearEquiv_one hd
    have hev := congrArg (fun F : complement d →L[ℝ] complement d => F (sliceCorrection hd z)) heq
    rw [← linearPart_eq (by omega)] at hev
    change e (sliceCorrection hd z) = sliceCorrection hd z - linearPart (greenContinuous d) (sliceCorrection hd z) at hev
    rw [hev]
    change correction hd (1,z) - linearPart (greenContinuous d) (correction hd (1,z)) = _
    apply sub_eq_iff_eq_add.mpr
    exact hz.trans (add_comm _ _)
  exact ((e.symm_apply_eq).mpr he.symm).symm

/-- The actual complementary graph has the quadratic slaved mode obtained by
applying (I−G)⁻¹G to the centered square, with a cubic C-norm remainder. -/
theorem correction_quadratic_expansion {d : ℕ} (hd : 12 ≤ d) :
    (fun z => sliceCorrection hd z - quadraticCorrection hd z)
      =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖^3) := by
  have hh := ((inverseGreen hd).isBigO_comp _ _).trans (nonlinear_error_cubic hd)
  apply hh.congr'
  · filter_upwards [sliceCorrection_inverse hd] with z hz
    simp only [map_sub, hz, quadraticCorrection]
  · exact Eventually.of_forall (fun _ => rfl)

#print axioms correction_quadratic_expansion
end BecknerOnofri.HighDim.QuadraticSlaving
