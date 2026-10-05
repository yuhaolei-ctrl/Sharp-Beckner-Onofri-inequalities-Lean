import BecknerOnofri.ReducedAxisDerivative
import BecknerOnofri.ContinuousComplementBounds

/-! Uniform quadratic size of the actual implicit complement correction in the amplitude,
proved by the genuine complement resolvent and absorption of the quadratic Gibbs remainder. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter Asymptotics
open scoped Topology
namespace BecknerOnofri.HighDim.UniformComplementBounds
open ContinuousGibbs ContinuousFirstShell ContinuousComplement GreenLocalBranch ReducedEquation
open ReducedCubicExpansion QuadraticSlaving

def uniformInverseBound (d : ℕ) : ℝ := 1+(64/31:ℝ)*‖greenFourierVector d‖
theorem uniformInverseBound_pos (d : ℕ) : 0 < uniformInverseBound d := by unfold uniformInverseBound; positivity

def nonlinearGreen (d : ℕ) : Space d →L[ℝ] complement d := (complementMap d).comp (greenContinuous d)

theorem correction_inverse_parameter {d : ℕ} (hd : 12 ≤ d) (x : ℝ × Coordinates d)
    (hx : projectedEquation (greenContinuous d) (x,correction hd x) = 0)
    (hμ0 : 0 ≤ x.1) (hμ2 : x.1 ≤ 2) :
    correction hd x = continuousComplementInverse hd hμ0 hμ2
      (x.1 • nonlinearGreen d (nonlinearRemainder (potential hd x))) := by
  let e := continuousComplementContinuousLinearEquiv hd hμ0 hμ2
  have he : e (correction hd x) = x.1 • nonlinearGreen d (nonlinearRemainder (potential hd x)) := by
    have ht := congrArg (fun F : complement d →L[ℝ] complement d => F (correction hd x))
      (continuousComplementContinuousLinearEquiv_toCLM hd hμ0 hμ2)
    change e (correction hd x) = correction hd x - x.1 • continuousComplementGreen (by omega) (correction hd x) at ht
    rw [ht]
    rw [projectedEquation_eq (greenContinuous d) (green_first_complement_zero (by omega))] at hx
    rw [linearPart_eq (by omega)] at hx
    change correction hd x - x.1 • (continuousComplementGreen (by omega) (correction hd x) +
      nonlinearGreen d (nonlinearRemainder (potential hd x))) = 0 at hx
    rw [smul_add, sub_eq_zero] at hx
    rw [sub_eq_iff_eq_add]
    exact hx.trans (add_comm _ _)
  exact ((e.symm_apply_eq).mpr he.symm).symm

theorem parameter_interval {d : ℕ} :
    ∀ᶠ x : ℝ × Coordinates d in 𝓝 (1,0), 0 ≤ x.1 ∧ x.1 ≤ 2 := by
  have ht : Tendsto (Prod.fst : ℝ × Coordinates d → ℝ) (𝓝 (1,0)) (𝓝 1) := continuous_fst.continuousAt
  exact ht.eventually (Icc_mem_nhds (by norm_num : (0:ℝ)<1) (by norm_num : (1:ℝ)<2))

theorem potential_tendsto {d : ℕ} (hd : 12 ≤ d) :
    Tendsto (potential hd) (𝓝 (1,(0 : Coordinates d))) (𝓝 0) := by
  simpa [potential, reconstruction_apply, correction_base] using (potential_analytic hd).continuousAt.tendsto

theorem correction_tendsto {d : ℕ} (hd : 12 ≤ d) :
    Tendsto (correction hd) (𝓝 (1,(0 : Coordinates d))) (𝓝 0) := by
  simpa only [correction_base] using (correction_analytic hd).continuousAt.tendsto

theorem correction_controlled_by_nonlinear {d : ℕ} (hd : 12 ≤ d) :
    correction hd =O[𝓝 (1,(0 : Coordinates d))]
      (fun x => nonlinearRemainder (potential hd x)) := by
  apply IsBigO.of_bound (2*uniformInverseBound d*‖nonlinearGreen d‖)
  filter_upwards [correction_solves hd, parameter_interval (d := d)] with x hx hμ
  rw [correction_inverse_parameter hd x hx hμ.1 hμ.2]
  calc
    _ ≤ uniformInverseBound d * ‖x.1 • nonlinearGreen d (nonlinearRemainder (potential hd x))‖ :=
      continuousComplementInverse_norm_le hd hμ.1 hμ.2 _
    _ ≤ uniformInverseBound d * (2 * (‖nonlinearGreen d‖ * ‖nonlinearRemainder (potential hd x)‖)) := by
      apply mul_le_mul_of_nonneg_left _ (uniformInverseBound_pos d).le
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hμ.1]
      exact mul_le_mul hμ.2 ((nonlinearGreen d).le_opNorm _) (norm_nonneg _) (by norm_num)
    _ = _ := by ring

/-- The exact complement equation forces a bound quadratic in the full potential. -/
theorem correction_potential_quadratic {d : ℕ} (hd : 12 ≤ d) :
    correction hd =O[𝓝 (1,(0 : Coordinates d))] (fun x => ‖potential hd x‖^2) :=
  (correction_controlled_by_nonlinear hd).trans
    ((nonlinearRemainder_quadratic d).comp_tendsto (potential_tendsto hd))

/-- Absorption removes the spurious |μ−1|‖z‖ term: the actual correction is uniformly O(‖z‖²). -/
theorem correction_uniform_quadratic {d : ℕ} (hd : 12 ≤ d) :
    correction hd =O[𝓝 (1,(0 : Coordinates d))] (fun x => ‖x.2‖^2) := by
  obtain ⟨C,hC,hB⟩ := (correction_potential_quadratic hd).exists_pos
  have hw : Tendsto (fun x => ‖correction hd x‖) (𝓝 (1,(0 : Coordinates d))) (𝓝 0) := by
    simpa using (correction_tendsto hd).norm
  have hsmall := hw.eventually (gt_mem_nhds (show (0:ℝ)<1/(4*C) by positivity))
  have hW : correction hd =O[𝓝 (1,(0 : Coordinates d))] (fun x => ‖assembly d x.2‖^2) := by
    apply IsBigO.of_bound (4*C)
    filter_upwards [hB.bound, hsmall] with x hx hs
    simp only [norm_pow, norm_norm] at hx ⊢
    have hs' : 4*C*‖correction hd x‖ ≤ 1 := by
      have hh := (le_div_iff₀ (by positivity : 0<4*C)).mp hs.le
      nlinarith
    have hu : ‖potential hd x‖ ≤ ‖assembly d x.2‖+‖correction hd x‖ := norm_add_le _ _
    have hsq : ‖potential hd x‖^2 ≤ 2*‖assembly d x.2‖^2+2*‖correction hd x‖^2 := by
      nlinarith [sq_nonneg (‖assembly d x.2‖-‖correction hd x‖), norm_nonneg (potential hd x),
        norm_nonneg (assembly d x.2), norm_nonneg (correction hd x)]
    have hmul := mul_le_mul_of_nonneg_left hsq hC.le
    have hab := mul_le_mul_of_nonneg_right hs' (norm_nonneg (correction hd x))
    nlinarith
  have hV : (fun x : ℝ × Coordinates d => assembly d x.2)
      =O[𝓝 (1,0)] (fun x => ‖x.2‖) := ((assembly d).isBigO_comp _ _).norm_right
  exact hW.trans (hV.norm_left.pow 2)

theorem correction_coe_uniform_quadratic {d : ℕ} (hd : 12 ≤ d) :
    (fun x => (correction hd x : Space d)) =O[𝓝 (1,(0 : Coordinates d))] (fun x => ‖x.2‖^2) :=
  ((complement d).subtypeL.isBigO_comp _ _).trans (correction_uniform_quadratic hd)

theorem potential_uniform_linear {d : ℕ} (hd : 12 ≤ d) :
    potential hd =O[𝓝 (1,(0 : Coordinates d))] (fun x => ‖x.2‖) := by
  have hV : (fun x : ℝ × Coordinates d => assembly d x.2)
      =O[𝓝 (1,0)] (fun x => ‖x.2‖) := ((assembly d).isBigO_comp _ _).norm_right
  have ht : Tendsto (Prod.snd : ℝ × Coordinates d → Coordinates d) (𝓝 (1,0)) (𝓝 0) :=
    continuous_snd.continuousAt
  exact hV.add ((correction_coe_uniform_quadratic hd).trans (pow_down.comp_tendsto ht))

#print axioms correction_uniform_quadratic
#print axioms potential_uniform_linear
end BecknerOnofri.HighDim.UniformComplementBounds
