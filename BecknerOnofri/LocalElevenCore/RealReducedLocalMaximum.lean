module

public import BecknerOnofri.LocalElevenCore.RealReducedEnergyGradient
public import BecknerOnofri.LocalElevenCore.ReducedHessianCoercivity
public import BecknerOnofri.CoerciveDerivativeLocalMaximum

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology BigOperators ComplexConjugate
namespace BecknerOnofri.HighDim.LocalEleven.RealReducedEnergy
open ContinuousFirstShell AmplitudeLinearization RescaledReducedEquation ReducedEquation
open DiagonalScalarBranch ReducedCubicExpansion ReducedHessianCoercivity

/-- A true variational local maximum on all real amplitudes, obtained by
integrating the energy derivative; this is stronger than a Hessian sign assertion. -/
theorem diagonal_isLocalMax {d : ℕ} (hd : 11≤d) :
    ∀ᶠ μ in 𝓝[>] (1:ℝ),IsLocalMax (energy hd μ) (fun _ : Fin d => amplitude hd μ) := by
  let a : ℝ → Amplitudes d := fun μ _ => amplitude hd μ
  have ht : Tendsto (fun μ => (μ,a μ)) (𝓝[>] (1:ℝ)) (𝓝 (1,(0 : Amplitudes d))) := by
    exact (tendsto_id.mono_left nhdsWithin_le_nhds).prodMk_nhds
      (tendsto_pi_nhds.mpr (fun _ => amplitude_tendsto hd))
  filter_upwards [ht.eventually (hasFDerivAt_energy hd).eventually_nhds,
    ht.eventually (hasFDerivAt_gradient hd),diagonal_real_jacobian_coercive hd,
    (amplitude_tendsto hd).eventually (parameter_reduced_zero hd),
    amplitude_eventually_inverse hd,self_mem_nhdsWithin] with μ hF hG hcoerce hr hinv hμ
  change 1<μ at hμ
  have hp : 0<μ := by linarith
  have hp2 : 0<2/μ := div_pos (by norm_num) hp
  rw [hinv] at hr
  have hz : reduced hd (μ,realCoordinates d (a μ))=0 := hr
  have hzero : gradient hd μ (a μ)=0 := by simp only [gradient,residual,hz,map_zero,smul_zero]
  have hslice : ∀ᶠ r in 𝓝 (a μ),HasFDerivAt (energy hd μ) (gradient hd μ r) r := by
    have hc : Tendsto (fun r : Amplitudes d => (μ,r)) (𝓝 (a μ)) (𝓝 (μ,a μ)) :=
      (continuous_const.prodMk continuous_id).continuousAt
    exact hc.eventually hF
  apply isLocalMax_of_coercive_derivative (c := (2/μ)*(μ-1))
    (mul_pos hp2 (sub_pos.mpr hμ)) hslice hG hzero
  intro h
  have hh := hcoerce h
  simp only [Complex.re_sum,realCoordinates_apply,Complex.conj_ofReal,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at hh
  have he : realCoordinates d (a μ)=realDiagonal d (amplitude hd μ) := rfl
  simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply,smul_eq_mul,
    dotDual_apply,reCoordinates_apply,he]
  calc
    _ ≤ -(2/μ)*((μ-1)*amplitudeSquare h) :=
      mul_le_mul_of_nonpos_left hh (neg_nonpos.mpr hp2.le)
    _ = -((2/μ)*(μ-1))*amplitudeSquare h := by ring
    _ ≤ -((2/μ)*(μ-1))*‖h‖^2 := mul_le_mul_of_nonpos_left
      (amplitude_norm_square_le h) (by nlinarith)

#print axioms diagonal_isLocalMax
end BecknerOnofri.HighDim.LocalEleven.RealReducedEnergy
