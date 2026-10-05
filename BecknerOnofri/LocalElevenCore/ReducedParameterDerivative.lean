import BecknerOnofri.LocalElevenContinuousInverse
import BecknerOnofri.ReducedParameterDerivative
import BecknerOnofri.LocalElevenCore.ReducedEnergyGradient

/-! The actual parameter derivative of the physical energy on the implicit
graph. Its proof differentiates the genuine projected Gibbs equation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false

open Filter
open scoped Topology
namespace BecknerOnofri.HighDim.LocalEleven.ReducedEnergyGradient

open BecknerOnofri.HighDim.ReducedEnergyGradient hiding fderiv_physicalReducedEnergy_apply graphGradient graphGradient_apply graphValue hasDerivAt_parameter_graphValue hasDerivAt_physicalReducedEnergy_parameter hasFDerivAt_graphValue hasFDerivAt_mean_mul hasFDerivAt_physicalReducedEnergy mean_mul_assembly pairing_cancellation parameter_pairing_cancellation physicalReducedEnergy physicalReducedEnergy_critical_iff physicalReducedEnergy_eq_graphValue projected_equation_value
open BecknerOnofri.HighDim.GreenLocalBranch hiding correction correction_analytic correction_axis correction_base correction_derivative_zero correction_quadratic correction_solves correction_unique exists_analytic_complement green_assembly green_first_complement_zero linearPart_eq zero_axis_of_unique
open BecknerOnofri.HighDim.ReducedEquation hiding complementMap_assembly complementMap_reconstruction coordinates_complement coordinates_green coordinates_one coordinates_reconstruction full full_complement full_coordinates full_mean full_zero_iff graph_full_iff_reduced local_full_iff_reduced meanZero_zero_iff mean_green potential potential_analytic reduced reduced_analytic
open ContinuousGibbs ContinuousFirstShell ContinuousComplement GreenLocalBranch ReducedEquation
open BecknerOnofri.HighDim.GraphEnergy hiding assembly_square_mean complement_fourier_euler graph_dualFunctional graph_energy_term graph_normalizedEnergy_hasSum graph_normalizedPotentialEnergy graph_potentialEnergy hasSum_pairing hasSum_square
open BecknerOnofri.HighDim.GreenPairing hiding coefficient_projectedGreen green_one mean_mul_green mean_mul_projectedGreen mean_mul_selfAdjoint_of_multiplier mean_projectedGreen projectedGreen projectedGreen_apply projectedGreen_one projectedGreen_sub_one
open BecknerOnofri.HighDim.QuadraticModes
open QuadraticModes GraphEnergy GreenPairing

theorem parameter_pairing_cancellation {d : ℕ} (hd : 0 < d) (μ : ℝ)
    (w N a dw : Space d) (hw : w = μ • projectedGreen d N)
    (hdw : dw = μ • projectedGreen d a + projectedGreen d N) :
    μ * (mean d (N*dw) - mean d (w*a)) = mean d (w*N) := by
  rw [hw, hdw]
  simp only [mul_add, mul_smul_comm, smul_mul_assoc, map_add, map_smul, smul_eq_mul]
  rw [mean_mul_projectedGreen hd N a]
  rw [mul_comm N (projectedGreen d N)]
  ring

theorem hasDerivAt_parameter_graphValue {d : ℕ} (hd : 0 < d) {μ : ℝ} (hμ : μ ≠ 0)
    (z : Coordinates d) {ψ : ℝ → complement d} {ψ' : complement d}
    (hψ : HasDerivAt ψ ψ' μ)
    (he : ∀ᶠ σ in 𝓝 μ, projectedEquation (greenContinuous d) ((σ,z),ψ σ) = 0) :
    HasDerivAt (fun σ => graphValue σ (fun _ => ψ σ) z)
      (mean d ((assembly d z)^2)/(2*μ^2) +
        mean d ((ψ μ : Space d)*normalized (reconstruction d (z,ψ μ)))/(2*μ)) μ := by
  let u := reconstruction d (z,ψ μ)
  let dw : Space d := ψ'
  let a : Space d := normalizedDerivative u dw
  have hw : HasDerivAt (fun σ => (ψ σ : Space d)) dw μ := by
    convert! (complement d).subtypeL.hasFDerivAt.comp_hasDerivAt μ hψ using 1
  have hu : HasDerivAt (fun σ => reconstruction d (z,ψ σ)) dw μ := by
    convert! (hasDerivAt_const μ (assembly d z)).add hw using 1 <;> simp
  have hn : HasDerivAt (fun σ => normalized (reconstruction d (z,ψ σ))) a μ := by
    convert! (hasFDerivAt_normalized u).comp_hasDerivAt μ hu using 1
  have hg : HasDerivAt
      (fun σ => σ • projectedGreen d (normalized (reconstruction d (z,ψ σ))))
      (μ • projectedGreen d a + projectedGreen d (normalized u)) μ := by
    convert! (hasDerivAt_id μ).smul ((projectedGreen d).hasFDerivAt.comp_hasDerivAt μ hn) using 1
    simp [u]
  have hec : (fun σ => (ψ σ : Space d)) =ᶠ[𝓝 μ]
      (fun σ => σ • projectedGreen d (normalized (reconstruction d (z,ψ σ)))) := by
    filter_upwards [he] with σ hσ
    exact projected_equation_value hd σ z (ψ σ) hσ
  have hdw : dw = μ • projectedGreen d a + projectedGreen d (normalized u) :=
    hw.unique (hg.congr_of_eventuallyEq hec)
  have hc := parameter_pairing_cancellation hd μ (ψ μ) (normalized u) a dw
    hec.self_of_nhds hdw
  have hl : HasDerivAt (fun σ => logPartitionReal (reconstruction d (z,ψ σ)))
      (mean d (normalized u*dw)) μ := by
    exact (hasFDerivAt_logPartitionReal u).comp_hasDerivAt μ hu
  have hm : HasDerivAt
      (fun σ => mean d ((ψ σ : Space d)*normalized (reconstruction d (z,ψ σ))))
      (mean d ((ψ μ : Space d)*a) + mean d (normalized u*dw)) μ := by
    convert! (meanProduct d).hasDerivAt_of_bilinear (fun _ => hw) (fun _ => hn) using 1
    simp only [meanProduct_apply]
    rw [mul_comm dw]
  have hv := ((hasDerivAt_id μ).inv hμ).const_mul (mean d ((assembly d z)^2)/2)
  convert! (hl.sub hv).sub (hm.const_mul (1/2:ℝ)) using 1
  · funext σ
    unfold graphValue
    simp only [Pi.sub_apply, Pi.inv_apply, id_eq]
    ring
  · dsimp only [id_eq]
    have hc' := congrArg (fun q : ℝ => μ*q) hc
    dsimp only [u] at hc'
    field_simp
    nlinarith [hc']

theorem hasDerivAt_physicalReducedEnergy_parameter {d : ℕ} (hd : 11 ≤ d) :
    ∀ᶠ x in 𝓝 (1, (0 : Coordinates d)),
      HasDerivAt (fun μ => physicalReducedEnergy hd (μ,x.2))
        (normalizedPotentialEnergy (potential hd x)/(2*x.1^2)) x.1 := by
  have hp : ∀ᶠ x : ℝ × Coordinates d in 𝓝 (1,0), 0 < x.1 :=
    continuous_fst.continuousAt.preimage_mem_nhds (Ioi_mem_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [(correction_solves hd).eventually_nhds,
    (correction_analytic hd).eventually_analyticAt, hp] with x hx ha hpos
  have ht : HasDerivAt (fun μ : ℝ => (μ,x.2)) (1,0) x.1 :=
    (hasDerivAt_id x.1).prodMk (hasDerivAt_const x.1 x.2)
  have hψ : DifferentiableAt ℝ (fun μ => correction hd (μ,x.2)) x.1 := by
    convert! ha.differentiableAt.comp x.1 ht.differentiableAt using 1
  have hes : ∀ᶠ μ in 𝓝 x.1,
      projectedEquation (greenContinuous d) ((μ,x.2),correction hd (μ,x.2)) = 0 :=
    ht.continuousAt.tendsto.eventually hx
  have hh := hasDerivAt_parameter_graphValue (by omega : 0 < d) hpos.ne' x.2 hψ.hasDerivAt hes
  have he : normalizedPotentialEnergy (potential hd x)/(2*x.1^2) =
      mean d ((assembly d x.2)^2)/(2*x.1^2) +
        mean d ((correction hd (x.1,x.2) : Space d)*normalized
          (reconstruction d (x.2,correction hd (x.1,x.2))))/(2*x.1) := by
    rw [potential, graph_normalizedPotentialEnergy (by omega) x.1 x.2 (correction hd x)
      (hx.self_of_nhds), assembly_square_mean]
    field_simp <;> ring
  rw [he]
  apply hh.congr_of_eventuallyEq
  filter_upwards [hes, Ioi_mem_nhds hpos] with μ hμ hμpos
  exact physicalReducedEnergy_eq_graphValue hd hμpos x.2 hμ

#print axioms hasDerivAt_physicalReducedEnergy_parameter
end BecknerOnofri.HighDim.LocalEleven.ReducedEnergyGradient
