module

public import BecknerOnofri.SupercriticalEnergyDerivatives
public import BecknerOnofri.OnsetConsequences
public import Mathlib.Analysis.Calculus.Deriv.CompMul

@[expose] public section

/-! One-sided second derivatives of the actual variational pressure. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter Set
open scoped Topology
namespace BecknerOnofri.HighDim.OnsetConsequences
open DiagonalScalarBranch

lemma pressure_eq_supercritical (d : ℕ) (hd : 12 ≤ d) :
    ∀ᶠ μ in 𝓝[>] (1:ℝ), (pressure d (μ*spectralThreshold d)).toReal = supercriticalEnergy hd μ := by
  have hE := EntropyMinorantCompletion.legacy_endpoint psi_le_gamma pressureScalar_gt hd
  have hR := EntropyMinorantCompletion.legacy_rigidity psi_le_gamma pressureScalar_gt hd
  filter_upwards [GlobalOptimizerClassification.branch_eventually_optimizer hd hE hR,
    supercriticalEnergy_coe hd,self_mem_nhdsWithin] with μ hm he hp
  have hβ : 0 < μ*spectralThreshold d :=
    mul_pos (by change 1<μ at hp; linarith) (spectralThreshold_pos (by omega))
  rw [GlobalPressureOnset.optimizer_pressure (by omega) hβ _ hm.1 hm.2.2,he,EReal.toReal_coe]

lemma second_deriv_scaled (f : ℝ → ℝ) (c x : ℝ) :
    deriv (deriv (fun y => f (c*y))) x = c^2*deriv (deriv f) (c*x) := by
  have he : deriv (fun y => f (c*y)) = fun y => c*deriv f (c*y) := by
    funext y
    simpa only [smul_eq_mul] using deriv_comp_mul_left c f y
  rw [he,deriv_const_mul_field,deriv_comp_mul_left]
  simp only [smul_eq_mul]
  ring

lemma second_deriv_eventuallyEq_right {f g : ℝ → ℝ} {a : ℝ}
    (he : f =ᶠ[𝓝[>] a] g) : deriv (deriv f) =ᶠ[𝓝[>] a] deriv (deriv g) := by
  have hfirst : deriv f =ᶠ[𝓝[>] a] deriv g :=
    (eventually_local_right he).mono (fun x h => (show f =ᶠ[𝓝 x] g from h).deriv_eq)
  exact (eventually_local_right hfirst).mono (fun x h => (show deriv f =ᶠ[𝓝 x] deriv g from h).deriv_eq)

/-- The right curvature is positive and equals d/(κ_d σ_d²). -/
theorem pressure_second_derivative_right (d : ℕ) (hd : 12 ≤ d) :
    Tendsto (deriv (deriv (fun β => (pressure d β).toReal))) (𝓝[>] (spectralThreshold d))
      (𝓝 ((d:ℝ)/(kappa d*(spectralThreshold d)^2))) := by
  have hσ := (spectralThreshold_pos (by omega : 0 < d)).ne'
  have he : (fun β => (pressure d β).toReal) =ᶠ[𝓝[>] (spectralThreshold d)]
      (fun β => supercriticalEnergy hd ((spectralThreshold d)⁻¹*β)) := by
    filter_upwards [(normalized_parameter_tendsto hd).eventually
      (pressure_eq_supercritical d hd)] with β hβ
    change (pressure d ((β / spectralThreshold d) * spectralThreshold d)).toReal = _ at hβ
    rw [div_mul_cancel₀ _ hσ] at hβ
    simpa only [div_eq_mul_inv,mul_comm] using hβ
  have ht := (supercriticalEnergy_second_derivative_limit hd).comp
    (normalized_parameter_tendsto hd)
  have ht' := ht.const_mul ((spectralThreshold d)⁻¹^2)
  have hvalue : (spectralThreshold d)⁻¹^2*((d:ℝ)/kappa d) =
      (d:ℝ)/(kappa d*(spectralThreshold d)^2) := by ring
  rw [hvalue] at ht'
  apply ht'.congr'
  filter_upwards [second_deriv_eventuallyEq_right he] with β hβ
  rw [hβ,second_deriv_scaled]
  simp only [Function.comp_apply,div_eq_mul_inv,mul_comm]

/-- The subcritical branch is identically zero, hence has zero left curvature. -/
theorem pressure_second_derivative_left (d : ℕ) (hd : 12 ≤ d) :
    Tendsto (deriv (deriv (fun β => (pressure d β).toReal))) (𝓝[<] (spectralThreshold d)) (𝓝 0) := by
  have he : ∀ β < spectralThreshold d, (fun γ => (pressure d γ).toReal) =ᶠ[𝓝 β] (fun _ => 0) := by
    intro β hβ
    filter_upwards [gt_mem_nhds hβ] with γ hγ
    simp [pressure_zero_below hd hγ.le]
  have hd1 : ∀ β < spectralThreshold d, deriv (fun γ => (pressure d γ).toReal) β = 0 := by
    intro β hβ
    simpa using (he β hβ).deriv_eq
  apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin] with β hβ
  have he' : deriv (fun γ => (pressure d γ).toReal) =ᶠ[𝓝 β] (fun _ => 0) := by
    filter_upwards [gt_mem_nhds hβ] with γ hγ
    exact hd1 γ hγ
  simpa using he'.deriv_eq.symm

#print axioms pressure_second_derivative_right
#print axioms pressure_second_derivative_left
end BecknerOnofri.HighDim.OnsetConsequences
