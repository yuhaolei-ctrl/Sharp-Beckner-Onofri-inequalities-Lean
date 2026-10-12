module

public import BecknerOnofri.V2.Onset.PressureOnset
public import BecknerOnofri.BranchSecondDerivativeRemainder
public import BecknerOnofri.BranchFirstDerivativeRemainder
public import BecknerOnofri.SupercriticalEnergyDerivatives
public import BecknerOnofri.QuadraticOnsetDerivative
public import BecknerOnofri.OrderParameterOnset
public import BecknerOnofri.V2.Reaudit.MorseBott.OrderParameterV2
public import BecknerOnofri.GlobalOptimizerClassification
public import BecknerOnofri.FiniteEntropyEnergy
public import Mathlib.Analysis.Calculus.Deriv.CompMul

@[expose] public section

/-! # One-sided pressure derivatives and the order parameter (clean route)

The statements of `OnsetConsequences`, `PressureDerivativeOnset`, `PressureCurvatureOnset` and
`PressureSecondDerivative`, rebuilt without importing those endpoint modules: the only inputs are the
interface hypotheses `OnsetEndpointInputs d` (the zero pressure at `β_s` is the dual form of the density
inequality, as in the proof of `cor:section5-high-endpoint`) together with the clean `DiagonalScalarBranch`,
`SupercriticalEnergyDerivatives`, `BranchFirstDerivativeRemainder` and
`BranchSecondDerivativeRemainder` declarations. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter Asymptotics Set MeasureTheory
open scoped Topology

namespace BecknerOnofri.V2.Onset
open BecknerOnofri.HighDim BecknerOnofri.HighDim.DiagonalScalarBranch

lemma pressure_monotone_v2 {d : ℕ} (hd : 0 < d) : Monotone (pressure d) := by
  intro a b hab
  apply iSup_le fun ρ => iSup_le fun hρ => ?_
  apply le_trans ?_ (le_iSup_of_le ρ (le_iSup_of_le hρ le_rfl) : pressureValue b ρ ≤ pressure d b)
  change pressureValue a ρ ≤ pressureValue b ρ
  simp only [pressureValue, spectralEnergy_coe_eq_tsum hd ρ hρ]
  rw [← EReal.coe_mul, ← EReal.coe_sub, ← EReal.coe_mul, ← EReal.coe_sub]
  apply EReal.coe_le_coe_iff.mpr
  apply sub_le_sub_right
  apply mul_le_mul_of_nonneg_right
  · exact div_le_div_of_nonneg_right hab (by positivity [spectralThreshold_pos hd])
  · apply tsum_nonneg
    intro k
    unfold spectralTerm frequencyLength
    positivity

/-- `P_d(β) = 0` for `β ≤ β_s(d)`, from the spectral inequality alone. -/
theorem pressure_zero_below_v2 {d : ℕ} (hd : 12 ≤ d) (E : OnsetEndpointInputs d) {β : ℝ}
    (hβ : β ≤ spectralThreshold d) : pressure d β = 0 := by
  apply le_antisymm _ (pressure_nonneg _ _)
  have h := pressure_monotone_v2 (d := d) (by omega) hβ
  have hd0 : 0 < d := by omega
  have hσ := spectralThreshold_pos hd0
  have hmem : pressure d (spectralThreshold d) = 0 := by
    rw [pressure_eq_coefficientDefect hd0 hσ]
    have he : spectralThreshold d / (2 * spectralThreshold d * (2 * Real.pi) ^ d) =
        spectralCoefficient d := by
      unfold spectralCoefficient
      field_simp
    rw [he]
    exact coefficientDefect_spectral_zero_of_primal hd0
      (fun u hu => (potential_endpoint_of_density hd0 E.inequality u hu).2)
  rwa [hmem] at h

/-- Near the threshold, the (real part of the) pressure is the explicit supercritical energy.
The optimizer is the one of the Sobolev-smallness / second-variation route (`branch_eventually_optimizer_v2`),
transported to the derivative-family branch through the profile branch
(`full_branch_identification`, `common_branch_interface`). -/
lemma pressure_eq_supercritical_v2 {d : ℕ} (hd : 12 ≤ d) (E : OnsetEndpointInputs d) :
    ∀ᶠ μ in 𝓝[>] (1 : ℝ), (pressure d (μ * spectralThreshold d)).toReal = supercriticalEnergy hd μ := by
  obtain ⟨R, -, hroot⟩ := V2.Reaudit.MorseBott.common_branch_interface hd
  filter_upwards [branch_eventually_optimizer_v2 hd E,
    LocalEleven.SupportedFamily.full_branch_identification (by omega : 11 ≤ d), hroot,
    supercriticalEnergy_coe hd, self_mem_nhdsWithin] with μ hm hcore hr he hp
  have hβ : 0 < μ * spectralThreshold d :=
    mul_pos (by change 1 < μ at hp; linarith) (spectralThreshold_pos (by omega))
  dsimp only at hm
  rw [GlobalPressureOnset.optimizer_pressure (by omega) hβ _ hm.1 hm.2.2, ← hcore, ← hr.1, he,
    EReal.toReal_coe]

lemma second_deriv_scaled_v2 (f : ℝ → ℝ) (c x : ℝ) :
    deriv (deriv (fun y => f (c * y))) x = c ^ 2 * deriv (deriv f) (c * x) := by
  have he : deriv (fun y => f (c * y)) = fun y => c * deriv f (c * y) := by
    funext y
    simpa only [smul_eq_mul] using deriv_comp_mul_left c f y
  rw [he, deriv_const_mul_field, deriv_comp_mul_left]
  simp only [smul_eq_mul]
  ring

lemma second_deriv_eventuallyEq_right_v2 {f g : ℝ → ℝ} {a : ℝ}
    (he : f =ᶠ[𝓝[>] a] g) : deriv (deriv f) =ᶠ[𝓝[>] a] deriv (deriv g) := by
  have hfirst : deriv f =ᶠ[𝓝[>] a] deriv g :=
    (eventually_local_right he).mono (fun x h => (show f =ᶠ[𝓝 x] g from h).deriv_eq)
  exact (eventually_local_right hfirst).mono
    (fun x h => (show deriv f =ᶠ[𝓝 x] deriv g from h).deriv_eq)

lemma pressure_eventuallyEq_supercritical {d : ℕ} (hd : 12 ≤ d) (E : OnsetEndpointInputs d) :
    (fun β => (pressure d β).toReal) =ᶠ[𝓝[>] (spectralThreshold d)]
      (fun β => supercriticalEnergy hd ((spectralThreshold d)⁻¹ * β)) := by
  have hσ := (spectralThreshold_pos (by omega : 0 < d)).ne'
  filter_upwards [(normalized_parameter_tendsto hd).eventually
    (pressure_eq_supercritical_v2 hd E)] with β hβ
  change (pressure d ((β / spectralThreshold d) * spectralThreshold d)).toReal = _ at hβ
  rw [div_mul_cancel₀ _ hσ] at hβ
  simpa only [div_eq_mul_inv, mul_comm] using hβ

lemma supercriticalEnergy_derivative_expansion_v2 {d : ℕ} (hd : 12 ≤ d) :
    (fun μ => deriv (supercriticalEnergy hd) μ - (d : ℝ) / kappa d * onset μ)
      =O[𝓝[>] (1 : ℝ)] (fun μ => (onset μ) ^ 2) := by
  have hfour : (fun μ => ‖amplitude hd μ‖ ^ 4) =O[𝓝[>] (1 : ℝ)] (fun μ => (onset μ) ^ 2) := by
    convert! (amplitude_square_bound hd).pow 2 using 1
    funext μ
    rw [Real.norm_eq_abs, abs_of_nonneg (amplitude_nonneg hd μ)]
    ring
  have hmain := ((energy_parameter_derivative_expansion hd).comp_tendsto
    (amplitude_tendsto_right hd)).trans hfour
  have hamp := (amplitude_square_expansion hd).const_mul_left (d : ℝ)
  apply (hmain.add hamp).congr'
  · filter_upwards [supercriticalEnergy_hasDerivAt hd] with μ hm
    rw [hm.deriv]
    dsimp only [Function.comp_apply]
    ring
  · rfl

lemma supercriticalEnergy_second_derivative_expansion_v2 {d : ℕ} (hd : 12 ≤ d) :
    (fun μ => deriv (deriv (supercriticalEnergy hd)) μ - (d : ℝ) / kappa d)
      =O[𝓝[>] (1 : ℝ)] onset := by
  have hb : (fun μ => ‖amplitude hd μ‖ ^ 2) =O[𝓝[>] (1 : ℝ)] onset := by
    simpa only [Real.norm_eq_abs, sq_abs] using amplitude_square_bound hd
  have h := ((energy_parameter_second_derivative_expansion hd).comp_tendsto
    (amplitude_tendsto_right hd)).trans hb
  apply h.congr'
  · filter_upwards [supercriticalEnergy_second_hasDerivAt hd] with μ hm
    exact congrArg (fun x => x - (d : ℝ) / kappa d) hm.deriv.symm
  · rfl

/-- **First-derivative onset formula.** -/
theorem pressure_derivative_expansion_v2 {d : ℕ} (hd : 12 ≤ d) (E : OnsetEndpointInputs d) :
    (fun β => deriv (fun γ => (pressure d γ).toReal) β -
      (d : ℝ) / (kappa d * spectralThreshold d) * onsetDelta d β)
      =O[𝓝[>] (spectralThreshold d)] (fun β => (onsetDelta d β) ^ 2) := by
  have he := pressure_eventuallyEq_supercritical hd E
  have h := ((supercriticalEnergy_derivative_expansion_v2 hd).comp_tendsto
    (normalized_parameter_tendsto hd)).const_mul_left ((spectralThreshold d)⁻¹)
  apply h.congr'
  · filter_upwards [eventually_local_right he] with β hb
    change (fun γ => (pressure d γ).toReal) =ᶠ[𝓝 β]
      (fun γ => supercriticalEnergy hd ((spectralThreshold d)⁻¹ * γ)) at hb
    rw [hb.deriv_eq, deriv_comp_mul_left]
    dsimp only [Function.comp_apply]
    rw [physical_onset_eq hd]
    simp only [smul_eq_mul, div_eq_mul_inv, mul_inv_rev]
    ring_nf
  · exact Eventually.of_forall (fun β => by simp only [Function.comp_apply, physical_onset_eq hd])

/-- **Second-derivative onset formula.** -/
theorem pressure_second_derivative_expansion_v2 {d : ℕ} (hd : 12 ≤ d) (E : OnsetEndpointInputs d) :
    (fun β => deriv (deriv (fun γ => (pressure d γ).toReal)) β -
      (d : ℝ) / (kappa d * (spectralThreshold d) ^ 2))
      =O[𝓝[>] (spectralThreshold d)] (onsetDelta d) := by
  have he := pressure_eventuallyEq_supercritical hd E
  have h := ((supercriticalEnergy_second_derivative_expansion_v2 hd).comp_tendsto
    (normalized_parameter_tendsto hd)).const_mul_left ((spectralThreshold d)⁻¹ ^ 2)
  apply h.congr'
  · filter_upwards [second_deriv_eventuallyEq_right_v2 he] with β hb
    rw [hb, second_deriv_scaled_v2]
    dsimp only [Function.comp_apply]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring_nf
  · exact Eventually.of_forall
      (fun β => by simpa only [Function.comp_apply] using physical_onset_eq hd β)

/-- The right first derivative of the pressure tends to `0` at the threshold. -/
theorem pressure_first_derivative_right_v2 {d : ℕ} (hd : 12 ≤ d) (E : OnsetEndpointInputs d) :
    Tendsto (deriv (fun β => (pressure d β).toReal))
      (𝓝[>] (spectralThreshold d)) (𝓝 0) := by
  have hδ : Tendsto (onsetDelta d) (𝓝[>] (spectralThreshold d)) (𝓝 0) := by
    simpa only [Function.comp_def, physical_onset_eq hd] using
      onset_tendsto.comp (normalized_parameter_tendsto hd)
  have hr := (pressure_derivative_expansion_v2 hd E).trans_tendsto
    (show Tendsto (fun β => (onsetDelta d β) ^ 2) _ (𝓝 0) by simpa using hδ.pow 2)
  have h := hr.add (hδ.const_mul ((d : ℝ) / (kappa d * spectralThreshold d)))
  simpa only [sub_add_cancel, mul_zero, zero_add] using h

/-- The left first derivative of the pressure is `0`. -/
theorem pressure_first_derivative_left_v2 {d : ℕ} (hd : 12 ≤ d) (E : OnsetEndpointInputs d) :
    Tendsto (deriv (fun β => (pressure d β).toReal))
      (𝓝[<] (spectralThreshold d)) (𝓝 0) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin] with β hβ
  have he : (fun γ => (pressure d γ).toReal) =ᶠ[𝓝 β] (fun _ => 0) := by
    filter_upwards [gt_mem_nhds hβ] with γ hγ
    simp [pressure_zero_below_v2 hd E hγ.le]
  simpa using he.deriv_eq.symm

/-- The right curvature is `d/(κ_d σ_d²)`. -/
theorem pressure_second_derivative_right_v2 {d : ℕ} (hd : 12 ≤ d) (E : OnsetEndpointInputs d) :
    Tendsto (deriv (deriv (fun β => (pressure d β).toReal))) (𝓝[>] (spectralThreshold d))
      (𝓝 ((d : ℝ) / (kappa d * (spectralThreshold d) ^ 2))) := by
  have he := pressure_eventuallyEq_supercritical hd E
  have ht := (supercriticalEnergy_second_derivative_limit hd).comp
    (normalized_parameter_tendsto hd)
  have ht' := ht.const_mul ((spectralThreshold d)⁻¹ ^ 2)
  have hvalue : (spectralThreshold d)⁻¹ ^ 2 * ((d : ℝ) / kappa d) =
      (d : ℝ) / (kappa d * (spectralThreshold d) ^ 2) := by ring
  rw [hvalue] at ht'
  apply ht'.congr'
  filter_upwards [second_deriv_eventuallyEq_right_v2 he] with β hβ
  rw [hβ, second_deriv_scaled_v2]
  simp only [Function.comp_apply, div_eq_mul_inv, mul_comm]

/-- The subcritical pressure vanishes identically, hence has zero left curvature. -/
theorem pressure_second_derivative_left_v2 {d : ℕ} (hd : 12 ≤ d) (E : OnsetEndpointInputs d) :
    Tendsto (deriv (deriv (fun β => (pressure d β).toReal))) (𝓝[<] (spectralThreshold d))
      (𝓝 0) := by
  have he : ∀ β < spectralThreshold d, (fun γ => (pressure d γ).toReal) =ᶠ[𝓝 β] (fun _ => 0) := by
    intro β hβ
    filter_upwards [gt_mem_nhds hβ] with γ hγ
    simp [pressure_zero_below_v2 hd E hγ.le]
  have hd1 : ∀ β < spectralThreshold d, deriv (fun γ => (pressure d γ).toReal) β = 0 := by
    intro β hβ
    simpa using (he β hβ).deriv_eq
  apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin] with β hβ
  have he' : deriv (fun γ => (pressure d γ).toReal) =ᶠ[𝓝 β] (fun _ => 0) := by
    filter_upwards [gt_mem_nhds hβ] with γ hγ
    exact hd1 γ hγ
  simpa using he'.deriv_eq.symm

/-- Both one-sided first derivatives at the threshold vanish: `P_d` is differentiable there with
derivative `0` (quadratic onset and vanishing below). -/
theorem pressure_derivative_at_threshold_v2 {d : ℕ} (hd : 12 ≤ d) (E : OnsetEndpointInputs d) :
    HasDerivAt (fun β => (pressure d β).toReal) 0 (spectralThreshold d) := by
  obtain ⟨ε, C, hε, hC, hbound⟩ := pressure_onset_of_inputs hd E
  have hk : 0 < kappa d := LocalQuartic.kappa_positive (by omega : 11 ≤ d)
  apply zero_derivative_of_quadratic_onset (spectralThreshold_pos (by omega))
    (K := (d : ℝ) / (2 * kappa d)) (by positivity) hC hε
  · intro β hβ
    rw [pressure_zero_below_v2 hd E hβ, EReal.toReal_zero]
  · intro β hβ hβε
    obtain ⟨p, hp, hb⟩ := hbound β hβ hβε
    simpa only [hp, EReal.toReal_coe] using hb

/-- **Order parameter onset**, one constant for all global minimizers and all translations. -/
theorem order_parameter_onset_v2 {d : ℕ} (hd : 12 ≤ d) (E : OnsetEndpointInputs d) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ β in 𝓝[>] (spectralThreshold d),
      ∀ ρ : ProbabilityDensity d, IsGlobalMinimizer β ρ →
        |firstShellOrderParameter ρ.value -
          Real.sqrt (2 * (d : ℝ) / kappa d) * Real.sqrt (onsetDelta d β)| ≤ C * onsetDelta d β :=
  V2.Reaudit.MorseBott.all_minimizers_bound_v2 hd E

#print axioms pressure_derivative_at_threshold_v2
#print axioms pressure_second_derivative_right_v2
#print axioms order_parameter_onset_v2

end BecknerOnofri.V2.Onset
