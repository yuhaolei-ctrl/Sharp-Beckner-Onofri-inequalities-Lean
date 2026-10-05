import BecknerOnofri.LocalReducedEnergyUpper

/-! A matching energy lower bound forces every first-shell direction to be active. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology BigOperators
namespace BecknerOnofri.HighDim.LocalReducedEnergyUpper
open ContinuousFirstShell ReducedEnergyGradient

theorem onsetParameter_tendsto {d : ℕ} :
    Tendsto (fun x : ℝ × Coordinates d => onsetParameter x.1) (𝓝 (1,0)) (𝓝 0) := by
  have hc : ContinuousAt onsetParameter 1 :=
    continuousAt_const.sub (continuousAt_const.div continuousAt_id (by norm_num))
  convert! hc.tendsto.comp (continuous_fst.continuousAt :
    Tendsto (Prod.fst : ℝ × Coordinates d → ℝ) (𝓝 (1,0)) (𝓝 1)) using 1 <;>
    simp only [onsetParameter, div_one, sub_self]

/-- No stationarity is assumed: the actual local energy value alone forces its squared
amplitudes within a cubic squared-distance error of the uniform amplitude. -/
theorem near_optimal_amplitude_bound {d : ℕ} (hd : 12 ≤ d) (C₀ : ℝ) (hC₀ : 0 ≤ C₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x in 𝓝 (1,(0 : Coordinates d)),
      1 < x.1 → 0 ≤ physicalReducedEnergy hd x →
      (d:ℝ)/(2*kappa d)*(onsetParameter x.1)^2 - C₀*(onsetParameter x.1)^3 ≤ physicalReducedEnergy hd x →
      (∑ i : Fin d, (‖x.2 i‖^2-onsetParameter x.1/kappa d)^2) ≤ C*(onsetParameter x.1)^3 := by
  obtain ⟨B,hB,hupper⟩ := nonnegative_energy_upper_with_defect hd
  have hk := kappa_pos d hd
  refine ⟨2*(B+C₀)/kappa d, by positivity, hupper.mono ?_⟩
  intro x hx hμ hE hlow
  have hh := hx hμ hE
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hk).mpr
  nlinarith

/-- Any local point with the matching onset energy has full coordinate support. -/
theorem near_optimal_full_support {d : ℕ} (hd : 12 ≤ d) (C₀ : ℝ) (hC₀ : 0 ≤ C₀) :
    ∀ᶠ x in 𝓝 (1,(0 : Coordinates d)),
      1 < x.1 → 0 ≤ physicalReducedEnergy hd x →
      (d:ℝ)/(2*kappa d)*(onsetParameter x.1)^2 - C₀*(onsetParameter x.1)^3 ≤ physicalReducedEnergy hd x →
      ∀ i : Fin d, x.2 i ≠ 0 := by
  obtain ⟨C,hC,hamp⟩ := near_optimal_amplitude_bound hd C₀ hC₀
  have hk := kappa_pos d hd
  have ht := (onsetParameter_tendsto (d := d)).const_mul (C*(kappa d)^2)
  simp only [mul_zero] at ht
  have hsmall := ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2))
  filter_upwards [hamp,hsmall] with x hx hs hμ hE hlow i hi
  have hδ := onsetParameter_pos hμ
  have hab := hx hμ hE hlow
  have hsingle : (‖x.2 i‖^2-onsetParameter x.1/kappa d)^2 ≤
      ∑ j : Fin d, (‖x.2 j‖^2-onsetParameter x.1/kappa d)^2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (‖x.2 j‖^2-onsetParameter x.1/kappa d)) (Finset.mem_univ i)
  rw [hi, norm_zero, zero_pow (by decide : (2:ℕ)≠0), zero_sub, neg_sq, div_pow] at hsingle
  have hle : (onsetParameter x.1)^2 ≤ C*(onsetParameter x.1)^3*(kappa d)^2 :=
    (div_le_iff₀ (sq_pos_of_pos hk)).mp (hsingle.trans hab)
  have hlt := mul_lt_mul_of_pos_right hs (sq_pos_of_pos hδ)
  nlinarith [sq_pos_of_pos hδ]

#print axioms near_optimal_amplitude_bound
#print axioms near_optimal_full_support
end BecknerOnofri.HighDim.LocalReducedEnergyUpper
