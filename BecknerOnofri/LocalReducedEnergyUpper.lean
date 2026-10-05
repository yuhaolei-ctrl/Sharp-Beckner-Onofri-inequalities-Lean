import BecknerOnofri.ReducedEnergyJointExpansion
import BecknerOnofri.CriticalGraphCoercivity

/-! The actual local physical energy has the sharp upper onset coefficient. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter Asymptotics
open scoped Topology BigOperators
namespace BecknerOnofri.HighDim.LocalReducedEnergyUpper
open ContinuousFirstShell ReducedEnergyGradient ReducedQuarticExpansion ReducedPhysicalEnergy
open UniformComplementBounds

def onsetParameter (μ : ℝ) : ℝ := 1-1/μ

theorem onsetParameter_pos {μ : ℝ} (hμ : 1 < μ) : 0 < onsetParameter μ := by
  have hi : 1/μ < 1 := (div_lt_one (by linarith : 0<μ)).mpr hμ
  exact sub_pos.mpr hi

theorem parameter_distance_bound {μ : ℝ} (hμ : 1 < μ) (hμ2 : μ ≤ 2) :
    |μ-1| ≤ 2*onsetParameter μ := by
  have he : μ-1 = μ*onsetParameter μ := by
    unfold onsetParameter
    field_simp
  rw [abs_of_pos (sub_pos.mpr hμ), he]
  exact mul_le_mul_of_nonneg_right hμ2 (onsetParameter_pos hμ).le

theorem amplitude_sum_le {d : ℕ} (z : Coordinates d) :
    (∑ i : Fin d, ‖z i‖^2) ≤ (d:ℝ)*‖z‖^2 := by
  calc
    _ ≤ ∑ _i : Fin d, ‖z‖^2 := Finset.sum_le_sum
      (fun i _ => pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm z i) 2)
    _ = _ := by simp

/-- Nonnegative actual graph energy forces the amplitude onto the onset scale. -/
theorem nonnegative_energy_amplitude_bound {d : ℕ} (hd : 12 ≤ d) :
    ∀ᶠ x in 𝓝 (1,(0 : Coordinates d)), 1 < x.1 → 0 ≤ physicalReducedEnergy hd x →
      ‖x.2‖^2 ≤ (4*(d:ℝ)/kappa d)*onsetParameter x.1 := by
  obtain ⟨C,hC,hbound⟩ := (physicalReducedEnergy_joint_quartic hd).exists_pos
  have hk := kappa_pos d hd
  have ht : Tendsto (fun x : ℝ × Coordinates d => C*(‖x.2‖^2+|x.1-1|))
      (𝓝 (1,0)) (𝓝 0) := by
    have hh : ContinuousAt (fun x : ℝ × Coordinates d => C*(‖x.2‖^2+|x.1-1|)) (1,0) := by fun_prop
    simpa using hh.tendsto
  have hsmall := ht.eventually (gt_mem_nhds (show 0<kappa d/4 by positivity))
  filter_upwards [hbound.bound, hsmall] with x hx hs hμ hE
  have hδ := onsetParameter_pos hμ
  have hmass := mul_le_mul_of_nonneg_left (amplitude_sum_le x.2) hδ.le
  have hq := quarticValue_coercive hd x.2
  have he : physicalReducedEnergy hd x - onsetParameter x.1*(∑ i : Fin d, ‖x.2 i‖^2) - quarticValue x.2 ≤
      C*(‖x.2‖^6+|x.1-1| * ‖x.2‖^4) := by
    have hn : 0 ≤ ‖x.2‖^6+|x.1-1| * ‖x.2‖^4 := by positivity
    have hh := hx
    rw [Real.norm_eq_abs, Real.norm_of_nonneg hn] at hh
    exact (le_abs_self _).trans hh
  have hab := mul_le_mul_of_nonneg_right hs.le (pow_nonneg (norm_nonneg x.2) 4)
  have ht0 : 0 ≤ ‖x.2‖^2 := sq_nonneg _
  have hmain : (kappa d/4)*(‖x.2‖^2)^2 ≤ onsetParameter x.1*(d:ℝ)*‖x.2‖^2 := by
    nlinarith [hE]
  have hgoal : kappa d*‖x.2‖^2 ≤ 4*(d:ℝ)*onsetParameter x.1 := by
    by_cases ht : ‖x.2‖^2 = 0
    · rw [ht, mul_zero]
      positivity
    · have htpos : 0 < ‖x.2‖^2 := lt_of_le_of_ne ht0 (Ne.symm ht)
      have hh : (kappa d*‖x.2‖^2)*(‖x.2‖^2) ≤
          (4*(d:ℝ)*onsetParameter x.1)*(‖x.2‖^2) := by nlinarith [hmain]
      exact (mul_le_mul_iff_left₀ htpos).mp hh
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hk).mpr
  nlinarith [hgoal]

theorem quartic_model_eq {d : ℕ} (δ : ℝ) (z : Coordinates d) :
    δ*(∑ i : Fin d, ‖z i‖^2)+quarticValue z = reducedQuartic d δ (fun i => ‖z i‖^2) := by
  rw [quarticValue_eq_reducedQuartic]
  unfold reducedQuartic
  ring

/-- The sharp quartic coefficient and its full squared-amplitude coercive defect survive
in the actual physical energy, up to a cubic parameter remainder. -/
theorem nonnegative_energy_upper_with_defect {d : ℕ} (hd : 12 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x in 𝓝 (1,(0 : Coordinates d)),
      1 < x.1 → 0 ≤ physicalReducedEnergy hd x →
      physicalReducedEnergy hd x ≤ (d:ℝ)/(2*kappa d)*(onsetParameter x.1)^2 -
        kappa d/2*(∑ i : Fin d, (‖x.2 i‖^2-onsetParameter x.1/kappa d)^2) +
        C*(onsetParameter x.1)^3 := by
  obtain ⟨C,hC,hbound⟩ := (physicalReducedEnergy_joint_quartic hd).exists_pos
  let A : ℝ := 4*(d:ℝ)/kappa d
  have hd0 : (0:ℝ)<d := by exact_mod_cast (show 0<d by omega)
  have hA : 0 < A := by dsimp [A]; exact div_pos (by positivity) (kappa_pos d hd)
  refine ⟨C*(A^3+2*A^2), by positivity, ?_⟩
  filter_upwards [hbound.bound, nonnegative_energy_amplitude_bound hd, parameter_interval (d := d)]
    with x hx ha hinterval hμ hE
  have hδ := onsetParameter_pos hμ
  have hamp : ‖x.2‖^2 ≤ A*onsetParameter x.1 := ha hμ hE
  have hμδ := parameter_distance_bound hμ hinterval.2
  have h6 : ‖x.2‖^6 ≤ (A*onsetParameter x.1)^3 := by
    convert! pow_le_pow_left₀ (sq_nonneg ‖x.2‖) hamp 3 using 1 <;> ring
  have h4 : ‖x.2‖^4 ≤ (A*onsetParameter x.1)^2 := by
    convert! pow_le_pow_left₀ (sq_nonneg ‖x.2‖) hamp 2 using 1 <;> ring
  have he4 : |x.1-1| * ‖x.2‖^4 ≤ 2*onsetParameter x.1*(A*onsetParameter x.1)^2 :=
    mul_le_mul hμδ h4 (pow_nonneg (norm_nonneg _) 4) (by positivity)
  have he : physicalReducedEnergy hd x - onsetParameter x.1*(∑ i : Fin d, ‖x.2 i‖^2) - quarticValue x.2 ≤
      C*(A^3+2*A^2)*(onsetParameter x.1)^3 := by
    have hh : physicalReducedEnergy hd x - onsetParameter x.1*(∑ i : Fin d, ‖x.2 i‖^2) - quarticValue x.2 ≤
        C*(‖x.2‖^6+|x.1-1| * ‖x.2‖^4) := by
      have hn : 0 ≤ ‖x.2‖^6+|x.1-1| * ‖x.2‖^4 := by positivity
      have hh := hx
      rw [Real.norm_eq_abs, Real.norm_of_nonneg hn] at hh
      exact (le_abs_self _).trans hh
    calc
      _ ≤ C*(‖x.2‖^6+|x.1-1| * ‖x.2‖^4) := hh
      _ ≤ C*((A*onsetParameter x.1)^3+2*onsetParameter x.1*(A*onsetParameter x.1)^2) :=
        mul_le_mul_of_nonneg_left (add_le_add h6 he4) hC.le
      _ = _ := by ring
  have hq := reducedQuartic_coercive hd (onsetParameter x.1) (fun i => ‖x.2 i‖^2)
  rw [← quartic_model_eq] at hq
  linarith

theorem nonnegative_energy_upper {d : ℕ} (hd : 12 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x in 𝓝 (1,(0 : Coordinates d)),
      1 < x.1 → 0 ≤ physicalReducedEnergy hd x →
      physicalReducedEnergy hd x ≤ (d:ℝ)/(2*kappa d)*(onsetParameter x.1)^2 +
        C*(onsetParameter x.1)^3 := by
  obtain ⟨C,hC,h⟩ := nonnegative_energy_upper_with_defect hd
  refine ⟨C,hC,h.mono ?_⟩
  intro x hx hμ hE
  have hs : 0 ≤ kappa d/2*(∑ i : Fin d, (‖x.2 i‖^2-onsetParameter x.1/kappa d)^2) :=
    mul_nonneg (by have := kappa_pos d hd; positivity) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  linarith [hx hμ hE]

#print axioms nonnegative_energy_amplitude_bound
#print axioms nonnegative_energy_upper_with_defect
#print axioms nonnegative_energy_upper
end BecknerOnofri.HighDim.LocalReducedEnergyUpper
