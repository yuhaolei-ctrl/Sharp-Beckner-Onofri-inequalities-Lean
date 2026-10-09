module

public import BecknerOnofri.V2.Onset.Assembly
public import BecknerOnofri.V2.Onset.Kappa
public import BecknerOnofri.PressureRegularity

@[expose] public section

/-! # Pressure onset (equation `eq:intro-pressure-onset`)

The pressure equals the dual value of the explicit full-mode branch (`optimizer_pressure`), whose
expansion `(-1/(4 q_{d,d})) δ² + O(δ³) = (d/(2κ_d)) δ² + O(δ³)` is the full-support case of the
supported energy expansion together with `q_{d,d} = -κ_d/(2d)` (`Kappa`). -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped Topology

namespace BecknerOnofri.V2.Onset
open BecknerOnofri.HighDim ContinuousGibbs ContinuousSymmetry
open BecknerOnofri.HighDim.LocalEleven

/-- The explicit branch energy expansion in the `μ` variable, with `δ = 1 - 1/μ`. -/
theorem branch_energy_expansion {d : ℕ} (hd : 12 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ μ in 𝓝[>] (1 : ℝ),
      |(dualFunctional (μ * spectralThreshold d)
          (LocalEleven.DiagonalScalarBranch.branchPotential (by omega : 11 ≤ d)
            (LocalEleven.DiagonalScalarBranch.amplitude (by omega : 11 ≤ d) μ))).toReal -
        (d : ℝ) / (2 * kappa d) * (1 - 1 / μ) ^ 2| ≤ C * (1 - 1 / μ) ^ 3 := by
  have hd11 : 11 ≤ d := by omega
  have hne : (Finset.univ : Finset (Fin d)).Nonempty :=
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  have hO := (SupportedFamily.branch_profile hd11 Finset.univ hne).2
  rw [Finset.card_univ, Fintype.card_fin, neg_one_div_four_branchQuartic_self hd11] at hO
  obtain ⟨c, hc⟩ := hO.bound
  have hδ : Tendsto (fun μ : ℝ => 1 - 1 / μ) (𝓝[>] 1) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have : ContinuousAt (fun μ : ℝ => 1 - 1 / μ) 1 :=
        continuousAt_const.sub (continuousAt_const.div continuousAt_id one_ne_zero)
      simpa using this.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with μ hμ
      have : 1 < μ := hμ
      simp only [Set.mem_Ioi]
      have : 1 / μ < 1 := by rw [div_lt_one (by linarith)]; exact this
      linarith
  refine ⟨max c 0, le_max_right _ _, ?_⟩
  filter_upwards [hδ.eventually hc, SupportedFamily.full_branch_identification hd11,
    hδ.eventually (self_mem_nhdsWithin : (Set.Ioi (0 : ℝ)) ∈ 𝓝[>] (0 : ℝ)),
    self_mem_nhdsWithin] with μ hb hid hpos hp
  have hμ : (1 : ℝ) < μ := hp
  have hδpos : 0 < 1 - 1 / μ := hpos
  have hfac : 1 / (1 - (1 - 1 / μ)) * spectralThreshold d = μ * spectralThreshold d := by
    rw [sub_sub_cancel, one_div_one_div]
  rw [hfac, hid] at hb
  simp only [Real.norm_eq_abs, abs_of_pos hδpos, abs_of_nonneg (pow_nonneg hδpos.le 3)] at hb
  refine hb.trans ?_
  have : 0 ≤ (1 - 1 / μ) ^ 3 := by positivity
  exact mul_le_mul_of_nonneg_right (le_max_left _ _) this

/-- The pressure is the dual value of the explicit branch. -/
theorem pressure_eq_branch_dual {d : ℕ} (hd : 12 ≤ d) (E : OnsetEndpointInputs d) :
    ∀ᶠ μ in 𝓝[>] (1 : ℝ),
      pressure d (μ * spectralThreshold d) =
        dualFunctional (μ * spectralThreshold d)
          (LocalEleven.DiagonalScalarBranch.branchPotential (by omega : 11 ≤ d)
            (LocalEleven.DiagonalScalarBranch.amplitude (by omega : 11 ≤ d) μ)) := by
  filter_upwards [branch_eventually_optimizer_v2 hd E, self_mem_nhdsWithin] with μ hopt hp
  have hβ : 0 < μ * spectralThreshold d :=
    mul_pos (by change 1 < μ at hp; linarith) (spectralThreshold_pos (by omega))
  exact GlobalPressureOnset.optimizer_pressure (by omega) hβ _ hopt.1 hopt.2.2

/-- **Pressure onset.**  `P_d(β) = (d/(2κ_d)) (1 - β_s/β)² + O((β - β_s)³)`, with finite pressure. -/
theorem pressure_onset_of_inputs {d : ℕ} (hd : 12 ≤ d) (E : OnsetEndpointInputs d) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 ≤ C ∧
      ∀ β : ℝ, spectralThreshold d < β → β < spectralThreshold d + ε →
        ∃ p : ℝ, pressure d β = (p : EReal) ∧
          |p - (d : ℝ) / (2 * kappa d) * (1 - spectralThreshold d / β) ^ 2| ≤
            C * (β - spectralThreshold d) ^ 3 := by
  have hd11 : 11 ≤ d := by omega
  have hσ : 0 < spectralThreshold d := spectralThreshold_pos (by omega)
  obtain ⟨C0, hC0, hexp⟩ := branch_energy_expansion hd
  have hall : ∀ᶠ β in 𝓝[>] (spectralThreshold d),
      pressure d β = dualFunctional β
          (LocalEleven.DiagonalScalarBranch.physicalPotential hd11 β) ∧
      |(dualFunctional β (LocalEleven.DiagonalScalarBranch.physicalPotential hd11 β)).toReal -
        (d : ℝ) / (2 * kappa d) * (1 - 1 / (β / spectralThreshold d)) ^ 2| ≤
          C0 * (1 - 1 / (β / spectralThreshold d)) ^ 3 ∧ β < 2 * (d : ℝ) := by
    have hlt : ∀ᶠ β in 𝓝[>] (spectralThreshold d), β < 2 * (d : ℝ) :=
      (show ∀ᶠ β in 𝓝 (spectralThreshold d), β < 2 * (d : ℝ) from
        Iio_mem_nhds (spectral_subcritical_gap hd)).filter_mono nhdsWithin_le_nhds
    have h := (LocalEleven.DiagonalScalarBranch.normalized_parameter_tendsto hd11).eventually
      ((pressure_eq_branch_dual hd E).and hexp)
    filter_upwards [h, hlt] with β hβ hlt
    have hμ : β / spectralThreshold d * spectralThreshold d = β := div_mul_cancel₀ _ hσ.ne'
    obtain ⟨h1, h2⟩ := hβ
    rw [hμ] at h1 h2
    exact ⟨h1, h2, hlt⟩
  obtain ⟨r, hr, hBall⟩ := Metric.mem_nhdsWithin_iff.mp hall
  refine ⟨r, C0 / spectralThreshold d ^ 3, hr, by positivity, ?_⟩
  intro β hβ hupper
  have hmem : β ∈ Metric.ball (spectralThreshold d) r ∩ Set.Ioi (spectralThreshold d) := by
    refine ⟨?_, hβ⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (sub_pos.mpr hβ)]
    linarith
  obtain ⟨hpr, hbd, hlt⟩ := hBall hmem
  have hβ0 : 0 < β := hσ.trans hβ
  obtain ⟨M, hM⟩ := pressure_bounded_above (by omega) hβ0.le hlt
  have hlo : (0 : EReal) ≤ pressure d β := pressure_nonneg d β
  have hnt : pressure d β ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top M) hM
  have hnb : pressure d β ≠ ⊥ := fun h => by
    rw [h] at hlo
    exact absurd hlo (by simp)
  refine ⟨(pressure d β).toReal, (EReal.coe_toReal hnt hnb).symm, ?_⟩
  rw [← hpr] at hbd
  have hδ : 1 - 1 / (β / spectralThreshold d) = 1 - spectralThreshold d / β := by
    rw [one_div_div]
  rw [hδ] at hbd
  refine hbd.trans ?_
  have hδ0 : 0 ≤ 1 - spectralThreshold d / β := by
    rw [sub_nonneg, div_le_one hβ0]; exact hβ.le
  have hδle : 1 - spectralThreshold d / β ≤ (β - spectralThreshold d) / spectralThreshold d := by
    have : 1 - spectralThreshold d / β = (β - spectralThreshold d) / β := by field_simp
    rw [this]
    exact div_le_div_of_nonneg_left (by linarith) hσ hβ.le
  have h3 := pow_le_pow_left₀ hδ0 hδle 3
  calc C0 * (1 - spectralThreshold d / β) ^ 3
      ≤ C0 * (((β - spectralThreshold d) / spectralThreshold d) ^ 3) :=
        mul_le_mul_of_nonneg_left h3 hC0
    _ = C0 / spectralThreshold d ^ 3 * (β - spectralThreshold d) ^ 3 := by
        rw [div_pow]; ring

#print axioms pressure_onset_of_inputs

end BecknerOnofri.V2.Onset
