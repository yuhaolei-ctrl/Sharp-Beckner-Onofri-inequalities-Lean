module

public import BecknerOnofri.V2.Reaudit.Final.ManuscriptTheorems
public import BecknerOnofri.V2.Onset.PressureDerivatives

@[expose] public section

/-! # `onset_manuscript` with the left-sided limits and the one-sided derivatives (Reaudit, Final)

The display `(5.pressure-derivatives)` of `cor:section5-defect-onset` reads
`P'(β_s-) = P'(β_s+) = 0`, `P''(β_s-) = 0`, `P''(β_s+) = d/(κ_d β_s²) > 0`, i.e. limits of `P'(β)`,
`P''(β)` as `β → β_s∓` and one-sided derivatives of `P` and `P'` at `β_s`.  `Onset.onset_manuscript`
states the right-hand limits only.  `onset_manuscript_full` adds, for the same `P = (pressure d ·).toReal`:

* the left limits `P'(β) → 0` and `P''(β) → 0` as `β ↑ β_s`
  (`V2.Onset.pressure_first_derivative_left_v2`, `pressure_second_derivative_left_v2`);
* `P` is differentiable at `β_s` with `P'(β_s) = 0` (`V2.Onset.pressure_derivative_at_threshold_v2`);
* `d/(κ_d β_s²) > 0`;  (the right limits used in the mean value step are
  `V2.Onset.pressure_first_derivative_right_v2`, `pressure_second_derivative_right_v2`)
* the one-sided derivatives of `P'` at `β_s`: the right one is `d/(κ_d β_s²)` and the left one is `0`
  (mean value theorem step, `hasDerivWithinAt_Ici_of_tendsto_deriv` and
  `hasDerivWithinAt_Iic_of_tendsto_deriv`).

`theorem_1_3_printed_full` is `theorem_1_3_printed` together with these conjuncts. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter Set
open scoped Topology

namespace BecknerOnofri.V2.Reaudit.Final.Onset
open BecknerOnofri.HighDim

/-- The pressure derivative `P'` has one-sided derivatives at the threshold: `d/(κ_d β_s²)` on the
right and `0` on the left. -/
theorem pressure_derivative_one_sided (d : ℕ) (hd : 12 ≤ d) :
    HasDerivWithinAt (deriv (fun γ => (pressure d γ).toReal))
        ((d : ℝ) / (kappa d * spectralThreshold d ^ 2)) (Ici (spectralThreshold d))
        (spectralThreshold d) ∧
      HasDerivWithinAt (deriv (fun γ => (pressure d γ).toReal)) 0 (Iic (spectralThreshold d))
        (spectralThreshold d) := by
  have E := SpinChannel.onsetEndpointInputs_written hd
  set P : ℝ → ℝ := fun γ => (pressure d γ).toReal with hP
  have hσ : 0 < spectralThreshold d := spectralThreshold_pos (by omega)
  have hd0 : deriv P (spectralThreshold d) = 0 :=
    (V2.Onset.pressure_derivative_at_threshold_v2 hd E).deriv
  obtain ⟨R, hR, hform, -, -, -, -⟩ :=
    MorseBott.pressure_differentiation_from_remainder hd E
  have hlim1 := V2.Onset.pressure_first_derivative_right_v2 hd E
  have hlim2 := V2.Onset.pressure_second_derivative_right_v2 hd E
  constructor
  · -- right-hand derivative
    set g : ℝ → ℝ := fun β => (d : ℝ) / (2 * kappa d) * (1 - spectralThreshold d / β) ^ 2 +
      (1 - spectralThreshold d / β) ^ 3 * R (1 - spectralThreshold d / β) with hg
    have hδa : AnalyticAt ℝ (fun β : ℝ => 1 - spectralThreshold d / β) (spectralThreshold d) :=
      analyticAt_const.sub (analyticAt_const.div analyticAt_id hσ.ne')
    have hRa : AnalyticAt ℝ (R ∘ fun β : ℝ => 1 - spectralThreshold d / β) (spectralThreshold d) :=
      hR.comp_of_eq hδa (by simp [hσ.ne'])
    have hga : AnalyticAt ℝ g (spectralThreshold d) := by
      have h1 : AnalyticAt ℝ (fun β : ℝ => (d : ℝ) / (2 * kappa d) *
          (1 - spectralThreshold d / β) ^ 2) (spectralThreshold d) :=
        analyticAt_const.mul (hδa.pow 2)
      have h2 : AnalyticAt ℝ (fun β : ℝ => (1 - spectralThreshold d / β) ^ 3 *
          R (1 - spectralThreshold d / β)) (spectralThreshold d) :=
        (hδa.pow 3).mul hRa
      exact h1.add h2
    have hPg : P =ᶠ[𝓝[>] (spectralThreshold d)] g := by
      filter_upwards [hform] with β hβ
      simpa only [hP, hg, onsetDelta] using hβ
    have hdg : ∀ᶠ y in 𝓝 (spectralThreshold d), DifferentiableAt ℝ (deriv g) y :=
      hga.deriv.eventually_analyticAt.mono fun y hy => hy.differentiableAt
    have hloc := DiagonalScalarBranch.eventually_local_right hPg
    have hS : ∀ᶠ β in 𝓝[>] (spectralThreshold d), β ∈ {β : ℝ | spectralThreshold d < β ∧
        DifferentiableAt ℝ (deriv P) β} := by
      filter_upwards [hloc, hdg.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with β h1 h2 h3
      refine ⟨h3, ?_⟩
      exact h2.congr_of_eventuallyEq (show P =ᶠ[𝓝 β] g from h1).deriv
    refine hasDerivWithinAt_Ici_of_tendsto_deriv (s := {β : ℝ | spectralThreshold d < β ∧
        DifferentiableAt ℝ (deriv P) β}) ?_ ?_ hS ?_
    · exact fun β hβ => hβ.2.differentiableWithinAt
    · rw [ContinuousWithinAt, hd0]
      exact hlim1.mono_left (nhdsWithin_mono _ (fun β hβ => hβ.1))
    · exact hlim2
  · -- left-hand derivative
    have hS : (Iio (spectralThreshold d)) ∈ 𝓝[<] (spectralThreshold d) := self_mem_nhdsWithin
    refine hasDerivWithinAt_Iic_of_tendsto_deriv (s := Iio (spectralThreshold d)) ?_ ?_ hS
      (V2.Onset.pressure_second_derivative_left_v2 hd E)
    · intro β hβ
      have h0 : deriv P =ᶠ[𝓝 β] fun _ => (0 : ℝ) := by
        filter_upwards [gt_mem_nhds (show β < spectralThreshold d from hβ)] with γ hγ
        have : P =ᶠ[𝓝 γ] fun _ => (0 : ℝ) := by
          filter_upwards [gt_mem_nhds hγ] with γ' hγ'
          simp [hP, V2.Onset.pressure_zero_below_v2 hd E hγ'.le]
        simpa using this.deriv_eq
      exact ((differentiableAt_const (0 : ℝ)).congr_of_eventuallyEq h0).differentiableWithinAt
    · rw [ContinuousWithinAt, hd0]
      exact V2.Onset.pressure_first_derivative_left_v2 hd E

/-- **`onset_manuscript` together with the left-sided limits and the one-sided derivatives of
`(5.pressure-derivatives)`.**  The first conjunct is the statement of `Onset.onset_manuscript`. -/
theorem onset_manuscript_full (d : ℕ) (hd : 12 ≤ d) :
    type_of% (onset_manuscript d hd) ∧
    -- `P'(β_s-) = 0` and `P''(β_s-) = 0`
    (Tendsto (deriv (fun γ => (pressure d γ).toReal)) (𝓝[<] (spectralThreshold d)) (𝓝 0) ∧
      Tendsto (deriv (deriv (fun γ => (pressure d γ).toReal))) (𝓝[<] (spectralThreshold d))
        (𝓝 0)) ∧
    -- `P` is differentiable at `β_s` with `P'(β_s) = 0`
    HasDerivAt (fun γ => (pressure d γ).toReal) 0 (spectralThreshold d) ∧
    -- `P''(β_s+) = d/(κ_d β_s²) > 0` and `P''(β_s-) = 0` as one-sided derivatives of `P'`
    (0 < (d : ℝ) / (kappa d * spectralThreshold d ^ 2) ∧
      HasDerivWithinAt (deriv (fun γ => (pressure d γ).toReal))
        ((d : ℝ) / (kappa d * spectralThreshold d ^ 2)) (Ici (spectralThreshold d))
        (spectralThreshold d) ∧
      HasDerivWithinAt (deriv (fun γ => (pressure d γ).toReal)) 0 (Iic (spectralThreshold d))
        (spectralThreshold d)) := by
  have E := SpinChannel.onsetEndpointInputs_written hd
  have hσ : 0 < spectralThreshold d := spectralThreshold_pos (by omega)
  have hk : 0 < kappa d := V2.Final.kappa_pos d hd
  have hdd : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  obtain ⟨h1, h2⟩ := pressure_derivative_one_sided d hd
  exact ⟨onset_manuscript d hd,
    ⟨V2.Onset.pressure_first_derivative_left_v2 hd E,
      V2.Onset.pressure_second_derivative_left_v2 hd E⟩,
    V2.Onset.pressure_derivative_at_threshold_v2 hd E,
    ⟨by positivity, h1, h2⟩⟩

end BecknerOnofri.V2.Reaudit.Final.Onset

namespace BecknerOnofri.V2.Reaudit.Final
open BecknerOnofri.HighDim

/-- **Theorem 1.3 as printed, together with the left-sided limits and the one-sided derivatives of the
pressure derivatives (`eq:section5-pressure-derivatives`).**  The first conjunct is
`theorem_1_3_printed`; the rest is the new part of `Onset.onset_manuscript_full`. -/
theorem theorem_1_3_printed_full (d : ℕ) (hd : 12 ≤ d) :
    type_of% (theorem_1_3_printed d hd) ∧
    (Tendsto (deriv (fun γ => (pressure d γ).toReal)) (nhdsWithin (spectralThreshold d)
        (Set.Iio (spectralThreshold d))) (nhds 0) ∧
      Tendsto (deriv (deriv (fun γ => (pressure d γ).toReal)))
        (nhdsWithin (spectralThreshold d) (Set.Iio (spectralThreshold d))) (nhds 0)) ∧
    HasDerivAt (fun γ => (pressure d γ).toReal) 0 (spectralThreshold d) ∧
    (0 < (d : ℝ) / (kappa d * spectralThreshold d ^ 2) ∧
      HasDerivWithinAt (deriv (fun γ => (pressure d γ).toReal))
        ((d : ℝ) / (kappa d * spectralThreshold d ^ 2)) (Set.Ici (spectralThreshold d))
        (spectralThreshold d) ∧
      HasDerivWithinAt (deriv (fun γ => (pressure d γ).toReal)) 0 (Set.Iic (spectralThreshold d))
        (spectralThreshold d)) :=
  ⟨theorem_1_3_printed d hd, (Onset.onset_manuscript_full d hd).2⟩

#print axioms Onset.onset_manuscript_full
#print axioms theorem_1_3_printed_full

end BecknerOnofri.V2.Reaudit.Final
end
