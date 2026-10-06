module

public import BecknerOnofri.SelectedChannelEntropyEta
public import BecknerOnofri.SelectedEntropyRigidity
public import BecknerOnofri.SpinFiniteStateInequality
public import BecknerOnofri.EntropyTailLarge

@[expose] public section

/-!
# The global entropy estimate for selected maximizers (Proposition 5.10)

For the selected density `ρ_u` of a maximizer, with `t = \hat ρ(e_1)`,
`Ent(ρ) - (2π)^{12}/2 ‖ρ‖²_{\dot H^{-6}} ≥ t⁴/200`. The ingredients are Lemma 5.13 (the scalar
tail, proved), Proposition 5.11 (the singular Fourier tail), Proposition 5.12(i) (conditional
entropy with the Jensen remainder) and Proposition 5.12(ii) (the finite-state inequality).
Lemma 5.17 (`ψ ≤ γ`) and the numerical part of Lemma 5.19 enter as explicit hypotheses until
their certificates are attached.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set
open scoped BigOperators

namespace BecknerOnofri.HighDim.SelectedNumericalModel
open Legacy.TorusEndpoint Legacy.BecknerOnofri TorusSobolev ConditionalEntropy

/-- Proposition 5.12(i) for the selected density, with the full tail sums. -/
theorem selected_channel_entropy_eta {u : TorusL2 12} (hu : Selected u)
    (hminor : ∀ t ∈ Ico (0 : ℝ) 1, Spin.psi t ≤ CircleScalar.gamma t) :
    (∀ i : Fin 12, Summable (fun n : ℕ =>
      (∫ x, (spinDensity hu).value x * (fourier (n+3 : ℤ) (x i)).re ∂torusMeasure 12)^2 /
        (n+3 : ℝ))) ∧
    2 * Spin.relativeEntropy (Spin.countLaw (Spin.channelLaw (spinDensity hu))) Spin.reference +
      12 * Spin.psi (Spin.mean (Spin.countLaw (Spin.channelLaw (spinDensity hu)))) +
      Spin.eta (Spin.mean (Spin.countLaw (Spin.channelLaw (spinDensity hu)))) *
        (Spin.relativeEntropy (Spin.countLaw (Spin.channelLaw (spinDensity hu))) Spin.reference -
          12 * Spin.binaryCost (Spin.mean (Spin.countLaw (Spin.channelLaw (spinDensity hu))))) +
      (21/1000) * (∑ i : Fin 12,
        (∫ x, (spinDensity hu).value x * (fourier 2 (x i)).re ∂torusMeasure 12)^2) +
      (67/100) * (∑ i : Fin 12, ∑' n : ℕ,
        (∫ x, (spinDensity hu).value x * (fourier (n+3 : ℤ) (x i)).re ∂torusMeasure 12)^2 /
          (n+3 : ℝ)) ≤
      entropy (spinDensity hu) := by
  set t := Spin.mean (Spin.countLaw (Spin.channelLaw (spinDensity hu)))
  let a := fun (i : Fin 12) (n : ℕ) =>
    (∫ x, (spinDensity hu).value x * (fourier (n+3 : ℤ) (x i)).re ∂torusMeasure 12)^2 / (n+3 : ℝ)
  let A := 2 * Spin.relativeEntropy (Spin.countLaw (Spin.channelLaw (spinDensity hu))) Spin.reference +
    12 * Spin.psi t + Spin.eta t *
      (Spin.relativeEntropy (Spin.countLaw (Spin.channelLaw (spinDensity hu))) Spin.reference -
        12 * Spin.binaryCost t) +
    (21/1000) * (∑ i : Fin 12,
      (∫ x, (spinDensity hu).value x * (fourier 2 (x i)).re ∂torusMeasure 12)^2)
  have ha (i : Fin 12) (n : ℕ) : 0 ≤ a i n := by dsimp [a]; positivity
  have hf (s : Finset ℕ) :
      A + (67/100) * (∑ n ∈ s, ∑ i : Fin 12, a i n) ≤ entropy (spinDensity hu) := by
    rw [Finset.sum_comm]
    exact selected_channel_entropy_eta_finite hu hminor s
  obtain ⟨hs, hb⟩ := nonnegative_budget_limit (fun n => ∑ i : Fin 12, a i n)
    (fun n => Finset.sum_nonneg (fun i _ => ha i n)) A (entropy (spinDensity hu)) (67/100)
    (by norm_num) hf
  have hi (i : Fin 12) : Summable (a i) :=
    hs.of_nonneg_of_le (ha i) (fun n => Finset.single_le_sum (fun j _ => ha j n)
      (Finset.mem_univ i))
  refine ⟨hi, ?_⟩
  rw [Summable.tsum_finsetSum (fun i _ => hi i)] at hb
  exact hb

/-- **Proposition 5.10** for the selected density:
`Ent(ρ) - ½ ∑_{k≠0} |k|^{-12} |\hat ρ(k)|² ≥ t⁴/200`. -/
theorem selected_entropy_gap
    (hminor : ∀ t ∈ Ico (0 : ℝ) 1, Spin.psi t ≤ CircleScalar.gamma t)
    (hB : ∀ t ∈ Icc (1 / 16 : ℝ) (99 / 100), t ^ 4 / 200 < Spin.pressureScalar t)
    {u : TorusL2 12} (hu : Selected u) :
    (Spin.mean (Spin.countLaw (Spin.channelLaw (spinDensity hu)))) ^ 4 / 200 ≤
      HighDim.entropy (spinDensity hu) -
        (1/2 : ℝ) * EntropyTail.fullFourierEnergy (spinDensity hu).value := by
  have htail := selected_tail_of_scalar EntropyTail.scalarTail_le_budget hu
  have hent := (selected_channel_entropy_eta hu hminor).2
  simp only [← density_axis_norm_sq hu] at hent
  have hcube := Spin.cube_half_energy_eq_quadratic (spinDensity hu) (spinDensity_mixture hu)
    (selected_spin_exchangeable hu)
  have hsplit := EntropyTail.fullFourierEnergy_split (spinDensity_continuous hu)
  have hspin := Spin.finite_state_inequality_of_pressure hB (selected_spin_mean_range hu)
    (p := Spin.countLaw (Spin.channelLaw (spinDensity hu))) ⟨selected_spin_feasible hu, rfl⟩
  unfold Spin.penalized Spin.functional at hspin
  linarith

/-- The selected maximizer vanishes (Proposition 5.9 for `d = 12`). -/
theorem selected_zero
    (hminor : ∀ t ∈ Ico (0 : ℝ) 1, Spin.psi t ≤ CircleScalar.gamma t)
    (hB : ∀ t ∈ Icc (1 / 16 : ℝ) (99 / 100), t ^ 4 / 200 < Spin.pressureScalar t)
    {u : TorusL2 12} (hu : Selected u) : u = 0 := by
  have h := (selected_entropy_gap hminor hB hu).trans (selected_entropy_deficit_nonpos hu)
  have hz : Spin.mean (Spin.countLaw (Spin.channelLaw (spinDensity hu))) = 0 := by
    have h4 : (Spin.mean (Spin.countLaw (Spin.channelLaw (spinDensity hu)))) ^ 4 = 0 := by
      nlinarith [pow_nonneg (selected_spin_mean_range hu).1 4]
    exact (pow_eq_zero_iff (by decide : 4 ≠ 0)).mp h4
  exact selected_zero_of_uniform hu (selected_uniform_of_mean_zero hu hz)

end BecknerOnofri.HighDim.SelectedNumericalModel
