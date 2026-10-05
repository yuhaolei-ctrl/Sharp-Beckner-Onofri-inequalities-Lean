module

public import BecknerOnofri.CountableMixtureExtendedComparison
public import BecknerOnofri.MixtureMarginals

@[expose] public section

noncomputable section
open scoped BigOperators Topology ENNReal
open Finset MeasureTheory Filter
namespace BecknerOnofri.CosineMixtureTransfer
open RectangleLattice RandomRectangles Legacy.TorusEndpoint
open Legacy.BecknerOnofri Legacy.D10

/-- Nonzero mass, already established by the summable integral-norm theorem,
also certifies integrability without a pointwise majorant. -/
lemma rho_integrable_mass_one {d : ℕ} (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ)
    (hw : ∀ n, 0 ≤ w n) (hm : HasSum w 1) :
    Integrable (CosineMixtureApproximation.rho w N) (torusMeasure d) := by
  apply Integrable.of_integral_ne_zero
  rw [CosineMixtureApproximation.rho_mass w N hw hm]
  norm_num

lemma deletionEnergyENN_drop {d : ℕ} (i : Fin (d+1)) (p : ℝ) (w : ℕ → ℝ)
    (N : ℕ → Fin (d+1) → ℕ) (hw : ∀ n, 0 ≤ w n) (hs : Summable w) :
    weightedEnergyENN (fun k => if k i = 0 then weight p k else 0)
      (CosineMixtureApproximation.rho w N) =
    weightedEnergyENN (weight p) (CosineMixtureApproximation.rho w (fun n => drop i (N n))) := by
  let f : Frequency (d+1) → ℝ≥0∞ := fun k =>
    ENNReal.ofReal ((if k i = 0 then weight p k else 0) *
      ‖densityFourier (CosineMixtureApproximation.rho w N) k‖^2)
  have hsupport : Function.support f ⊆ Set.range (i.insertNth (0:ℤ)) := by
    intro k hk
    have hki : k i = 0 := by
      by_contra h
      exact hk (by simp [f, h])
    exact ⟨drop i k, Fin.insertNth_eq_iff.mpr ⟨hki.symm, rfl⟩⟩
  have ht := (Fin.insertNth_right_injective (α := fun _ => ℤ) (p := i) (0:ℤ)).tsum_eq hsupport
  change (∑' k, f k) = _
  rw [← ht]
  apply tsum_congr
  intro k
  simp only [f, Fin.insertNth_apply_same, if_true, weight_insert,
    rho_fourier_insert i w N hw hs]

theorem countable_mixture_dimension_transfer_enn {d : ℕ} (hd : 11 ≤ d)
    (w : ℕ → ℝ) (N : ℕ → Fin (d+1) → ℕ) (hw : ∀ n, 0 ≤ w n) (hs : Summable w) :
    weightedEnergyENN (weight ((d+1:ℕ):ℝ)) (CosineMixtureApproximation.rho w N) ≤
      ENNReal.ofReal (1/(d:ℝ)) * ∑ i : Fin (d+1), weightedEnergyENN (weight (d:ℝ))
        (CosineMixtureApproximation.rho w (fun n => drop i (N n))) := by
  have h := countable_mixture_comparison_enn (by omega : 12 ≤ d+1) w N hw hs
  simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right,
    deletionEnergyENN_drop _ _ w N hw hs] using h

#print axioms rho_integrable_mass_one
#print axioms deletionEnergyENN_drop
#print axioms countable_mixture_dimension_transfer_enn
end BecknerOnofri.CosineMixtureTransfer
