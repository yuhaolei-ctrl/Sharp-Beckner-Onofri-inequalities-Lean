import BecknerOnofri.ExtendedMixtureEnergy

/-! The codimension-one energy comparison for countable cosine-power mixtures,
including divergent energies. There is no spatial uniform-majorant hypothesis. -/
noncomputable section
open scoped BigOperators Topology ENNReal
open Finset MeasureTheory
namespace BecknerOnofri.CosineMixtureTransfer
open RectangleLattice RandomRectangles Legacy.TorusEndpoint
open Legacy.BecknerOnofri Legacy.D10

lemma finite_mixture_comparison_enn {α : Type*} {d : ℕ} (hd : 12 ≤ d)
    (s : Finset α) (w : α → ℝ) (N : α → Fin d → ℕ) (hw : ∀ a ∈ s, 0 ≤ w a) :
    weightedEnergyENN (weight (d:ℝ)) (CosineMixture.mixture s w N) ≤
      ENNReal.ofReal (1 / ((d:ℝ)-1)) * ∑ i : Fin d,
        weightedEnergyENN (fun k => if k i = 0 then weight ((d:ℝ)-1) k else 0)
          (CosineMixture.mixture s w N) := by
  have hg (i : Fin d) (k : Frequency d) :
      0 ≤ (if k i = 0 then weight ((d:ℝ)-1) k else 0) := by
    split_ifs
    · exact weight_nonneg _ _
    · exact le_rfl
  rw [finite_weightedEnergyENN s w N _ (weight_nonneg _)]
  simp_rw [finite_weightedEnergyENN s w N _ (hg _)]
  have hc : 0 ≤ 1 / ((d:ℝ)-1) := by
    have : (12:ℝ) ≤ d := by exact_mod_cast hd
    exact div_nonneg (by norm_num) (by linarith)
  have hn (i : Fin d) : 0 ≤ deletionEnergy ((d:ℝ)-1) (CosineMixture.mixture s w N) i :=
    tsum_nonneg (fun k => mul_nonneg (hg i k) (sq_nonneg _))
  change ENNReal.ofReal (energy _ _) ≤ _ * ∑ i, ENNReal.ofReal (deletionEnergy _ _ i)
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hn i), ← ENNReal.ofReal_mul hc]
  exact ENNReal.ofReal_le_ofReal (finite_mixture_comparison_ge12 hd s w N hw)

/-- The first inequality in the manuscript's marginal-energy proposition,
expressed by the Fourier mask of each coordinate marginal. -/
theorem countable_mixture_comparison_enn {d : ℕ} (hd : 12 ≤ d)
    (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ) (hw : ∀ n, 0 ≤ w n) (hs : Summable w) :
    weightedEnergyENN (weight (d:ℝ)) (CosineMixtureApproximation.rho w N) ≤
      ENNReal.ofReal (1 / ((d:ℝ)-1)) * ∑ i : Fin d,
        weightedEnergyENN (fun k => if k i = 0 then weight ((d:ℝ)-1) k else 0)
          (CosineMixtureApproximation.rho w N) := by
  apply weightedEnergyENN_le_of_partial_bounds w N hw hs
  intro m
  apply (finite_mixture_comparison_enn hd (range m) w N (fun n _ => hw n)).trans
  gcongr with i
  apply partial_weightedEnergyENN_le w N hw hs
  intro k
  split_ifs
  · exact weight_nonneg _ _
  · exact le_rfl

#print axioms finite_mixture_comparison_enn
#print axioms countable_mixture_comparison_enn
end BecknerOnofri.CosineMixtureTransfer
