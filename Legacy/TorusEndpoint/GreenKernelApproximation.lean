module

public import Legacy.TorusEndpoint.GreenKernelReal
public import Legacy.TorusEndpoint.FinitePhysicalBound
public import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
public import Mathlib.MeasureTheory.Group.Prod

@[expose] public section

/-!
# Actual finite Green-kernel approximation on the Haar product torus

A cofinal finite-frequency sequence exists on the countable actual lattice.
An almost-everywhere convergent subsequence pulls back under `(x,y) ↦ x-y`
by Haar quasi-measure preservation. No common lower bound is supplied.
-/

open MeasureTheory Filter
open scoped Topology

namespace Legacy.TorusEndpoint.GreenKernelApproximation

open GreenMultiplierSummability GreenKernelReal PhysicalFiniteFourier

set_option maxHeartbeats 600000

theorem exists_monotone_frequency_exhaustion (d : ℕ) :
    ∃ s : ℕ → Finset (Frequency d), Monotone s ∧ Tendsto s atTop atTop :=
  exists_seq_monotone_tendsto_atTop_atTop (Finset (Frequency d))

theorem ae_subtraction {d : ℕ} {p : Torus d → Prop}
    (h : ∀ᵐ z ∂torusMeasure d, p z) :
    ∀ᵐ xy ∂(torusMeasure d).prod (torusMeasure d), p (xy.1 - xy.2) := by
  letI : (torusMeasure d).IsAddRightInvariant := by
    rw [torusMeasure_explicit]
    infer_instance
  exact (quasiMeasurePreserving_sub_of_right_invariant
    (torusMeasure d) (torusMeasure d)).ae h

/-- Actual, unconditional existence of product-a.e. convergent finite kernels. -/
theorem exists_finiteKernel_tendsto_sub_ae (d : ℕ) :
    ∃ s : ℕ → Finset (Frequency d), Monotone s ∧ Tendsto s atTop atTop ∧
      ∀ᵐ xy ∂(torusMeasure d).prod (torusMeasure d),
        Tendsto (fun n => finiteKernel (s n) (greenMultiplier d) (xy.1 - xy.2))
          atTop (𝓝 (realGreen d (xy.1 - xy.2))) := by
  obtain ⟨s, hsmono, hs⟩ := exists_monotone_frequency_exhaustion d
  obtain ⟨ns, hns, hae⟩ := exists_subsequence_finiteKernel_tendsto_ae s hs
  refine ⟨s ∘ ns, hsmono.comp hns.monotone, hs.comp hns.tendsto_atTop, ?_⟩
  exact ae_subtraction hae

/-- Removing the zero frequency does not change these actual finite kernels. -/
lemma finiteKernel_nonzero_subtype {d : ℕ} (s : Finset (Frequency d)) (x : Torus d) :
    finiteKernel ((s.subtype (fun k => k ≠ 0)).map (nonzeroFrequencyEmbedding d))
      (greenMultiplier d) x = finiteKernel s (greenMultiplier d) x := by
  classical
  change finiteKernel ((s.subtype (fun k => k ≠ 0)).map
    (Function.Embedding.subtype _)) (greenMultiplier d) x = _
  rw [Finset.subtype_map]
  unfold finiteKernel
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : k = 0
  · simp [hk]
  · simp [hk]

/-- The same actual approximation in the existing nonzero-frequency index type. -/
theorem exists_nonzero_finiteKernel_tendsto_sub_ae (d : ℕ) :
    ∃ s : ℕ → Finset (NonzeroFrequency d),
      ∀ᵐ xy ∂(torusMeasure d).prod (torusMeasure d),
        Tendsto (fun n => finiteKernel ((s n).map (nonzeroFrequencyEmbedding d))
          (greenMultiplier d) (xy.1 - xy.2)) atTop
          (𝓝 (realGreen d (xy.1 - xy.2))) := by
  classical
  obtain ⟨s, _, _, hae⟩ := exists_finiteKernel_tendsto_sub_ae d
  refine ⟨fun n => (s n).subtype (fun k => k ≠ 0), ?_⟩
  simpa only [finiteKernel_nonzero_subtype] using hae

end Legacy.TorusEndpoint.GreenKernelApproximation

#print axioms Legacy.TorusEndpoint.GreenKernelApproximation.exists_monotone_frequency_exhaustion
#print axioms Legacy.TorusEndpoint.GreenKernelApproximation.ae_subtraction
#print axioms Legacy.TorusEndpoint.GreenKernelApproximation.exists_finiteKernel_tendsto_sub_ae
#print axioms Legacy.TorusEndpoint.GreenKernelApproximation.exists_nonzero_finiteKernel_tendsto_sub_ae
