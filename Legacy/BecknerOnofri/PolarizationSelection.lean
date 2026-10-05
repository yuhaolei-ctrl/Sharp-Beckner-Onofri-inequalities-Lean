module

public import Legacy.BecknerOnofri.SubcriticalDensityCompactness
public import Legacy.BecknerOnofri.PolarizationMoment
public import Legacy.BecknerOnofri.PolarizationDensity

@[expose] public section

/-! Compact variational selection: a single actual density maximizer is fixed
by every polarization which increases energy and is strict for the chosen
moment weight. Heat-kernel comparisons and the cosine weight are separate inputs. -/
noncomputable section
namespace Legacy.BecknerOnofri.PolarizationSelection
open MeasureTheory Legacy.TorusEndpoint TorusSobolev SubcriticalPrimalDual
open SubcriticalDensityCompactness GibbsL2Continuity CoordinatePolarization

theorem inner_toLp_eq_moment {d : ℕ} {f w : Torus d → ℝ}
    (hf : MemLp f 2 (torusMeasure d)) (hw : MemLp w 2 (torusMeasure d)) :
    inner ℝ (hw.toLp w) (hf.toLp f) = ∫ x, f x*w x ∂torusMeasure d := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hw.coeFn_toLp, hf.coeFn_toLp] with x hx hy
  simp [hx, hy]

/-- No selected maximizer is assumed: compactness supplies it for any L2 weight.
The conclusion quantifies over all energy-increasing polarizations for that weight. -/
theorem exists_fixed_maximizer {d : ℕ} (hd : 0 < d) {A : ℝ}
    (hA : 1/(4*endpointConstant d) < A) (w : Torus d → ℝ)
    (hw : MemLp w 2 (torusMeasure d)) :
    ∃ r : ProbabilityDensity d, ∃ _ : MemLp r.value 2 (torusMeasure d),
      (∀ q : ProbabilityDensity d, MemLp q.value 2 (torusMeasure d) →
        densityFunctional A q ≤ densityFunctional A r) ∧
      ∀ (i : Fin d) (a : ℝ),
        (∀ x ∈ halfTorus i a, reflection i a x ≠ x → w (reflection i a x) < w x) →
        fourierEnergy r ≤ fourierEnergy (density i a r) →
        polarize i a r.value =ᵐ[torusMeasure d] r.value := by
  let L : DensityL2 d → ℝ := fun r => inner ℝ (hw.toLp w) r
  have hL : Continuous L := by fun_prop
  obtain ⟨rL, hrL, hmaxL⟩ := exists_maximal_moment hd hA L hL
  rcases hrL with ⟨r, hr, rfl, hmax⟩
  refine ⟨r, hr, hmax, ?_⟩
  intro i a hstrict hQ
  have hC : 0 < endpointConstant d := div_pos (Nat.cast_pos.mpr hd) (endpointSigma_pos hd)
  have hA0 : 0 < A := (by positivity : 0 < 1/(4*endpointConstant d)).trans hA
  let q := density i a r
  have hq : MemLp q.value 2 (torusMeasure d) := density_memLp_two i a hr
  have hqm := (rearranged_density_maximizer hA0 r q hq hmax
    (density_entropy i a (PhysicalGreenL2.finiteEntropy_of_memLp r hr)) hQ).2
  have hmem : hq.toLp q.value ∈ densityMaximizers d A := ⟨q, hq, rfl, hqm⟩
  have hupper := hmaxL _ hmem
  change inner ℝ (hw.toLp w) (hq.toLp q.value) ≤ inner ℝ (hw.toLp w) (hr.toLp r.value) at hupper
  rw [inner_toLp_eq_moment hq hw, inner_toLp_eq_moment hr hw] at hupper
  have hmono (x : Torus d) (hx : x ∈ halfTorus i a) : w (reflection i a x) ≤ w x := by
    by_cases hfix : reflection i a x = x
    · rw [hfix]
    · exact (hstrict x hx hfix).le
  have hlower := moment_polarize_le i a hr hw hmono
  exact polarize_ae_eq_of_moment_eq i a hr hw hstrict (le_antisymm hlower hupper)

#print axioms exists_fixed_maximizer
end Legacy.BecknerOnofri.PolarizationSelection
