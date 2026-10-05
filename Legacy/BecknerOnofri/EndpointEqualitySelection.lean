import Legacy.BecknerOnofri.EndpointEqualityCompactness
import Legacy.BecknerOnofri.PolarizationSelection
import Legacy.BecknerOnofri.SteinerSelection

/-! Genuine endpoint Steiner selection at a fixed entropy level. Starting
from an actual equality density, the selected smooth Euler density preserves
its entropy; no endpoint-wide compactness or subcritical coefficient is used. -/
noncomputable section
open MeasureTheory Set
namespace Legacy.BecknerOnofri.EndpointEqualitySelection
open Legacy.TorusEndpoint TorusSobolev SubcriticalAttainment SubcriticalEuler
open SubcriticalPrimalDual GibbsL2Continuity CoordinatePolarization
open EndpointMaximizerLevel EndpointEqualityCompactness PolarizationSelection
open SteinerSelection SteinerFromPolarization SmoothFourier WienerFourier

variable {d : ℕ} (hd : 0 < d) (hEndpoint : Endpoint d) {b Ab A : ℝ}
  (hb : 0 < b) (hR : RoughExponentialBound d b Ab) (hA : 0 < A)
  (hCoeff : 1/(4*A) = endpointConstant d)

include hd hEndpoint hb hR hA hCoeff
theorem exists_fixed_equality (r₀ : ProbabilityDensity d)
    (hr₀ : MemLp r₀.value 2 (torusMeasure d))
    (he₀ : densityEntropy r₀.value = endpointConstant d * fourierEnergy r₀)
    (w : Torus d → ℝ) (hw : MemLp w 2 (torusMeasure d)) :
    ∃ r : ProbabilityDensity d, ∃ _ : MemLp r.value 2 (torusMeasure d),
      densityEntropy r.value = densityEntropy r₀.value ∧
      densityEntropy r.value = endpointConstant d * fourierEnergy r ∧
      ∀ (i : Fin d) (a : ℝ),
        (∀ x ∈ halfTorus i a, reflection i a x ≠ x → w (reflection i a x) < w x) →
        fourierEnergy r ≤ fourierEnergy (density i a r) →
        polarize i a r.value =ᵐ[torusMeasure d] r.value := by
  let E := densityEntropy r₀.value
  have hE : 0 ≤ E := densityEntropy_nonneg_of_finite r₀ (PhysicalGreenL2.finiteEntropy_of_memLp r₀ hr₀)
  have hcompact := densityLevel_isCompact hd hEndpoint hb hR hA hCoeff hE
  have hn : (densityLevel d E).Nonempty := ⟨hr₀.toLp r₀.value, r₀, hr₀, rfl, rfl, he₀⟩
  let L : DensityL2 d → ℝ := fun r => inner ℝ (hw.toLp w) r
  have hL : Continuous L := by fun_prop
  obtain ⟨rL, hrL, hmaxL⟩ := hcompact.exists_isMaxOn hn hL.continuousOn
  rcases hrL with ⟨r, hr, rfl, hEnt, he⟩
  refine ⟨r, hr, hEnt, he, ?_⟩
  intro i a hstrict hQ
  let q := density i a r
  have hq : MemLp q.value 2 (torusMeasure d) := density_memLp_two i a hr
  have hqm := rearranged_density_maximizer hA r q hq
    (equality_density_maximizer hEndpoint hCoeff r he)
    (density_entropy i a (PhysicalGreenL2.finiteEntropy_of_memLp r hr)) hQ
  have hqE : densityEntropy q.value = E :=
    (density_entropy i a (PhysicalGreenL2.finiteEntropy_of_memLp r hr)).trans hEnt
  have hqe : densityEntropy q.value = endpointConstant d * fourierEnergy q := by
    have hz := hqm.1
    simp only [densityFunctional, hCoeff, he, sub_self] at hz
    exact (sub_eq_zero.mp hz).symm
  have hmem : hq.toLp q.value ∈ densityLevel d E := ⟨q, hq, rfl, hqE, hqe⟩
  have hupper := hmaxL hmem
  change inner ℝ (hw.toLp w) (hq.toLp q.value) ≤ inner ℝ (hw.toLp w) (hr.toLp r.value) at hupper
  rw [inner_toLp_eq_moment hq hw, inner_toLp_eq_moment hr hw] at hupper
  have hmono (x : Torus d) (hx : x ∈ halfTorus i a) : w (reflection i a x) ≤ w x := by
    by_cases hfix : reflection i a x = x
    · rw [hfix]
    · exact (hstrict x hx hfix).le
  exact polarize_ae_eq_of_moment_eq i a hr hw hstrict
    (le_antisymm (moment_polarize_le i a hr hw hmono) hupper)

theorem exists_steiner_equality (r : ProbabilityDensity d)
    (hr : MemLp r.value 2 (torusMeasure d))
    (he : densityEntropy r.value = endpointConstant d * fourierEnergy r) :
    ∃ u : TorusL2 d, Admissible u ∧
      (∀ v : TorusL2 d, Admissible v → functional A v ≤ functional A u) ∧
      Steiner (smoothGibbsValue u) ∧ Steiner (fun x => (representative u x).re) ∧
      densityEntropy (smoothGibbsValue u) = densityEntropy r.value := by
  obtain ⟨q, hq, hEnt, hqe, hfixed⟩ := exists_fixed_equality hd hEndpoint hb hR hA hCoeff
    r hr he (CosineMomentWeight.weight d) (CosineMomentWeight.weight_memLp d)
  have hmax := equality_density_maximizer hEndpoint hCoeff q hqe
  have hqinv : OriginPolarizationInvariant q.value := by
    intro i a ha ha0
    exact hfixed i a (CosineMomentWeight.weight_strict i ha ha0)
      (fourierEnergy_polarize_le hd i a q hq)
  let u := dualPotential A q hq
  have hu : Admissible u := dualPotential_admissible hd A q hq
  have humax := (density_maximizer_dual hd hR hA q hq hmax).2
  have hs := maximizer_fourier_summable hd hR hA hu humax
  have hEq : smoothGibbsValue u =ᵐ[torusMeasure d] q.value :=
    (smoothGibbsValue_ae_eq u hs).trans (density_maximizer_gibbs hd hR hA q hq hmax).symm
  have hinv : OriginPolarizationInvariant (smoothGibbsValue u) := by
    intro i a ha ha0
    exact (polarize_congr_ae i a hEq).trans ((hqinv i a ha ha0).trans hEq.symm)
  have hst := steiner_of_origin_invariant (smoothGibbsValue_continuous u hs) hinv
  exact ⟨u, hu, humax, hst, steiner_of_normalized_exp (partition_pos hR hu) hst,
    (densityEntropy_congr_ae hEq).trans hEnt⟩

#print axioms exists_fixed_equality
#print axioms exists_steiner_equality
end Legacy.BecknerOnofri.EndpointEqualitySelection
