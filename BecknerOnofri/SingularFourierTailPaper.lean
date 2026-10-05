import BecknerOnofri.ContinuousMixtureMajorant
import BecknerOnofri.EntropyTailCountableMixture
import BecknerOnofri.EntropyTailCertifiedScalar

/-! The source singular Fourier-tail proposition on every smooth probability
mixture, with the majorant derived rather than added as a hypothesis. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators
namespace BecknerOnofri.HighDim.EntropyTail

theorem smooth_mixture_singular_tail (ρ : ProbabilityDensity 12)
    (hs : SmoothOnTorus ρ.value) (hρ : IsCountableCosineMixture ρ) :
    (1/2 : ℝ)*(∑' k : Frequency 12,scalarTailWeight k*‖fourierCoeff ρ.value k‖^2) ≤
      ∑ i : Fin 12,((21/1000)*‖fourierCoeff ρ.value (Pi.single i (2 : ℤ))‖^2+
        (27/40)*∑' j : ℕ,‖fourierCoeff ρ.value (Pi.single i (j+3 : ℤ))‖^2/(j+3 : ℝ)) := by
  obtain ⟨w,N,hw,hm,he⟩ := hρ
  have he' : ρ.value =ᵐ[torusMeasure 12] Legacy.BecknerOnofri.CosineMixtureApproximation.rho w N := he
  have hSup := CosineMixtureTransfer.mixture_majorant_of_continuous ρ.value
    (UniformFourier.smooth_continuous hs) w N hw hm.summable he'
  have htail := countable_mixture_tail_of_scalar scalarTail_le_budget w N hw hm.summable hSup
  have hf (k : Frequency 12) : fourierCoeff ρ.value k=
      fourierCoeff (Legacy.BecknerOnofri.CosineMixtureApproximation.rho w N) k := by
    apply integral_congr_ae
    filter_upwards [he'] with x hx
    rw [hx]
  simp_rw [hf]
  exact htail

#print axioms smooth_mixture_singular_tail
end BecknerOnofri.HighDim.EntropyTail
