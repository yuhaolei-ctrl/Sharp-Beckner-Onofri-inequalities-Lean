import BecknerOnofri.EndpointDuality
import BecknerOnofri.FirstShellSharpness

/-! Exact coefficient-threshold consequence of the density endpoint.
The still-unproved density endpoint is an explicit premise of this reduction. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace BecknerOnofri.HighDim

theorem zero_inCriticalSobolev (d : ℕ) :
    InCriticalSobolev (fun _ : Torus d => (0 : ℝ)) := by
  constructor
  · exact memLp_const (0 : ℝ)
  · have he : potentialTerm (fun _ : Torus d => (0 : ℝ)) =
        (fun _ : NonzeroFrequency d => (0 : ℝ)) := by
      funext k
      simp [potentialTerm, fourierCoeff]
    rw [he]
    exact summable_zero

theorem coefficientDefect_nonneg (d : ℕ) (A : ℝ) : 0 ≤ coefficientDefect d A := by
  have h := le_iSup_of_le (fun _ : Torus d => (0 : ℝ))
    (le_iSup_of_le (zero_inCriticalSobolev d) le_rfl)
      (f := fun u : Torus d → ℝ => ⨆ (_ : InCriticalSobolev u),
        logPartition u - (A * potentialEnergy u : ℝ))
  simpa [coefficientDefect, logPartition, centered, potentialEnergy, potentialTerm, fourierCoeff]
    using h

theorem coefficientDefect_spectral_zero_of_primal {d : ℕ} (hd : 0 < d)
    (hP : ∀ u : Torus d → ℝ, InCriticalSobolev u →
      logPartition u ≤ ((spectralCoefficient d * potentialEnergy u : ℝ) : EReal)) :
    coefficientDefect d (spectralCoefficient d) = 0 := by
  apply le_antisymm ?_ (coefficientDefect_nonneg _ _)
  unfold coefficientDefect
  refine iSup_le (fun u => iSup_le (fun hu => ?_))
  have h := hP u hu
  rw [logPartition_eq_log_integral hd u hu] at h ⊢
  have hr : Real.log (∫ x, Real.exp (centered u x) ∂torusMeasure d) ≤
      spectralCoefficient d * potentialEnergy u := by exact_mod_cast h
  exact_mod_cast sub_nonpos.mpr hr

theorem coefficient_threshold_of_density {d : ℕ} (hd : 0 < d)
    (hE : ∀ ρ : ProbabilityDensity d, ρ.FiniteEntropy →
      spectralEnergy ρ ≤ ENNReal.ofReal (2 * entropy ρ)) :
    IsLeast {A : ℝ | 0 < A ∧ coefficientDefect d A = 0} (spectralCoefficient d) := by
  constructor
  · refine ⟨by unfold spectralCoefficient; positivity, ?_⟩
    exact coefficientDefect_spectral_zero_of_primal hd
      (fun u hu => (potential_endpoint_of_density hd hE u hu).2)
  · intro A hA
    by_contra hn
    have hpos := coefficientDefect_pos_of_lt_spectral hd (lt_of_not_ge hn)
    rw [hA.2] at hpos
    exact lt_irrefl _ hpos

#print axioms coefficient_threshold_of_density
end BecknerOnofri.HighDim
