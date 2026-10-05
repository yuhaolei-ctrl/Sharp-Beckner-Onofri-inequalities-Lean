import Challenge
import Paper2Definitions

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators
namespace BecknerOnofri.Paper2
open HighDim

theorem negativeSobolevEnergy_normalization {d : ℕ} (ρ : ProbabilityDensity d) :
    ENNReal.ofReal ((2 * Real.pi) ^ d) * negativeSobolevEnergy ρ =
      spectralEnergy ρ := by
  sorry

theorem negativeSobolevEnergy_fourier {d : ℕ} (ρ : ProbabilityDensity d) :
    negativeSobolevEnergy ρ = negativeSobolevFourierSeries ρ := by
  sorry

theorem low_density_extended (d : ℕ) (hd : 1 ≤ d) (hd10 : d ≤ 10)
    (ρ : ProbabilityDensity d) :
    (((d : ℝ) / spectralThreshold d : ℝ) : EReal) *
      (ENNReal.ofReal ((2 * Real.pi) ^ d) * negativeSobolevEnergy ρ).toEReal ≤
        extendedEntropy ρ := by
  sorry

theorem high_density_extended (d : ℕ) (hd : 12 ≤ d)
    (ρ : ProbabilityDensity d) :
    ((1 / 2 : ℝ) : EReal) *
      (ENNReal.ofReal ((2 * Real.pi) ^ d) * negativeSobolevEnergy ρ).toEReal ≤
        extendedEntropy ρ := by
  sorry

theorem physicalSpectralPowerGraph_scaling {d : ℕ}
    (α : Friedrichs.MixedSpatial.MultiIndex d) (s : ℝ)
    (f g : Friedrichs.MixedSpatial.H α)
    (h : Friedrichs.MixedSpatial.SpectralPowerGraph α s f g) :
    physicalSpectralPowerGraph α s f (((2 * Real.pi) ^ 2) ^ s • g) := by
  sorry

theorem periodization_derivatives_locally_uniform (is : List (Fin 11)) :
    TendstoLocallyUniformly
      (fun S : Finset (Frequency 11) => fun x : Periodization.E =>
        ∑ n ∈ S, Periodization.mixed is
          (fun y => Eleven.euclideanProfile (fun j => y j+(n j:ℝ))) x)
      (fun x : Periodization.E => ∑' n : Frequency 11,
        Periodization.mixed is
          (fun y => Eleven.euclideanProfile (fun j => y j+(n j:ℝ))) x) Filter.atTop := by
  sorry

theorem physical_fractional_intertwining (d : ℕ) :
    Physical.FractionalIntertwining d := by
  sorry

theorem physical_operatorGraph_transport {d : ℕ} (α : Friedrichs.MixedSpatial.MultiIndex d)
    (f g : Friedrichs.MixedSpatial.H α) :
    Physical.operatorGraph α (Physical.coordinateLpEquiv α f)
      (Physical.scale^2 • Physical.coordinateLpEquiv α g) ↔
      Friedrichs.MixedSpatial.operatorGraph α f g := by
  sorry

theorem physical_spectralPower_domain {d : ℕ} (α : Friedrichs.MixedSpatial.MultiIndex d)
    (s : ℝ) (f : Friedrichs.MixedSpatial.H α) :
    (∃ g : Physical.H α, Physical.SpectralPowerGraph α s (Physical.coordinateLpEquiv α f) g) ↔
      ∃ g : Friedrichs.MixedSpatial.H α, Friedrichs.MixedSpatial.SpectralPowerGraph α s f g := by
  sorry

theorem physical_measure_transport {d : ℕ} (α : Friedrichs.MixedSpatial.MultiIndex d) :
    (Friedrichs.MixedSpatial.spatialMeasure α).map Physical.down =
      ENNReal.ofReal (Physical.scale^d) • Physical.spatialMeasure α := by
  sorry

theorem physical_form_transport {d : ℕ} (α : Friedrichs.MixedSpatial.MultiIndex d) :
    Physical.energyEquiv α '' Friedrichs.MixedSpatial.formClosure α = Physical.formClosure α := by
  sorry

theorem physical_potential (m : ℕ) (x : ℝ) :
    Physical.potentialFactor m x ^ 2 =
      (2*Real.pi)^2 * ((m:ℝ)*((m:ℝ)-1)) / Real.sin (2*Real.pi*x)^2 := by
  sorry

end BecknerOnofri.Paper2
