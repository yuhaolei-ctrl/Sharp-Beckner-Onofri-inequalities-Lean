module

public import BecknerOnofri.MixtureSubsetNormalized
public import BecknerOnofri.MixtureMarginalFourier
public import BecknerOnofri.MixtureEnergyStatementBridge

@[expose] public section

/-! The two literal marginal-energy inequalities of the manuscript, with actual
Haar marginals, normalized probability mixtures, and extended Fourier energies. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ENNReal
open Finset MeasureTheory
namespace BecknerOnofri.CosineMixtureTransfer
open RectangleLattice Legacy.TorusEndpoint Legacy.BecknerOnofri
open HighDim.EntropyShearer

lemma inversePowerEnergy_congr_ae {d r : ℕ} (hr : 0 < r) {f g : Torus d → ℝ}
    (he : f =ᵐ[torusMeasure d] g) : HighDim.inversePowerEnergy r f = HighDim.inversePowerEnergy r g := by
  rw [← weightedEnergyENN_eq_inversePowerEnergy hr, ← weightedEnergyENN_eq_inversePowerEnergy hr]
  exact weightedEnergyENN_congr_ae _ he

lemma coordinateEnergy_eq_inversePower_marginal {d r : ℕ} (hr : 0 < r)
    (ρ : HighDim.ProbabilityDensity d) (I : Finset (Fin d))
    (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ) (hw : ∀ n, 0 ≤ w n) (hm : HasSum w 1)
    (he : ρ.value =ᵐ[torusMeasure d] CosineMixtureApproximation.rho w N) :
    coordinateEnergy I (r:ℝ) (CosineMixtureApproximation.rho w N) =
      HighDim.inversePowerEnergy r (HighDim.coordinateMarginal ρ I) := by
  rw [coordinateEnergy_eq_Haar_marginal I _ w N hw hm, weightedEnergyENN_eq_inversePowerEnergy hr,
    coordinateMarginal_eq]
  exact (inversePowerEnergy_congr_ae hr (fullAvg_congr_ae Iᶜ he)).symm

theorem cosine_mixture_subset_energy {d r : ℕ} (hr : 12 ≤ r) (hrd : r ≤ d)
    (ρ : HighDim.ProbabilityDensity d) (hρ : HighDim.IsCountableCosineMixture ρ) :
    HighDim.spectralEnergy ρ ≤ ENNReal.ofReal ((d:ℝ)/((r:ℝ)*(d.choose r:ℝ))) *
      ∑ I ∈ (univ : Finset (Fin d)).powersetCard r,
        HighDim.inversePowerEnergy r (HighDim.coordinateMarginal ρ I) := by
  obtain ⟨w, N, hw, hm, he⟩ := hρ
  rw [countableCosineMixture_eq] at he
  have h := countable_mixture_subset_comparison hr hrd w N hw hm.summable
  have hd0 : 0 < d := by omega
  have hr0 : 0 < r := by omega
  have hleft : weightedEnergyENN (weight (d:ℝ)) (CosineMixtureApproximation.rho w N) =
      HighDim.spectralEnergy ρ := by
    rw [weightedEnergyENN_eq_inversePowerEnergy hd0]
    exact (inversePowerEnergy_congr_ae hd0 he).symm
  rw [hleft] at h
  simpa only [coordinateEnergy_eq_inversePower_marginal hr0 ρ _ w N hw hm he] using h

theorem cosine_mixture_deletion_energy {d : ℕ} (hd : 12 ≤ d)
    (ρ : HighDim.ProbabilityDensity d) (hρ : HighDim.IsCountableCosineMixture ρ) :
    HighDim.spectralEnergy ρ ≤ ENNReal.ofReal (1/((d:ℝ)-1)) *
      ∑ i : Fin d, HighDim.inversePowerEnergy (d-1) (HighDim.coordinateMarginal ρ (univ.erase i)) := by
  obtain ⟨w, N, hw, hm, he⟩ := hρ
  rw [countableCosineMixture_eq] at he
  have h := countable_mixture_comparison_enn hd w N hw hm.summable
  have hd0 : 0 < d := by omega
  have hr0 : 0 < d-1 := by omega
  have hleft : weightedEnergyENN (weight (d:ℝ)) (CosineMixtureApproximation.rho w N) =
      HighDim.spectralEnergy ρ := by
    rw [weightedEnergyENN_eq_inversePowerEnergy hd0]
    exact (inversePowerEnergy_congr_ae hd0 he).symm
  rw [hleft] at h
  have hdel (i : Fin d) : weightedEnergyENN
      (fun k => if k i = 0 then weight ((d:ℝ)-1) k else 0) (CosineMixtureApproximation.rho w N) =
      HighDim.inversePowerEnergy (d-1) (HighDim.coordinateMarginal ρ (univ.erase i)) := by
    have hc := coordinateEnergy_eq_inversePower_marginal hr0 ρ (univ.erase i) w N hw hm he
    simpa [coordinateEnergy, Nat.cast_sub (show 1 ≤ d by omega)] using hc
  simpa only [hdel] using h

#print axioms cosine_mixture_subset_energy
#print axioms cosine_mixture_deletion_energy
end BecknerOnofri.CosineMixtureTransfer
