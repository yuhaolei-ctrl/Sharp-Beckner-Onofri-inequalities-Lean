module

public import BecknerOnofri.CountableMixtureSubsetMarginal
public import BecknerOnofri.MixtureSubsetEnergy

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ENNReal
open Finset MeasureTheory
namespace BecknerOnofri.CosineMixtureTransfer
open RectangleLattice RandomRectangles Legacy.TorusEndpoint
open Legacy.BecknerOnofri Legacy.D10
open HighDim.EntropyShearer

lemma weightedEnergyENN_congr_ae {d : ℕ} (g : Frequency d → ℝ) {f h : Torus d → ℝ}
    (he : f =ᵐ[torusMeasure d] h) : weightedEnergyENN g f = weightedEnergyENN g h := by
  have hc (k : Frequency d) : densityFourier f k = densityFourier h k :=
    integral_congr_ae (he.mono (fun x hx => by dsimp only; rw [hx]))
  unfold weightedEnergyENN
  simp_rw [hc]

lemma componentCoeff_maskIndex {d : ℕ} (I : Finset (Fin d)) (N : Fin d → ℕ)
    (k : Frequency d) : componentCoeff (maskIndex I N) k =
      if ∀ i ∉ I, k i = 0 then componentCoeff N k else 0 := by
  classical
  by_cases h : ∀ i ∉ I, k i = 0
  · rw [if_pos h]
    unfold componentCoeff binomialProduct
    apply prod_congr rfl
    intro i hi
    by_cases hI : i ∈ I
    · simp only [maskIndex, hI, if_true]
    · simp only [maskIndex, hI, if_false, h i hI, Int.natAbs_zero, coeff_zero]
  · rw [if_neg h]
    push_neg at h
    obtain ⟨i, hI, hki⟩ := h
    unfold componentCoeff binomialProduct
    apply prod_eq_zero (mem_univ i)
    simp only [maskIndex, hI, if_false]
    exact coeff_eq_zero (Int.natAbs_pos.mpr hki)

lemma rho_fourier_maskIndex {d : ℕ} (I : Finset (Fin d)) (w : ℕ → ℝ)
    (N : ℕ → Fin d → ℕ) (hw : ∀ n, 0 ≤ w n) (hs : Summable w) (k : Frequency d) :
    densityFourier (CosineMixtureApproximation.rho w (fun n => maskIndex I (N n))) k =
      if ∀ i ∉ I, k i = 0 then densityFourier (CosineMixtureApproximation.rho w N) k else 0 := by
  classical
  simp only [rho_fourier w _ hw hs, componentCoeff_maskIndex]
  by_cases h : ∀ i ∉ I, k i = 0
  · simp only [if_pos h]
  · simp only [if_neg h, mul_zero, tsum_zero, Complex.ofReal_zero]

lemma coordinateEnergy_eq_maskIndex {d : ℕ} (I : Finset (Fin d)) (p : ℝ) (w : ℕ → ℝ)
    (N : ℕ → Fin d → ℕ) (hw : ∀ n, 0 ≤ w n) (hs : Summable w) :
    coordinateEnergy I p (CosineMixtureApproximation.rho w N) =
      weightedEnergyENN (weight p) (CosineMixtureApproximation.rho w (fun n => maskIndex I (N n))) := by
  classical
  unfold coordinateEnergy weightedEnergyENN
  apply tsum_congr
  intro k
  rw [rho_fourier_maskIndex I w N hw hs]
  dsimp only
  by_cases h : ∀ i ∉ I, k i = 0
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]
    simp

theorem coordinateEnergy_eq_Haar_marginal {d : ℕ} (I : Finset (Fin d)) (p : ℝ)
    (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ) (hw : ∀ n, 0 ≤ w n) (hm : HasSum w 1) :
    coordinateEnergy I p (CosineMixtureApproximation.rho w N) =
      weightedEnergyENN (weight p) (fullAvg Iᶜ (CosineMixtureApproximation.rho w N)) :=
  (coordinateEnergy_eq_maskIndex I p w N hw hm.summable).trans
    (weightedEnergyENN_congr_ae (weight p) (fullAvg_countable_mixture_subset I w N hw hm)).symm

#print axioms coordinateEnergy_eq_Haar_marginal
end BecknerOnofri.CosineMixtureTransfer
