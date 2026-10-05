module

public import BecknerOnofri.EntropyTailCountableMixture

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace BecknerOnofri.HighDim.EntropyTail

def fullFourierEnergy (f : Torus 12 → ℝ) : ℝ :=
  ∑' k : Frequency 12, (frequencyLength k^12)⁻¹*‖fourierCoeff f k‖^2

theorem fullWeight_le_one (k : Frequency 12) : (frequencyLength k^12)⁻¹ ≤ 1 := by
  by_cases hk : k=0
  · subst k
    simp [frequencyLength]
  have hn : 1 ≤ latticeSquare k := by
    have h := (latticeSquare_eq_zero_iff k).not.mpr hk
    omega
  apply inv_le_one_of_one_le₀
  rw [frequencyLength_pow_eq]
  exact Real.one_le_rpow (by exact_mod_cast hn) (by positivity)

theorem fullFourierEnergy_summable {f : Torus 12 → ℝ} (hf : Continuous f) :
    Summable (fun k : Frequency 12 => (frequencyLength k^12)⁻¹*‖fourierCoeff f k‖^2) := by
  have hs := CosineMixtureTransfer.summable_fourier_sq hf
  apply hs.of_nonneg_of_le
  · intro k
    exact mul_nonneg (inv_nonneg.mpr (pow_nonneg (Real.sqrt_nonneg _) _)) (sq_nonneg _)
  · intro k
    exact mul_le_of_le_one_left (sq_nonneg _) (fullWeight_le_one k)

attribute [local irreducible] RectangleLattice.box

theorem fullFourierEnergy_split {f : Torus 12 → ℝ} (hf : Continuous f) :
    fullFourierEnergy f =
      (∑ k ∈ RectangleLattice.box (fun _ : Fin 12 => 1), (frequencyLength k^12)⁻¹*‖fourierCoeff f k‖^2)+
      (∑' k : Frequency 12, scalarTailWeight k*‖fourierCoeff f k‖^2) := by
  classical
  have h := finite_complement_tsum (fun k : Frequency 12 => (frequencyLength k^12)⁻¹*‖fourierCoeff f k‖^2)
    (fullFourierEnergy_summable hf) (RectangleLattice.box (fun _ : Fin 12 => 1))
  have he : (∑' k : Frequency 12, scalarTailWeight k*‖fourierCoeff f k‖^2) =
      (∑' k : Frequency 12, (frequencyLength k^12)⁻¹*‖fourierCoeff f k‖^2)-
        ∑ k ∈ RectangleLattice.box (fun _ : Fin 12 => 1), (frequencyLength k^12)⁻¹*‖fourierCoeff f k‖^2 := by
    rw [← h]
    apply tsum_congr
    intro k
    simp only [scalarTailWeight, outsideCube_iff_not_mem]
    split_ifs <;> simp only [zero_mul]
  unfold fullFourierEnergy
  linarith

#print axioms fullFourierEnergy_split
end BecknerOnofri.HighDim.EntropyTail
