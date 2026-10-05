import BecknerOnofri.LocalElevenContinuousInverse
import BecknerOnofri.FirstShellProduct
import BecknerOnofri.LocalElevenCore.ComplexFirstShellMoments
import BecknerOnofri.ContinuousGibbsCubic

/-! Exact Fourier multiplication by arbitrary full first-shell functions. -/
noncomputable section
set_option autoImplicit false

open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace BecknerOnofri.HighDim.LocalEleven.QuadraticModes

open BecknerOnofri.HighDim.QuadraticModes hiding actual_quartic_coefficients amplitude_sum_square assembly_fourth_moment assembly_product_coefficient assembly_quartic_cumulant assembly_second_moment assembly_third_moment complementGreen_synthesis complementMap_center complementMap_const complementMap_synthesis complementMap_synthesis_zero complementSynthesis green_complementMap green_synthesis inverseGreen_factor mixedAmplitudeSum off_diagonal_sum quadraticCorrection_eq_resolvent quadraticSource_expansion quadraticSource_value quadratic_schur_identity quartic_slaving_contribution resolvent resolventPair resolventPair_apply resolventPair_synthesis resolvent_synthesis schur_diagonal schur_double_sum schur_off_diagonal shellSquare_first_coefficient shellSquare_mean shellSquare_projection sourcePair sourcePair_diagonal sourcePair_off_diagonal source_norm_moment source_norm_sq synthesis_complex synthesis_mem_complement synthesis_product_coefficient

open ContinuousGibbs ContinuousFirstShell

theorem synthesis_complex {d : ℕ} (k : Frequency d) (z : ℂ) (x : Torus d) :
    ((synthesis k z x : ℝ):ℂ) =
      z*UnitAddTorus.mFourier k x + conj z*UnitAddTorus.mFourier (-k) x := by
  rw [synthesis_apply, ← Complex.add_conj]
  simp only [map_mul, UnitAddTorus.mFourier_neg]

theorem synthesis_product_coefficient {d : ℕ} (f : Space d) (k l : Frequency d) (z : ℂ) :
    coefficient l (synthesis k z * f) =
      z * coefficient (l-k) f + conj z * coefficient (l+k) f := by
  have hi (m : Frequency d) (w : ℂ) :
      Integrable (fun x : Torus d => w*(UnitAddTorus.mFourier (-m) x*(f x:ℂ))) (torusMeasure d) :=
    (continuous_const.mul ((UnitAddTorus.mFourier (-m)).continuous.mul
      (Complex.continuous_ofReal.comp f.continuous))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  simp only [coefficient_integral]
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (hi (l-k) z) (hi (l+k) (conj z))]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by
    dsimp only
    rw [ContinuousMap.mul_apply, Complex.ofReal_mul, synthesis_complex]
    have h₁ : UnitAddTorus.mFourier (-(l-k)) x =
        UnitAddTorus.mFourier (-l) x * UnitAddTorus.mFourier k x := by
      rw [neg_sub, sub_eq_add_neg, UnitAddTorus.mFourier_add, mul_comm]
    have h₂ : UnitAddTorus.mFourier (-(l+k)) x =
        UnitAddTorus.mFourier (-l) x * UnitAddTorus.mFourier (-k) x := by
      rw [neg_add, UnitAddTorus.mFourier_add]
    rw [h₁,h₂]
    ring)

theorem assembly_product_coefficient {d : ℕ} (f : Space d) (z : Coordinates d) (k : Frequency d) :
    coefficient k (assembly d z * f) = ∑ i : Fin d,
      (z i * coefficient (k-axisFrequency i) f + conj (z i) * coefficient (k+axisFrequency i) f) := by
  rw [assembly_apply, Finset.sum_mul, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact synthesis_product_coefficient f _ k (z i)

#print axioms assembly_product_coefficient
end BecknerOnofri.HighDim.LocalEleven.QuadraticModes
