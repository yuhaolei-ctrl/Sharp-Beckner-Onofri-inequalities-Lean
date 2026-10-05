import BecknerOnofri.LocalElevenCore.QuadraticCorrectionCoefficients
import BecknerOnofri.LocalElevenCore.GraphWienerBounds

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace BecknerOnofri.HighDim.LocalEleven.QuadraticSlaving
open ContinuousGibbs ContinuousFirstShell ContinuousComplement QuadraticModes
open GraphRegularity GraphWienerBounds
open Legacy.BecknerOnofri.RadialWiener BecknerOnofri.OnsetWienerBounds

lemma inverseGreen_coefficient_bound {d : ℕ} (hd : 11≤d) (u : Space d) (k : Frequency d) :
    ‖coefficient k (inverseGreen hd u).val‖≤‖coefficient k u‖ := by
  by_cases hk : ComplementFrequency k
  · rw [inverseGreen_factor,resolvent_coefficient hd _ hk,
      BecknerOnofri.HighDim.QuadraticModes.complementMap_coefficient,if_pos hk]
    have he := complement_eigenvalue_ge_thirtytwo hd hk
    have hp : 0<frequencyLength k^d-1 := by linarith
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (div_pos zero_lt_one hp)]
    exact mul_le_of_le_one_left (norm_nonneg _) ((div_le_one hp).mpr (by linarith))
  · rw [(mem_complement_fourier_iff _).mp (inverseGreen hd u).property k hk,norm_zero]
    exact norm_nonneg _

lemma inverseGreen_radial {d : ℕ} (hd : 11≤d) (m : ℕ) (u : Space d) (hu : Radial m u) :
    Radial m (inverseGreen hd u).val := by
  apply hu.of_nonneg_of_le
    (fun k => mul_nonneg ((radialWeight_isWeight m).nonneg k) (norm_nonneg _))
  intro k
  exact mul_le_mul_of_nonneg_left (inverseGreen_coefficient_bound hd u k)
    ((radialWeight_isWeight m).nonneg k)

lemma inverseGreen_wienerSize_le {d : ℕ} (hd : 11≤d) (m : ℕ) (u : Space d) (hu : Radial m u) :
    wienerSize m (inverseGreen hd u).val≤wienerSize m u := by
  apply (inverseGreen_radial hd m u hu).tsum_le_tsum _ hu
  intro k
  exact mul_le_mul_of_nonneg_left (inverseGreen_coefficient_bound hd u k)
    ((radialWeight_isWeight m).nonneg k)

#print axioms inverseGreen_wienerSize_le
end BecknerOnofri.HighDim.LocalEleven.QuadraticSlaving
