module

public import BecknerOnofri.HeatL1Convergence
public import BecknerOnofri.PotentialRigidity
public import BecknerOnofri.FiniteEntropyEnergy
public import BecknerOnofri.Uniform

@[expose] public section

/-! Positivity of the interaction for every nonuniform finite-entropy density.
Fourier uniqueness is obtained on the entire L1 domain by heat smoothing. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped Topology
namespace BecknerOnofri.HighDim
open Legacy.BecknerOnofri.TorusSobolev Legacy.BecknerOnofri.HeatDensityApproximation
open HeatApproximation

lemma density_uniform_of_fourier_nonzero_eq_zero {d : ℕ} (ρ : ProbabilityDensity d)
    (h : ∀ k : Frequency d, k ≠ 0 → fourierCoeff ρ.value k = 0) :
    ρ.value =ᵐ[torusMeasure d] (fun _ => 1) := by
  have hconst : MemLp (fun _ : Torus d => (1:ℝ)) 2 (torusMeasure d) := memLp_const 1
  have heatEq {t : ℝ} (ht : 0 < t) : heatValue (Bridge.density ρ) t =ᵐ[torusMeasure d] (fun _ => 1) := by
    have he : heatLp (Bridge.density ρ) ht = Bridge.potentialLp (fun _ => 1) hconst := by
      apply (fourierIsometry d).injective
      ext k
      rw [heatLp_fourier,Bridge.potentialLp_fourier]
      by_cases hk : k = 0
      · subst k
        have hz : fourierCoeff ρ.value 0 = 1 := Legacy.TorusEndpoint.densityFourier_zero (Bridge.density ρ)
        rw [show fourierCoeff (Bridge.density ρ).value 0 = 1 from hz]
        simp [Legacy.TorusEndpoint.TorusHeatBounds.heatWeight,
          fourierCoeff,UnitAddTorus.mFourier_zero,Legacy.TorusEndpoint.GreenMultiplierSummability.radiusSq]
      · rw [show fourierCoeff (Bridge.density ρ).value k = 0 from h k hk,mul_zero]
        exact (uniformDensity_fourierCoeff_nonzero k hk).symm
    have hae := ContinuousFirstShell.toL2_ae (d := d)
      ⟨heatValue (Bridge.density ρ) t,heatValue_continuous (Bridge.density ρ) ht⟩
    change heatLp (Bridge.density ρ) ht =ᵐ[torusMeasure d]
      (fun x => (heatValue (Bridge.density ρ) t x : ℂ)) at hae
    rw [he] at hae
    filter_upwards [hae,Bridge.potentialLp_ae (fun _ : Torus d => (1:ℝ)) hconst] with x hx hy
    exact Complex.ofReal_injective (hx.symm.trans hy)
  let t : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  have ht (n : ℕ) : 0 < t n := by dsimp [t]; positivity
  have ht0 : Tendsto t atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hl := heat_l1_tendsto (Bridge.density ρ) t ht ht0
  have he (n : ℕ) : l1distance (heatValue (Bridge.density ρ) (t n)) ρ.value =
      l1distance (fun _ => 1) ρ.value := by
    apply integral_congr_ae
    filter_upwards [heatEq (ht n)] with x hx
    rw [hx]
  change Tendsto (fun n => l1distance (heatValue (Bridge.density ρ) (t n)) ρ.value) atTop (𝓝 0) at hl
  simp only [he] at hl
  have hz : l1distance (fun _ => 1) ρ.value = 0 := tendsto_nhds_unique tendsto_const_nhds hl
  have hz' := (integral_eq_zero_iff_of_nonneg (fun x : Torus d => norm_nonneg ((1:ℝ)-ρ.value x))
    ((integrable_const 1).sub ρ.integrable).norm).mp hz
  filter_upwards [hz'] with x hx
  exact (sub_eq_zero.mp (norm_eq_zero.mp hx)).symm

lemma scalar_spectral_energy_nonneg {d : ℕ} (ρ : ProbabilityDensity d) :
    0 ≤ ∑' k, spectralTerm ρ k := tsum_nonneg (fun k => by
  unfold spectralTerm frequencyLength
  positivity)

lemma scalar_spectral_energy_zero_iff {d : ℕ} (hd : 0 < d)
    (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy) :
    (∑' k, spectralTerm ρ k) = 0 ↔ ρ.value =ᵐ[torusMeasure d] (fun _ => 1) := by
  constructor
  · intro hz
    apply density_uniform_of_fourier_nonzero_eq_zero ρ
    intro k hk
    have hle := (finiteEntropy_spectralTerm_summable hd ρ hρ).le_tsum
      ⟨k,hk⟩ (fun j hj => by unfold spectralTerm frequencyLength; positivity)
    rw [hz] at hle
    have hw : 0 < (frequencyLength k^d)⁻¹ := inv_pos.mpr
      (pow_pos (Legacy.TorusEndpoint.frequencyRadius_pos hk) _)
    have hn : ‖fourierCoeff ρ.value k‖^2 ≤ 0 := by
      change (frequencyLength k^d)⁻¹*‖fourierCoeff ρ.value k‖^2 ≤ 0 at hle
      nlinarith [sq_nonneg ‖fourierCoeff ρ.value k‖]
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm hn (sq_nonneg _)))
  · intro he
    calc
      (∑' k, spectralTerm ρ k) = ∑' _ : NonzeroFrequency d, (0:ℝ) := by
        apply tsum_congr
        intro k
        simp only [spectralTerm,fourierCoeff_congr_ae he,
          fourierCoeff_one_nonzero k.val k.property,norm_zero,zero_pow (by decide : 2 ≠ 0),mul_zero]
      _ = 0 := tsum_zero

lemma scalar_spectral_energy_pos_iff {d : ℕ} (hd : 0 < d)
    (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy) :
    0 < ∑' k, spectralTerm ρ k ↔ ¬ (ρ.value =ᵐ[torusMeasure d] (fun _ => 1)) := by
  rw [← scalar_spectral_energy_zero_iff hd ρ hρ]
  exact (lt_iff_le_and_ne).trans (by simp [scalar_spectral_energy_nonneg ρ,eq_comm])

#print axioms density_uniform_of_fourier_nonzero_eq_zero
#print axioms scalar_spectral_energy_pos_iff
end BecknerOnofri.HighDim
