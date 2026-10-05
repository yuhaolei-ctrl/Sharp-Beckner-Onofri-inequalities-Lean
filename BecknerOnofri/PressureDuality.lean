module

public import BecknerOnofri.PressureRegularity
public import BecknerOnofri.ThresholdReduction
public import BecknerOnofri.RawAttainment
public import Legacy.BecknerOnofri.SubcriticalPrimalDual
public import BecknerOnofri.HeatEnergyLimit
public import Mathlib.Topology.Instances.EReal.Lemmas

@[expose] public section

/-! Actual Gibbs comparison and strict positivity above the spectral threshold. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal BigOperators Topology
namespace BecknerOnofri.HighDim

theorem coefficientDefect_le_pressure {d : ℕ} (hd : 0 < d) {β : ℝ}
    (hβ : 0 < β) :
    coefficientDefect d (spectralThreshold d / (2 * β * (2 * Real.pi) ^ d)) ≤
      pressure d β := by
  let A := spectralThreshold d / (2 * β * (2 * Real.pi) ^ d)
  have hσ := spectralThreshold_pos hd
  have hA : 0 < A := by dsimp [A]; positivity
  have hAn : 0 < A * (2 * Real.pi) ^ d := by positivity
  have hC : 0 < Legacy.BecknerOnofri.endpointConstant d :=
    div_pos (Nat.cast_pos.mpr hd) (Legacy.TorusEndpoint.endpointSigma_pos hd)
  have hR := GenericAttainment.rough_bound hd
    (by positivity : 0 < Legacy.BecknerOnofri.endpointConstant d / 2)
    (by linarith : Legacy.BecknerOnofri.endpointConstant d / 2 <
      Legacy.BecknerOnofri.endpointConstant d)
  have he : 1 / (4 * (A * (2 * Real.pi) ^ d)) = β / (2 * spectralThreshold d) := by
    dsimp [A]
    field_simp
    <;> ring
  unfold coefficientDefect
  refine iSup_le (fun u => iSup_le (fun hu => ?_))
  have hadm := Legacy.BecknerOnofri.SobolevCentering.center_admissible hd
    (Bridge.potentialLp_real u hu.1) (Bridge.potentialLp_summable hd u hu)
  let r := Legacy.BecknerOnofri.SubcriticalEuler.gibbsDensity hR hadm
  have hr : (Bridge.rawDensity r).FiniteEntropy :=
    Legacy.BecknerOnofri.SubcriticalEuler.gibbsDensity_finiteEntropy hR hadm
  have hD := Legacy.BecknerOnofri.SubcriticalPrimalDual.dual_le_gibbs hd hR hAn hadm
  change _ ≤ Legacy.BecknerOnofri.SubcriticalPrimalDual.densityFunctional
    (A * (2 * Real.pi) ^ d) r at hD
  have hterms : Legacy.BecknerOnofri.fourierEnergy r =
      ∑' k, spectralTerm (Bridge.rawDensity r) k := by
    exact tsum_congr (Bridge.densitySpectralTerm_eq (Bridge.rawDensity r))
  unfold Legacy.BecknerOnofri.SubcriticalPrimalDual.densityFunctional at hD
  rw [he, hterms] at hD
  change RawAttainment.rawFunctional A u ≤ pressure d β
  rw [RawAttainment.rawFunctional_eq_legacy hd A u hu]
  calc
    _ ≤ ((β / (2 * spectralThreshold d) * (∑' k, spectralTerm (Bridge.rawDensity r) k) -
        entropy (Bridge.rawDensity r) : ℝ) : EReal) := by exact_mod_cast hD
    _ = (β / (2 * spectralThreshold d) : ℝ) * (spectralEnergy (Bridge.rawDensity r)).toEReal -
        (entropy (Bridge.rawDensity r) : EReal) := by
      rw [spectralEnergy_coe_eq_tsum hd _ hr]
      norm_cast
    _ ≤ pressure d β := le_iSup_of_le (Bridge.rawDensity r) (le_iSup_of_le hr le_rfl)

theorem pressure_pos_of_spectral_lt {d : ℕ} (hd : 0 < d) {β : ℝ}
    (hβ : spectralThreshold d < β) : 0 < pressure d β := by
  have hσ := spectralThreshold_pos hd
  have hβ0 : 0 < β := hσ.trans hβ
  have hc : 0 < (2 * Real.pi) ^ d := by positivity
  have hA : spectralThreshold d / (2 * β * (2 * Real.pi) ^ d) < spectralCoefficient d := by
    unfold spectralCoefficient
    apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith
  exact (coefficientDefect_pos_of_lt_spectral hd hA).trans_le
    (coefficientDefect_le_pressure hd hβ0)

theorem l2_density_le_coefficientDefect {d : ℕ} (hd : 0 < d) {A : ℝ}
    (hA : 0 < A) (ρ : Legacy.TorusEndpoint.ProbabilityDensity d)
    (hρ : MemLp ρ.value 2 (Legacy.TorusEndpoint.torusMeasure d)) :
    (Legacy.BecknerOnofri.SubcriticalPrimalDual.densityFunctional
      (A * (2 * Real.pi) ^ d) ρ : EReal) ≤ coefficientDefect d A := by
  have hC : 0 < Legacy.BecknerOnofri.endpointConstant d :=
    div_pos (Nat.cast_pos.mpr hd) (Legacy.TorusEndpoint.endpointSigma_pos hd)
  have hR := GenericAttainment.rough_bound hd
    (by positivity : 0 < Legacy.BecknerOnofri.endpointConstant d / 2)
    (by linarith : Legacy.BecknerOnofri.endpointConstant d / 2 <
      Legacy.BecknerOnofri.endpointConstant d)
  let v := Legacy.BecknerOnofri.SubcriticalPrimalDual.dualPotential
    (A * (2 * Real.pi) ^ d) ρ hρ
  have hv := Legacy.BecknerOnofri.SubcriticalPrimalDual.dualPotential_admissible
    hd (A * (2 * Real.pi) ^ d) ρ hρ
  have h := Legacy.BecknerOnofri.SubcriticalPrimalDual.density_le_dual hd hR
    (by positivity : 0 < A * (2 * Real.pi) ^ d) ρ hρ
  calc
    _ ≤ (Legacy.BecknerOnofri.SubcriticalAttainment.functional
        (A * (2 * Real.pi) ^ d) v : EReal) := by exact_mod_cast h
    _ = RawAttainment.rawFunctional A (RawAttainment.realValue v) :=
      (RawAttainment.rawFunctional_realValue hd A v hv).symm
    _ ≤ coefficientDefect d A := le_iSup_of_le (RawAttainment.realValue v)
      (le_iSup_of_le (RawAttainment.realValue_sobolev v hv) le_rfl)

theorem pressure_le_coefficientDefect {d : ℕ} (hd : 0 < d) {β : ℝ}
    (hβ : 0 < β) : pressure d β ≤
      coefficientDefect d (spectralThreshold d / (2 * β * (2 * Real.pi) ^ d)) := by
  let A := spectralThreshold d / (2 * β * (2 * Real.pi) ^ d)
  have hσ := spectralThreshold_pos hd
  have hA : 0 < A := by dsimp [A]; positivity
  have he : 1 / (4 * (A * (2 * Real.pi) ^ d)) = β / (2 * spectralThreshold d) := by
    dsimp [A]
    field_simp
    <;> ring
  unfold pressure
  refine iSup_le (fun ρ => iSup_le (fun hρ => ?_))
  let t : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have ht (n : ℕ) : 0 < t n := by dsimp [t]; positivity
  let r := fun n => Legacy.BecknerOnofri.HeatDensityApproximation.heatDensity (Bridge.density ρ) (ht n)
  have hlim := heat_fourierEnergy_tendsto hd (Bridge.density ρ) hρ t ht
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim' := EReal.tendsto_coe.mpr
    ((hlim.const_mul (β / (2 * spectralThreshold d))).sub_const (entropy ρ))
  have hterms : Legacy.BecknerOnofri.fourierEnergy (Bridge.density ρ) =
      ∑' k, spectralTerm ρ k := tsum_congr (Bridge.densitySpectralTerm_eq ρ)
  rw [spectralEnergy_coe_eq_tsum hd ρ hρ, ← EReal.coe_mul, ← EReal.coe_sub, ← hterms]
  apply le_of_tendsto hlim'
  exact Eventually.of_forall (fun n => by
    have hr : MemLp (r n).value 2 (Legacy.TorusEndpoint.torusMeasure d) :=
      (Legacy.BecknerOnofri.HeatDensityApproximation.heatValue_continuous
        (Bridge.density ρ) (ht n)).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hent := Legacy.BecknerOnofri.HeatDensityApproximation.heatDensity_entropy_le
      (Bridge.density ρ) hρ (ht n)
    have hb := l2_density_le_coefficientDefect hd hA (r n) hr
    unfold Legacy.BecknerOnofri.SubcriticalPrimalDual.densityFunctional at hb
    rw [he] at hb
    apply le_trans ?_ hb
    apply EReal.coe_le_coe_iff.mpr
    exact sub_le_sub_left hent _)

/-- Exact duality for the full finite-entropy and critical Sobolev domains. -/
theorem pressure_eq_coefficientDefect {d : ℕ} (hd : 0 < d) {β : ℝ} (hβ : 0 < β) :
    pressure d β = coefficientDefect d
      (spectralThreshold d / (2 * β * (2 * Real.pi) ^ d)) :=
  le_antisymm (pressure_le_coefficientDefect hd hβ) (coefficientDefect_le_pressure hd hβ)

/-- The exact endpoint inequality is the only unproved premise of this threshold reduction. -/
theorem pressure_threshold_of_density {d : ℕ} (hd : 0 < d)
    (hE : ∀ ρ : ProbabilityDensity d, ρ.FiniteEntropy →
      spectralEnergy ρ ≤ ENNReal.ofReal (2 * entropy ρ)) :
    IsGreatest {β : ℝ | 0 ≤ β ∧ pressure d β = 0} (spectralThreshold d) := by
  have hσ := spectralThreshold_pos hd
  constructor
  · refine ⟨hσ.le, ?_⟩
    rw [pressure_eq_coefficientDefect hd hσ]
    have he : spectralThreshold d / (2 * spectralThreshold d * (2 * Real.pi) ^ d) =
        spectralCoefficient d := by
      unfold spectralCoefficient
      field_simp
    rw [he]
    exact (coefficient_threshold_of_density hd hE).1.2
  · intro β hβ
    by_contra hn
    have hpos := pressure_pos_of_spectral_lt hd (lt_of_not_ge hn)
    rw [hβ.2] at hpos
    exact lt_irrefl _ hpos

#print axioms coefficientDefect_le_pressure
#print axioms pressure_pos_of_spectral_lt
#print axioms pressure_eq_coefficientDefect
#print axioms pressure_threshold_of_density
end BecknerOnofri.HighDim
