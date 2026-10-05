module

public import BecknerOnofri.LegacyBridge
public import BecknerOnofri.GenericAttainment
public import BecknerOnofri.BranchDefinitions
public import BecknerOnofri.PartitionRegularity

@[expose] public section

/-! Subcritical variational attainment on the actual raw-function Sobolev domain. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace BecknerOnofri.HighDim.RawAttainment

open Legacy.BecknerOnofri.TorusSobolev
open Legacy.BecknerOnofri.SubcriticalAttainment
open Legacy.BecknerOnofri.SobolevCentering

/-- The real representative of a genuine complex L² equivalence class. -/
def realValue {d : ℕ} (u : TorusL2 d) : Torus d → ℝ := fun x => (u x).re

theorem realValue_memLp {d : ℕ} (u : TorusL2 d) :
    MemLp (realValue u) 2 (torusMeasure d) := by
  change MemLp (fun x => (u x).re) 2 (Legacy.TorusEndpoint.torusMeasure d)
  simpa only [Function.comp_def, Complex.reCLM_apply] using
    Complex.reCLM.comp_memLp u

theorem potentialLp_realValue {d : ℕ} (u : TorusL2 d) (hu : RealPotential u) :
    Bridge.potentialLp (realValue u) (realValue_memLp u) = u := by
  apply Lp.ext
  filter_upwards [Bridge.potentialLp_ae (realValue u) (realValue_memLp u), hu] with x hx hi
  rw [hx]
  apply Complex.ext
  · rfl
  · simp only [Complex.ofReal_im, hi]

theorem realValue_sobolev {d : ℕ} (u : TorusL2 d) (hu : Admissible u) :
    InCriticalSobolev (realValue u) := by
  refine ⟨realValue_memLp u, ?_⟩
  have hs : Summable (fun k : NonzeroFrequency d => weightedSquare (fourierIsometry d u) k.val) :=
    hu.2.2.subtype {k | k ≠ 0}
  apply (hs.mul_left ((2 * Real.pi) ^ d)).congr
  intro k
  rw [Bridge.potentialTerm_eq (realValue u) (realValue_memLp u), potentialLp_realValue u hu.1]

theorem realValue_meanZero {d : ℕ} (u : TorusL2 d) (hu : Admissible u) :
    MeanZero (realValue u) := by
  have hz := hu.2.1
  rw [Legacy.BecknerOnofri.SobolevCentering.fourier_zero] at hz
  change (∫ x, (u x).re ∂torusMeasure d) = 0
  calc
    _ = (∫ x, u x ∂Legacy.TorusEndpoint.torusMeasure d).re :=
      integral_re ((Lp.memLp u).integrable (by norm_num))
    _ = 0 := congrArg Complex.re hz

theorem realValue_energy {d : ℕ} (hd : 0 < d) (u : TorusL2 d) (hu : Admissible u) :
    potentialEnergy (realValue u) = (2 * Real.pi) ^ d * criticalEnergy u := by
  rw [Bridge.potentialLp_energy hd (realValue u) (realValue_sobolev u hu)]
  rw [potentialLp_realValue u hu.1]

theorem centered_realValue {d : ℕ} (u : TorusL2 d) (hu : Admissible u) :
    centered (realValue u) = realValue u := by
  have hz : (∫ x, realValue u x ∂torusMeasure d) = 0 := realValue_meanZero u hu
  funext x
  simp only [centered, hz, sub_zero]

theorem center_potentialLp_realValue {d : ℕ} (u : TorusL2 d) (hu : Admissible u) :
    center (Bridge.potentialLp (realValue u) (realValue_memLp u)) = u := by
  rw [potentialLp_realValue u hu.1]
  simp [center, hu.2.1, constant]

/-- The actual centered variational functional with the physical energy convention. -/
def rawFunctional {d : ℕ} (A : ℝ) (u : Torus d → ℝ) : EReal :=
  logPartition u - ((A * potentialEnergy u : ℝ) : EReal)

theorem rawFunctional_eq_legacy {d : ℕ} (hd : 0 < d) (A : ℝ)
    (u : Torus d → ℝ) (hu : InCriticalSobolev u) :
    rawFunctional A u =
      (functional (A * (2 * Real.pi) ^ d) (center (Bridge.potentialLp u hu.1)) : EReal) := by
  have hZ : partition (center (Bridge.potentialLp u hu.1)) =
      ∫ x, Real.exp (centered u x) ∂torusMeasure d := by
    apply integral_congr_ae
    filter_upwards [Bridge.centeredLp_ae u hu.1] with x hx
    rw [hx]
  unfold rawFunctional functional
  rw [logPartition_eq_log_integral hd u hu, hZ, center_energy hd,
    Bridge.potentialLp_energy hd u hu, mul_assoc, EReal.coe_sub]

theorem rawFunctional_realValue {d : ℕ} (hd : 0 < d) (A : ℝ)
    (u : TorusL2 d) (hu : Admissible u) :
    rawFunctional A (realValue u) = (functional (A * (2 * Real.pi) ^ d) u : EReal) := by
  rw [rawFunctional_eq_legacy hd A (realValue u) (realValue_sobolev u hu)]
  rw [center_potentialLp_realValue u hu]

theorem physical_threshold {d : ℕ} (hd : 0 < d) {A : ℝ}
    (hA : spectralThreshold d / (4 * (d : ℝ) * (2 * Real.pi) ^ d) < A) :
    1 / (4 * Legacy.BecknerOnofri.endpointConstant d) < A * (2 * Real.pi) ^ d := by
  have hd' : (d : ℝ) ≠ 0 := (Nat.cast_pos.mpr hd).ne'
  have hσ : spectralThreshold d ≠ 0 := (Legacy.TorusEndpoint.endpointSigma_pos hd).ne'
  have hc : 0 < (2 * Real.pi) ^ d := pow_pos (by positivity) d
  have he : 1 / (4 * Legacy.BecknerOnofri.endpointConstant d) =
      spectralThreshold d / (4 * (d : ℝ)) := by
    unfold Legacy.BecknerOnofri.endpointConstant
    rw [← Bridge.spectralThreshold_eq]
    field_simp
  rw [he]
  apply (div_lt_iff₀ hc).mp
  simpa only [div_div] using hA

/-- Subcritical attainment, in the paper's unnormalized physical-energy convention.
The optimizing real function is critical Sobolev and has mean zero; comparison
holds against every raw critical Sobolev function. -/
theorem exists_subcritical_optimizer {d : ℕ} (hd : 0 < d) {A : ℝ}
    (hA : spectralThreshold d / (4 * (d : ℝ) * (2 * Real.pi) ^ d) < A) :
    ∃ u : Torus d → ℝ, InCriticalSobolev u ∧ MeanZero u ∧
      0 ≤ rawFunctional A u ∧
      ∀ v : Torus d → ℝ, InCriticalSobolev v → rawFunctional A v ≤ rawFunctional A u := by
  obtain ⟨u, hu, hzero, hmax⟩ :=
    GenericAttainment.exists_subcritical_optimizer hd (physical_threshold hd hA)
  refine ⟨realValue u, realValue_sobolev u hu, realValue_meanZero u hu, ?_, ?_⟩
  · rw [rawFunctional_realValue hd A u hu]
    exact_mod_cast hzero
  · intro v hv
    rw [rawFunctional_eq_legacy hd A v hv, rawFunctional_realValue hd A u hu]
    have hadm := center_admissible hd (Bridge.potentialLp_real v hv.1)
      (Bridge.potentialLp_summable hd v hv)
    exact_mod_cast hmax _ hadm

theorem dualFunctional_eq_raw {d : ℕ} (β : ℝ) (u : Torus d → ℝ) :
    dualFunctional β u =
      rawFunctional (spectralThreshold d / (2 * β * (2 * Real.pi) ^ d)) u := by
  unfold dualFunctional rawFunctional normalizedPotentialEnergy
  congr 2
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The β-normalized actual dual problem is attained throughout the full
subcritical interval 0 < β < 2d. -/
theorem exists_dual_optimizer {d : ℕ} (hd : 0 < d) {β : ℝ}
    (hβ : 0 < β) (hβd : β < 2 * (d : ℝ)) :
    ∃ u : Torus d → ℝ, InCriticalSobolev u ∧ MeanZero u ∧
      0 ≤ dualFunctional β u ∧
      ∀ v : Torus d → ℝ, InCriticalSobolev v → dualFunctional β v ≤ dualFunctional β u := by
  have hc : 0 < (2 * Real.pi) ^ d := pow_pos (by positivity) d
  have hσ : 0 < spectralThreshold d := Legacy.TorusEndpoint.endpointSigma_pos hd
  have hden : 0 < 2 * β * (2 * Real.pi) ^ d := mul_pos (by positivity) hc
  have hdenlt : 2 * β * (2 * Real.pi) ^ d < 4 * (d : ℝ) * (2 * Real.pi) ^ d :=
    mul_lt_mul_of_pos_right (by linarith) hc
  have hA := div_lt_div_of_pos_left hσ hden hdenlt
  simpa only [← dualFunctional_eq_raw] using exists_subcritical_optimizer hd hA

#print axioms exists_subcritical_optimizer
#print axioms exists_dual_optimizer

end BecknerOnofri.HighDim.RawAttainment
