module

public import BecknerOnofri.Definitions
public import Legacy.BecknerOnofri.SobolevCentering
public import Legacy.BecknerOnofri.SubcriticalRoughBound

@[expose] public section

/-!
Exact identifications between the trusted raw-function statement and the
actual L2 Fourier/Sobolev objects in the recovered analytic library.
No endpoint inequality or selection principle is assumed here.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace BecknerOnofri.HighDim

namespace Bridge

open Legacy.BecknerOnofri.TorusSobolev

theorem measure_eq (d : ℕ) : torusMeasure d = Legacy.TorusEndpoint.torusMeasure d := rfl

theorem frequencyLength_eq {d : ℕ} (k : Frequency d) :
    frequencyLength k = Legacy.TorusEndpoint.frequencyRadius k := rfl

theorem spectralThreshold_eq (d : ℕ) :
    spectralThreshold d = Legacy.TorusEndpoint.endpointSigma d := rfl

def density {d : ℕ} (ρ : ProbabilityDensity d) : Legacy.TorusEndpoint.ProbabilityDensity d where
  value := ρ.value
  nonneg := ρ.nonneg
  integrable := ρ.integrable
  mass := ρ.mass

theorem finiteEntropy_iff {d : ℕ} (ρ : ProbabilityDensity d) :
    (density ρ).FiniteEntropy ↔ ρ.FiniteEntropy := Iff.rfl

theorem densityEntropy_eq {d : ℕ} (ρ : ProbabilityDensity d) :
    Legacy.TorusEndpoint.densityEntropy (density ρ).value = entropy ρ := rfl

theorem densityFourier_eq {d : ℕ} (u : Torus d → ℝ) (k : Frequency d) :
    Legacy.TorusEndpoint.densityFourier u k = fourierCoeff u k := rfl

theorem densitySpectralTerm_eq {d : ℕ} (ρ : ProbabilityDensity d) (k : NonzeroFrequency d) :
    Legacy.TorusEndpoint.densitySpectralTerm (density ρ) k = spectralTerm ρ k := by
  unfold Legacy.TorusEndpoint.densitySpectralTerm spectralTerm
  rw [densityFourier_eq]
  change ‖fourierCoeff ρ.value k.val‖ ^ 2 / frequencyLength k.val ^ d = _
  ring

def potentialLp {d : ℕ} (u : Torus d → ℝ) (hu : MemLp u 2 (torusMeasure d)) : TorusL2 d :=
  (hu.ofReal : MemLp (fun x => (u x : ℂ)) 2 (torusMeasure d)).toLp (fun x => (u x : ℂ))

theorem potentialLp_ae {d : ℕ} (u : Torus d → ℝ) (hu : MemLp u 2 (torusMeasure d)) :
    potentialLp u hu =ᵐ[torusMeasure d] fun x => (u x : ℂ) :=
  MemLp.coeFn_toLp _

theorem potentialLp_real {d : ℕ} (u : Torus d → ℝ) (hu : MemLp u 2 (torusMeasure d)) :
    Legacy.BecknerOnofri.SubcriticalAttainment.RealPotential (potentialLp u hu) := by
  filter_upwards [potentialLp_ae u hu] with x hx
  simp [hx]

theorem potentialLp_fourier {d : ℕ} (u : Torus d → ℝ) (hu : MemLp u 2 (torusMeasure d))
    (k : Frequency d) : fourierIsometry d (potentialLp u hu) k = fourierCoeff u k := by
  rw [fourierIsometry_apply]
  change (∫ x, UnitAddTorus.mFourier (-k) x • potentialLp u hu x
    ∂torusMeasure d) = _
  apply integral_congr_ae
  filter_upwards [potentialLp_ae u hu] with x hx
  simp only [hx, smul_eq_mul]

theorem potentialTerm_eq {d : ℕ} (u : Torus d → ℝ) (hu : MemLp u 2 (torusMeasure d))
    (k : NonzeroFrequency d) :
    potentialTerm u k = (2 * Real.pi) ^ d *
      weightedSquare (fourierIsometry d (potentialLp u hu)) k.val := by
  rw [weightedSquare, potentialLp_fourier]
  unfold potentialTerm
  rw [mul_pow]
  rw [frequencyLength_eq]
  ring

theorem potentialLp_summable {d : ℕ} (hd : 0 < d) (u : Torus d → ℝ)
    (hu : InCriticalSobolev u) :
    Summable (weightedSquare (fourierIsometry d (potentialLp u hu.1))) := by
  let w := weightedSquare (fourierIsometry d (potentialLp u hu.1))
  have hsupport : Function.support w ⊆ {k : Frequency d | k ≠ 0} := by
    intro k hk hzero
    subst k
    simp [w, weightedSquare, Legacy.TorusEndpoint.frequencyRadius, hd.ne'] at hk
  have hc : (2 * Real.pi) ^ d ≠ 0 := (pow_pos (by positivity : 0 < 2 * Real.pi) d).ne'
  have hs : Summable (fun k : NonzeroFrequency d => w k.val) := by
    have hp := hu.2.mul_left ((2 * Real.pi) ^ d)⁻¹
    apply hp.congr
    intro k
    rw [potentialTerm_eq u hu.1]
    change ((2 * Real.pi) ^ d)⁻¹ * ((2 * Real.pi) ^ d * w k.val) = w k.val
    rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  exact (hasSum_subtype_iff_of_support_subset hsupport).mp hs.hasSum |>.summable

theorem potentialLp_energy {d : ℕ} (hd : 0 < d) (u : Torus d → ℝ)
    (hu : InCriticalSobolev u) :
    potentialEnergy u = (2 * Real.pi) ^ d * criticalEnergy (potentialLp u hu.1) := by
  let w := weightedSquare (fourierIsometry d (potentialLp u hu.1))
  have hsupport : Function.support w ⊆ {k : Frequency d | k ≠ 0} := by
    intro k hk hzero
    subst k
    simp [w, weightedSquare, Legacy.TorusEndpoint.frequencyRadius, hd.ne'] at hk
  have hs := potentialLp_summable hd u hu
  have hsum := (hasSum_subtype_iff_of_support_subset hsupport).mpr hs.hasSum
  unfold potentialEnergy
  simp_rw [potentialTerm_eq u hu.1]
  rw [tsum_mul_left]
  congr 1
  exact hsum.tsum_eq

theorem centeredLp_ae {d : ℕ} (u : Torus d → ℝ) (hu : MemLp u 2 (torusMeasure d)) :
    (fun x => (Legacy.BecknerOnofri.SobolevCentering.center (potentialLp u hu) x).re)
      =ᵐ[torusMeasure d] centered u := by
  have hr : (fun x => (potentialLp u hu x).re) =ᵐ[torusMeasure d] u := by
    filter_upwards [potentialLp_ae u hu] with x hx
    simp [hx]
  have hi := integral_congr_ae hr
  filter_upwards [Legacy.BecknerOnofri.SobolevCentering.center_real_ae (potentialLp u hu), hr]
    with x hx hrx
  change (Legacy.BecknerOnofri.SobolevCentering.center (potentialLp u hu) x).re =
    (potentialLp u hu x).re - (∫ y, (potentialLp u hu y).re ∂torusMeasure d) at hx
  simpa only [centered, hrx, hi] using hx

end Bridge

/-- Every critical Sobolev potential has all positive exponential moments.
This is obtained from the proved Green estimate, with no rough-bound hypothesis. -/
theorem critical_exp_integrable {d : ℕ} (hd : 0 < d)
    (u : Torus d → ℝ) (hu : InCriticalSobolev u) {p : ℝ} (hp : 0 < p) :
    Integrable (fun x => Real.exp (p * centered u x)) (torusMeasure d) := by
  let C := Legacy.BecknerOnofri.endpointConstant d
  have hC : 0 < C := div_pos (Nat.cast_pos.mpr hd)
    (Legacy.TorusEndpoint.endpointSigma_pos hd)
  have hb : 0 < C / 2 := by positivity
  have hbd : C / 2 < C := by linarith
  have hadm := Legacy.BecknerOnofri.SobolevCentering.center_admissible hd
    (Bridge.potentialLp_real u hu.1) (Bridge.potentialLp_summable hd u hu)
  have hi := (Legacy.BecknerOnofri.SubcriticalAttainment.roughExponentialBound
    hd hb hbd _ hadm p hp).1
  apply hi.congr
  filter_upwards [Bridge.centeredLp_ae u hu.1] with x hx
  rw [hx]

#print axioms critical_exp_integrable

end BecknerOnofri.HighDim
