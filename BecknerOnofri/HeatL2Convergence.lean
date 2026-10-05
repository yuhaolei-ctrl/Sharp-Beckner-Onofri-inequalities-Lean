module

public import BecknerOnofri.HeatEnergyLimit
public import BecknerOnofri.ContinuousFirstShell
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

@[expose] public section

/-! Strong L2 convergence of the actual heat convolution for L2 densities.
The proof uses Parseval and domination by the original Fourier square sum. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped Topology
namespace BecknerOnofri.HighDim.HeatApproximation
open Legacy.BecknerOnofri.TorusSobolev
open Legacy.BecknerOnofri.HeatDensityApproximation
open Legacy.TorusEndpoint.TorusHeatBounds Legacy.TorusEndpoint.GreenHeatRegularization

def heatLp {d : ℕ} (ρ : Legacy.TorusEndpoint.ProbabilityDensity d)
    {t : ℝ} (ht : 0 < t) : TorusL2 d :=
  ContinuousFirstShell.toL2 d ⟨heatValue ρ t, heatValue_continuous ρ ht⟩

lemma heatLp_fourier {d : ℕ} (ρ : Legacy.TorusEndpoint.ProbabilityDensity d)
    {t : ℝ} (ht : 0 < t) (k : Frequency d) :
    fourierIsometry d (heatLp ρ ht) k =
      (heatWeight t k : ℂ) * fourierCoeff ρ.value k := by
  change ContinuousFirstShell.coefficient k ⟨heatValue ρ t, heatValue_continuous ρ ht⟩ = _
  rw [ContinuousFirstShell.coefficient_eq_fourierCoeff]
  exact heatValue_fourier ρ ht k

theorem heatLp_tendsto {d : ℕ} (ρ : Legacy.TorusEndpoint.ProbabilityDensity d)
    (hρ : MemLp ρ.value 2 (torusMeasure d))
    (t : ℕ → ℝ) (ht : ∀ n, 0 < t n) (ht0 : Tendsto t atTop (𝓝 0)) :
    Tendsto (fun n => heatLp ρ (ht n)) atTop (𝓝 (Bridge.potentialLp ρ.value hρ)) := by
  let u := Bridge.potentialLp ρ.value hρ
  have hs : Summable (fun k : Frequency d => ‖fourierCoeff ρ.value k‖^2) := by
    have h := (lp.memℓp (fourierIsometry d u)).summable (by norm_num : (0:ℝ) < (2:ENNReal).toReal)
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, u, Bridge.potentialLp_fourier] using h
  have hpoint (k : Frequency d) : Tendsto
      (fun n => ‖((heatWeight (t n) k-1:ℝ):ℂ)*fourierCoeff ρ.value k‖^2)
      atTop (𝓝 0) := by
    have h := ((Complex.continuous_ofReal.tendsto 0).comp
      (by simpa using (heatWeight_tendsto_one ht0 k).sub_const 1)).mul_const
        (fourierCoeff ρ.value k)
    simpa using h.norm.pow 2
  have hbound : ∀ᶠ n in atTop, ∀ k : Frequency d,
      ‖‖((heatWeight (t n) k-1:ℝ):ℂ)*fourierCoeff ρ.value k‖^2‖ ≤
        ‖fourierCoeff ρ.value k‖^2 := by
    refine Eventually.of_forall (fun n k => ?_)
    have hp := heatWeight_pos (t n) k
    have hle := Legacy.TorusEndpoint.GreenHeatRegularization.heatWeight_le_one (ht n).le k
    simp only [Real.norm_of_nonneg (sq_nonneg _), norm_mul, Complex.norm_real,
      Real.norm_eq_abs, mul_pow, sq_abs]
    have hb : (heatWeight (t n) k-1)^2 ≤ 1 := by nlinarith
    nlinarith [sq_nonneg ‖fourierCoeff ρ.value k‖]
  have hsum := tendsto_tsum_of_dominated_convergence hs hpoint hbound
  have he (n : ℕ) : ‖heatLp ρ (ht n)-u‖^2 =
      ∑' k : Frequency d, ‖((heatWeight (t n) k-1:ℝ):ℂ)*fourierCoeff ρ.value k‖^2 := by
    rw [← (fourierIsometry d).norm_map]
    have hn := lp.norm_rpow_eq_tsum (show (0:ℝ)<(2:ENNReal).toReal by norm_num)
      (fourierIsometry d (heatLp ρ (ht n)-u))
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hn
    rw [hn]
    apply tsum_congr
    intro k
    simp only [map_sub, lp.coeFn_sub, Pi.sub_apply, heatLp_fourier, u, Bridge.potentialLp_fourier]
    congr 2
    push_cast
    ring
  have hsq : Tendsto (fun n => ‖heatLp ρ (ht n)-u‖^2) atTop (𝓝 0) := by
    simpa only [he, tsum_zero] using hsum
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simpa only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero, Function.comp_def] using h

#print axioms heatLp_tendsto
end BecknerOnofri.HighDim.HeatApproximation
