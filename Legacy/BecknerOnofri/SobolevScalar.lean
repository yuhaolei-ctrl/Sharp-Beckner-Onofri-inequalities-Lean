module

public import Legacy.BecknerOnofri.SubcriticalAttainmentDefs

@[expose] public section

/-! Real scalar multiplication on the actual critical Sobolev class. -/
namespace Legacy.BecknerOnofri.TorusSobolev
open MeasureTheory Legacy.TorusEndpoint

theorem weightedSquare_smul_real {d : ℕ} (u : TorusL2 d) (t : ℝ) (k : Frequency d) :
    weightedSquare (fourierIsometry d ((t : ℂ) • u)) k =
      t^2 * weightedSquare (fourierIsometry d u) k := by
  simp only [weightedSquare, map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
    norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  ring

theorem criticalSobolev_smul_real {d : ℕ} {u : TorusL2 d} (hu : CriticalSobolev u) (t : ℝ) :
    CriticalSobolev ((t : ℂ) • u) := by
  constructor
  · change fourierIsometry d ((t : ℂ) • u) 0 = 0
    rw [map_smul, lp.coeFn_smul]
    simp only [Pi.smul_apply, hu.1, smul_zero]
  · have he : weightedSquare (fourierIsometry d ((t : ℂ) • u)) =
        fun k => t^2 * weightedSquare (fourierIsometry d u) k :=
      funext (weightedSquare_smul_real u t)
    rw [he]
    exact hu.2.mul_left _

theorem criticalEnergy_smul_real {d : ℕ} (u : TorusL2 d) (t : ℝ) :
    criticalEnergy ((t : ℂ) • u) = t^2 * criticalEnergy u := by
  simp only [criticalEnergy, coefficientEnergy, weightedSquare_smul_real, tsum_mul_left]

theorem realPotential_smul_real {d : ℕ} {u : TorusL2 d}
    (hu : SubcriticalAttainment.RealPotential u) (t : ℝ) :
    SubcriticalAttainment.RealPotential ((t : ℂ) • u) := by
  filter_upwards [Lp.coeFn_smul (t : ℂ) u, hu] with x hx hx0
  rw [hx]
  change ((t : ℂ) * u x).im = 0
  simp only [Complex.mul_im, Complex.ofReal_im, hx0, mul_zero, zero_mul, add_zero]

theorem admissible_smul_real {d : ℕ} {u : TorusL2 d}
    (hu : SubcriticalAttainment.Admissible u) (t : ℝ) :
    SubcriticalAttainment.Admissible ((t : ℂ) • u) :=
  ⟨realPotential_smul_real hu.1 t, criticalSobolev_smul_real hu.2 t⟩

#print axioms admissible_smul_real
#print axioms criticalEnergy_smul_real
end Legacy.BecknerOnofri.TorusSobolev
