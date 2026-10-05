module

public import BecknerOnofri.GraphRegularity
public import BecknerOnofri.FiniteEntropyEnergy

@[expose] public section

/-! Every positive-time heat regularization of an actual probability density
is smooth. All Fourier moments are controlled by a slower Gaussian. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped BigOperators
namespace BecknerOnofri.HighDim.HeatSmooth
open Legacy.TorusEndpoint.TorusHeatBounds Legacy.TorusEndpoint.GreenMultiplierSummability
open Legacy.BecknerOnofri.HeatDensityApproximation Legacy.BecknerOnofri.RadialWiener

lemma polynomial_gaussian_bound (m : ℕ) {a r : ℝ} (ha : 0 < a) (hr : 0 ≤ r) :
    (1+r)^m * Real.exp (-2*a*r^2) ≤
      ((2+1/a)^m * Real.exp 1 * (m.factorial:ℝ)) * Real.exp (-a*r^2) := by
  have har : 0 ≤ a*r^2 := mul_nonneg ha.le (sq_nonneg _)
  have hbase : 1+r ≤ (2+1/a)*(1+a*r^2) := by
    have he : (2+1/a)*(1+a*r^2) = 2+1/a+(2*a+1)*r^2 := by field_simp
    rw [he]
    have hi : 0 ≤ 1/a := by positivity
    nlinarith [sq_nonneg (r-1), har, hi]
  have hfac : (0:ℝ) < m.factorial := Nat.cast_pos.mpr (Nat.factorial_pos m)
  have hp := (div_le_iff₀ hfac).mp
    (Real.pow_div_factorial_le_exp (1+a*r^2) (by positivity) m)
  have hpoly : (1+r)^m ≤ (2+1/a)^m * (Real.exp (1+a*r^2)*(m.factorial:ℝ)) := by
    calc
      _ ≤ ((2+1/a)*(1+a*r^2))^m := pow_le_pow_left₀ (by positivity) hbase m
      _ = (2+1/a)^m * (1+a*r^2)^m := mul_pow _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hp (by positivity)
  calc
    _ ≤ ((2+1/a)^m * (Real.exp (1+a*r^2)*(m.factorial:ℝ))) * Real.exp (-2*a*r^2) :=
      mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le
    _ = ((2+1/a)^m * Real.exp 1 * (m.factorial:ℝ)) * Real.exp (-a*r^2) := by
      have he : Real.exp (1+a*r^2)*Real.exp (-2*a*r^2) = Real.exp 1*Real.exp (-a*r^2) := by
        rw [← Real.exp_add,← Real.exp_add]
        congr 1
        ring
      linear_combination ((2+1/a)^m*(m.factorial:ℝ))*he

lemma heat_radial_summable {d : ℕ} {t : ℝ} (ht : 0 < t) (m : ℕ) :
    Summable (fun k : Frequency d => radialWeight m k * heatWeight t k) := by
  let a := Real.pi*t/2
  have ha : 0 < a := by dsimp [a]; positivity
  let C := (2+1/a)^m * Real.exp 1 * (m.factorial:ℝ)
  apply ((heatWeight_summable (d := d) (half_pos ht)).mul_left C).of_nonneg_of_le
  · intro k
    exact mul_nonneg ((radialWeight_isWeight m).nonneg k) (heatWeight_pos t k).le
  · intro k
    have h := polynomial_gaussian_bound m ha (Real.sqrt_nonneg (radiusSq k))
    have hs : (Real.sqrt (radiusSq k))^2 = radiusSq k := Real.sq_sqrt (radiusSq_nonneg k)
    rw [hs] at h
    convert! h using 1 <;> simp only [radialWeight, heatWeight, a, C]
    · congr 2 <;> ring
    · congr 2 <;> ring

lemma density_fourier_norm_le_one {d : ℕ} (ρ : Legacy.TorusEndpoint.ProbabilityDensity d)
    (k : Frequency d) : ‖Legacy.TorusEndpoint.densityFourier ρ.value k‖ ≤ 1 := by
  rw [← ρ.mass]
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono_ae
    (Legacy.TorusEndpoint.densityFourier_integrable ρ k).norm ρ.integrable
  filter_upwards [ρ.nonneg] with x hx
  simp only [norm_mul, Legacy.TorusEndpoint.mFourier_norm_apply, one_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx, le_refl]

lemma heatValue_radial {d : ℕ} (ρ : Legacy.TorusEndpoint.ProbabilityDensity d)
    {t : ℝ} (ht : 0 < t) (m : ℕ) :
    RadialSummable (Legacy.TorusEndpoint.densityFourier (heatValue ρ t)) m := by
  apply (heat_radial_summable (d := d) ht m).of_nonneg_of_le
  · intro k
    exact mul_nonneg ((radialWeight_isWeight m).nonneg k) (norm_nonneg _)
  · intro k
    rw [heatValue_fourier ρ ht, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (heatWeight_pos t k)]
    exact mul_le_mul_of_nonneg_left
      (mul_le_of_le_one_right (heatWeight_pos t k).le (density_fourier_norm_le_one ρ k))
      ((radialWeight_isWeight m).nonneg k)

theorem heatValue_smooth {d : ℕ} (ρ : Legacy.TorusEndpoint.ProbabilityDensity d)
    {t : ℝ} (ht : 0 < t) : SmoothOnTorus (heatValue ρ t) := by
  let u : ContinuousGibbs.Space d := ⟨heatValue ρ t,heatValue_continuous ρ ht⟩
  apply GraphRegularity.smooth_of_radial u
  intro m
  apply (heatValue_radial ρ ht m).congr
  intro k
  dsimp only
  rw [ContinuousFirstShell.coefficient_eq_fourierCoeff]
  rfl

#print axioms heatValue_smooth
end BecknerOnofri.HighDim.HeatSmooth
