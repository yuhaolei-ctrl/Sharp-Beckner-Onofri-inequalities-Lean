module

public import BecknerOnofri.BesselIntegral
public import BecknerOnofri.CircleMeanBounds
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Measure.OpenPos

@[expose] public section

/-!
# One-dimensional facts on the circle used by the channel argument (work package G10)

* `integral_mul_cos_nonneg`: a function nondecreasing in `cos` has nonnegative covariance with
  `cos`; proved by the antipodal pairing `z ↦ z + 1/2` (`cos(z + 1/2) = -cos z`), which is the
  pairing of positive and negative cosine values of the manuscript (the manuscript writes it with
  the arcsine density `z/(π √(1-z²))`).
* `integral_density_cos_lt_one`: a continuous strictly positive density has first cosine moment `< 1`
  (strict positivity of the density, as in "Strict positivity gives `t_i < 1`").
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Function
namespace BecknerOnofri.V2.Channel
open BecknerOnofri.HighDim

theorem cosine_half_shift (z : UnitAddCircle) :
    (fourier 1 (z + ((1 / 2 : ℝ) : UnitAddCircle))).re = -(fourier 1 z).re :=
  CircleScalar.circle_cosine_half_shift z

theorem cosine_continuous : Continuous (fun z : UnitAddCircle => (fourier 1 z).re) :=
  Complex.continuous_re.comp (fourier 1).continuous

theorem cosine_norm_le (z : UnitAddCircle) : ‖(fourier 1 z).re‖ ≤ 1 := by
  rw [Real.norm_eq_abs]; exact CircleScalar.circle_cosine_bound z

theorem integrable_mul_cosine {a : UnitAddCircle → ℝ} (ha : Integrable a AddCircle.haarAddCircle) :
    Integrable (fun z => a z * (fourier 1 z).re) AddCircle.haarAddCircle :=
  ha.mul_bdd cosine_continuous.aestronglyMeasurable (Filter.Eventually.of_forall cosine_norm_le)

/-- Covariance inequality: if `a` is nondecreasing in `cos` then `∫ a cos ≥ 0`
(note `∫ cos = 0`, so this is `Cov(a, cos) ≥ 0`, Chebyshev's association inequality for the
arcsine law). -/
theorem integral_mul_cos_nonneg {a : UnitAddCircle → ℝ}
    (ha : Integrable a AddCircle.haarAddCircle)
    (hmono : ∀ y z : UnitAddCircle, (fourier 1 y).re ≤ (fourier 1 z).re → a y ≤ a z) :
    0 ≤ ∫ z, a z * (fourier 1 z).re ∂AddCircle.haarAddCircle := by
  have hi := integrable_mul_cosine ha
  set h : UnitAddCircle := ((1 / 2 : ℝ) : UnitAddCircle) with hh
  have hshift : Integrable (fun z => a (z + h) * (fourier 1 z).re) AddCircle.haarAddCircle :=
    integrable_mul_cosine (ha.comp_add_right h) |>.congr (Filter.Eventually.of_forall fun z => rfl)
  have htrans := integral_add_right_eq_self (μ := AddCircle.haarAddCircle)
    (fun z => a z * (fourier 1 z).re) h
  have hfun : (fun z => a (z + h) * (fourier 1 (z + h)).re) =
      fun z => -(a (z + h) * (fourier 1 z).re) := by
    funext z
    rw [hh, cosine_half_shift]
    ring
  rw [hfun, integral_neg] at htrans
  have hpoint : ∀ z : UnitAddCircle,
      0 ≤ a z * (fourier 1 z).re - a (z + h) * (fourier 1 z).re := by
    intro z
    rw [← sub_mul]
    by_cases hz : 0 ≤ (fourier 1 z).re
    · apply mul_nonneg _ hz
      apply sub_nonneg.mpr
      apply hmono
      rw [hh, cosine_half_shift]
      linarith
    · apply mul_nonneg_of_nonpos_of_nonpos _ (le_of_not_ge hz)
      apply sub_nonpos.mpr
      apply hmono
      rw [hh, cosine_half_shift]
      linarith [not_le.mp hz]
  have hnon : 0 ≤ ∫ z, (a z * (fourier 1 z).re - a (z + h) * (fourier 1 z).re)
        ∂AddCircle.haarAddCircle := integral_nonneg hpoint
  rw [integral_sub hi hshift] at hnon
  linarith

/-- `1 - cos` has mean one. -/
theorem integral_one_sub_cos :
    (∫ z : UnitAddCircle, (1 - (fourier 1 z).re) ∂AddCircle.haarAddCircle) = 1 := by
  have hint : Integrable (fun z : UnitAddCircle => (fourier 1 z).re) AddCircle.haarAddCircle :=
    cosine_continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hc0 : (∫ z : UnitAddCircle, (fourier 1 z).re ∂AddCircle.haarAddCircle) = 0 := by
    have hi := (map_continuous (fourier (1 : ℤ) : C(UnitAddCircle, ℂ))).integrable_of_hasCompactSupport
      (μ := AddCircle.haarAddCircle) (HasCompactSupport.of_compactSpace _)
    have h := integral_re hi
    change (∫ z : UnitAddCircle, (fourier 1 z).re ∂AddCircle.haarAddCircle) =
      (∫ z : UnitAddCircle, fourier 1 z ∂AddCircle.haarAddCircle).re at h
    rw [circle_fourier_integral] at h
    norm_num at h
    simpa using h
  rw [integral_sub (integrable_const 1) hint, hc0]
  simp

/-- A continuous strictly positive probability density on the circle has first cosine moment
strictly less than one. -/
theorem integral_density_cos_lt_one {a : UnitAddCircle → ℝ} (ha : Continuous a)
    (hpos : ∀ z, 0 < a z) (hmass : (∫ z, a z ∂AddCircle.haarAddCircle) = 1) :
    (∫ z, a z * (fourier 1 z).re ∂AddCircle.haarAddCircle) < 1 := by
  let v : UnitAddCircle → ℝ := fun x => a x * (1 - (fourier 1 x).re)
  have hcv : Continuous v := ha.mul (continuous_const.sub cosine_continuous)
  have hi {f : UnitAddCircle → ℝ} (hf : Continuous f) : Integrable f AddCircle.haarAddCircle :=
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hv : ∀ x, 0 ≤ v x := fun x => mul_nonneg (hpos x).le
    (sub_nonneg.mpr (abs_le.mp (CircleScalar.circle_cosine_bound x)).2)
  have hposv : 0 < ∫ x, v x ∂AddCircle.haarAddCircle := by
    by_contra hh
    have hz := le_antisymm (le_of_not_gt hh) (integral_nonneg hv)
    have hae := (integral_eq_zero_iff_of_nonneg_ae (Filter.Eventually.of_forall hv) (hi hcv)).mp hz
    have he := congrFun (MeasureTheory.Measure.eq_of_ae_eq hae hcv continuous_const)
      (((1 / 2 : ℝ) : UnitAddCircle))
    have hhalf : (fourier 1 (((1 / 2 : ℝ) : UnitAddCircle))).re = -1 := by
      simpa using CircleScalar.circle_cosine_half_shift 0
    change a (((1 / 2 : ℝ) : UnitAddCircle)) *
      (1 - (fourier 1 (((1 / 2 : ℝ) : UnitAddCircle))).re) = 0 at he
    rw [hhalf] at he
    have hp := hpos (((1 / 2 : ℝ) : UnitAddCircle))
    linarith
  have he : (∫ x, v x ∂AddCircle.haarAddCircle) = 1 -
      ∫ x, a x * (fourier 1 x).re ∂AddCircle.haarAddCircle := by
    change (∫ x, a x * (1 - (fourier 1 x).re) ∂AddCircle.haarAddCircle) = _
    simp_rw [mul_sub, mul_one]
    rw [integral_sub (g := fun x => a x * (fourier 1 x).re) (hi ha)
      (hi (ha.mul cosine_continuous)), hmass]
  rw [he] at hposv
  linarith

end BecknerOnofri.V2.Channel
