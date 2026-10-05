module

public import BecknerOnofri.RadialMeasureJacobian
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.MeasureTheory.Function.JacobianOneDim

@[expose] public section

/-! Spherical integration with the exact twelve-dimensional squared-radius constant. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Function
open scoped ENNReal BigOperators
namespace BecknerOnofri.HighDim.RadialMeasure

theorem lintegral_fun_norm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f ‖x‖ ∂μ) = (Module.finrank ℝ E : ℝ≥0∞) * μ (Metric.ball 0 1) *
      ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r^(Module.finrank ℝ E-1)) * f r := by
  calc
    (∫⁻ x, f ‖x‖ ∂μ) =
        ∫⁻ x : ({(0 : E)}ᶜ : Set E), f ‖x.1‖ ∂μ.comap Subtype.val := by
      rw [lintegral_subtype_comap (measurableSet_singleton (0 : E)).compl (fun x : E => f ‖x‖),restrict_compl_singleton]
    _ = ∫⁻ x, f x.2 ∂μ.toSphere.prod (.volumeIoiPow (Module.finrank ℝ E-1)) := by
      simpa using μ.measurePreserving_homeomorphUnitSphereProd.lintegral_comp_emb
        (Homeomorph.measurableEmbedding _) (f ∘ Subtype.val ∘ Prod.snd)
    _ = μ.toSphere univ * ∫⁻ r : Ioi (0 : ℝ), f r ∂.volumeIoiPow (Module.finrank ℝ E-1) := by
      have hme : Measurable (fun x : Metric.sphere (0 : E) 1 × Ioi (0 : ℝ) => f x.2) :=
        hf.comp (measurable_subtype_coe.comp measurable_snd)
      rw [lintegral_prod _ hme.aemeasurable]
      simp [mul_comm]
    _ = _ := by
      rw [Measure.toSphere_apply_univ,Measure.volumeIoiPow,
        lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (show Measurable (fun r : Ioi (0 : ℝ) => f r) from hf.comp measurable_subtype_coe)]
      congr 1
      exact lintegral_subtype_comap measurableSet_Ioi
        (fun r => ENNReal.ofReal (r^(Module.finrank ℝ E-1))*f r)

theorem square_image_Ioi : (fun r : ℝ => r^2) '' Ioi 0 = Ioi 0 := by
  ext s
  constructor
  · rintro ⟨r,hr,rfl⟩
    exact sq_pos_of_pos (show 0 < r from hr)
  · intro hs
    exact ⟨Real.sqrt s,Real.sqrt_pos.mpr hs,Real.sq_sqrt hs.le⟩

theorem square_injOn_Ioi : InjOn (fun r : ℝ => r^2) (Ioi 0) := by
  intro x hx y hy h
  dsimp at h
  nlinarith [show 0 < x from hx,show 0 < y from hy]

theorem squared_radius_change (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s^5)*F s) =
      2 * ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r^11)*F (r^2) := by
  have h := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi
    (fun r _ => ((hasDerivAt_id r).pow 2).hasDerivWithinAt) square_injOn_Ioi
    (fun s => ENNReal.ofReal (s^5)*F s)
  change (∫⁻ s in (fun r : ℝ => r^2) '' Ioi 0, ENNReal.ofReal (s^5)*F s) =
    ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal |(2:ℝ)*r^(2-1)*1| *(ENNReal.ofReal ((r^2)^5)*F (r^2)) at h
  rw [square_image_Ioi] at h
  rw [h,← lintegral_const_mul _ (by fun_prop :
    Measurable (fun r : ℝ => ENNReal.ofReal (r^11)*F (r^2)))]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro r hr
  change 0 < r at hr
  dsimp only
  have hp : |(2 : ℝ)*r^(2-1)*1|=2*r := by
    simp [abs_of_pos hr]
  rw [hp,← mul_assoc,← ENNReal.ofReal_mul (by positivity)]
  rw [show (2*r)*(r^2)^5=2*r^11 by ring,ENNReal.ofReal_mul (by norm_num)]
  norm_num
  ring

theorem twelve_ball_constant :
    (12 : ℝ≥0∞) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 12)) 1) =
      ENNReal.ofReal (Real.pi^6 / 120) * 2 := by
  rw [InnerProductSpace.volume_ball_of_dim_even (k := 6) (by simp)]
  norm_num
  have he : (12 : ℝ)*(Real.pi^6/720)=(Real.pi^6/120)*2 := by ring
  have ht := congrArg ENNReal.ofReal he
  simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 12),
    ENNReal.ofReal_mul (by positivity : 0 ≤ Real.pi^6/120),ENNReal.ofReal_ofNat] using ht

theorem euclidean_squared_radius (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ y : EuclideanSpace ℝ (Fin 12), F (‖y‖^2)) =
      ENNReal.ofReal (Real.pi^6/120) *
        ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s^5)*F s := by
  have h := lintegral_fun_norm (volume : Measure (EuclideanSpace ℝ (Fin 12)))
    (fun r => F (r^2)) (by fun_prop)
  norm_num only [finrank_euclideanSpace, Fintype.card_fin, show 12-1=11 by norm_num] at h
  rw [h,twelve_ball_constant,squared_radius_change F hF,mul_assoc]

theorem pi_squared_radius (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ y : Fin 12 → ℝ, F (squareRadius y)) =
      ENNReal.ofReal (Real.pi^6/120) *
        ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s^5)*F s := by
  have h := (PiLp.volume_preserving_toLp (Fin 12)).lintegral_comp
    (show Measurable (fun y : EuclideanSpace ℝ (Fin 12) => F (‖y‖^2)) by fun_prop)
  have he : ∀ y : Fin 12 → ℝ, ‖WithLp.toLp 2 y‖^2 = squareRadius y := by
    intro y
    simp [EuclideanSpace.norm_sq_eq,squareRadius,Real.norm_eq_abs,sq_abs]
  simp_rw [he] at h
  refine h.trans ?_
  simpa only [EuclideanSpace.norm_sq_eq,Real.norm_eq_abs,sq_abs,squareRadius] using
    euclidean_squared_radius F hF

theorem pi_ball_squared_radius (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ y in unitBall 12, F (squareRadius y)) =
      ENNReal.ofReal (Real.pi^6/120) *
        ∫⁻ s in Ioo (0 : ℝ) 1, ENNReal.ofReal (s^5)*F s := by
  have h := pi_squared_radius ((Iio (1:ℝ)).indicator F) (hF.indicator measurableSet_Iio)
  have hl : (fun y : Fin 12 → ℝ => (Iio (1:ℝ)).indicator F (squareRadius y)) =
      (unitBall 12).indicator (fun y => F (squareRadius y)) := by
    ext y
    simp [Set.indicator,unitBall]
  have hr : (fun s : ℝ => ENNReal.ofReal (s^5)*(Iio (1:ℝ)).indicator F s) =
      (Iio (1:ℝ)).indicator (fun s => ENNReal.ofReal (s^5)*F s) := by
    ext s
    by_cases hs : s < 1 <;> simp [Set.indicator,hs]
  rw [hl,lintegral_indicator (unitBall_measurable 12),hr,
    lintegral_indicator measurableSet_Iio,Measure.restrict_restrict measurableSet_Iio] at h
  simpa only [Iio_inter_Ioi] using h

#print axioms pi_ball_squared_radius

#print axioms euclidean_squared_radius

#print axioms lintegral_fun_norm
end BecknerOnofri.HighDim.RadialMeasure
