module

public import BecknerOnofri.ElevenEuclideanFourier
public import BecknerOnofri.ElevenUnscaledFourier
public import BecknerOnofri.ElevenPeriodizedMass
public import BecknerOnofri.PeriodizationCharacter
public import BecknerOnofri.PeriodizationComplexIntegral

@[expose] public section

/-! Fourier coefficients of the actual periodized competitor, obtained by
unfolding the lattice sum on the normalized Haar fundamental cube. -/
noncomputable section
open MeasureTheory Set
namespace BecknerOnofri.HighDim.Eleven
set_option backward.isDefEq.respectTransparency false

lemma profile_character_integrable (k : Frequency 11) :
    Integrable (fun x : Fin 11 → ℝ => liftedCharacter k x * (euclideanProfile x:ℂ)) := by
  apply euclideanProfile_integrable.norm.mono'
    ((liftedCharacter_measurable k).mul
      (Complex.measurable_ofReal.comp euclideanProfile_continuous.measurable)).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by
    change ‖liftedCharacter k x * (euclideanProfile x:ℂ)‖ ≤ ‖euclideanProfile x‖
    rw [norm_mul, liftedCharacter_norm, one_mul, Complex.norm_real])

lemma periodizedProfile_fourier_unfold (k : Frequency 11) :
    fourierCoeff periodizedProfile k =
      ∫ x : Fin 11 → ℝ, liftedCharacter k x * (euclideanProfile x:ℂ) := by
  have hm := PeriodizationCube.quotient_measurePreserving 11
  have hme : Measurable (fun x : Torus 11 => UnitAddTorus.mFourier (-k) x * (periodizedProfile x:ℂ)) :=
    (UnitAddTorus.mFourier (-k)).continuous.measurable.mul
      (Complex.measurable_ofReal.comp periodizedProfile_measurable)
  have h := integral_map (μ := volume.restrict (PeriodizationCube.cube 11))
    hm.measurable.aemeasurable hme.aestronglyMeasurable
  rw [hm.map_eq] at h
  change fourierCoeff periodizedProfile k = _ at h
  rw [h]
  calc
    _ = ∫ x in PeriodizationCube.cube 11, ∑' n : Frequency 11,
        liftedCharacter k (fun i => x i+(n i:ℝ)) *
          (euclideanProfile (fun i => x i+(n i:ℝ)):ℂ) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (PeriodizationCube.cube_measurable 11)] with x hx
      rw [periodizedProfile_on_cube hx, Complex.ofReal_tsum, ← tsum_mul_left]
      apply tsum_congr
      intro n
      rw [liftedCharacter_periodic]
      rfl
    _ = _ := PeriodizationCube.unfold_integral_complex 11 _
      ((liftedCharacter_measurable k).mul
        (Complex.measurable_ofReal.comp euclideanProfile_continuous.measurable))
      (profile_character_integrable k)

/-- The `c = 25` formula for the scaled profile `η_{1/5}`, derived from the `c = 1` display
`unscaledProfile_fourier` by the change of variables `x ↦ 5x`. -/
lemma euclideanProfile_fourier_via_unscaled (w : EuclideanSpace ℝ (Fin 11)) :
    (∫ x : EuclideanSpace ℝ (Fin 11),
      StudentIntegral.phase w x * (euclideanProfile (fun i => x i):ℂ)) =
        (fourierProfile (2*Real.pi*‖w‖/5):ℂ) := by
  let U : EuclideanSpace ℝ (Fin 11) → ℝ := fun y => (122880/Real.pi^6)*(1+‖y‖^2)^(-(11:ℝ))
  let g : EuclideanSpace ℝ (Fin 11) → ℂ := fun y =>
    StudentIntegral.phase ((5:ℝ)⁻¹ • w) y * (U y:ℂ)
  have hpt (x : EuclideanSpace ℝ (Fin 11)) :
      StudentIntegral.phase w x * (euclideanProfile (fun i => x i):ℂ) =
        (((5:ℝ)^11:ℝ):ℂ) * g ((5:ℝ) • x) := by
    have hph : StudentIntegral.phase w x =
        StudentIntegral.phase ((5:ℝ)⁻¹ • w) ((5:ℝ) • x) := by
      unfold StudentIntegral.phase
      congr 3
      rw [real_inner_smul_left, real_inner_smul_right]; field_simp
    have hU : euclideanProfile (fun i => x i) = (5:ℝ)^11 * U ((5:ℝ) • x) := by
      rw [euclideanProfile_norm]
      simp only [U, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ) < 5), mul_pow]
      ring_nf
    rw [hph, hU]; simp only [g]; push_cast; ring
  have hsc := MeasureTheory.Measure.integral_comp_smul
    (μ := (volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 11)))) g (5:ℝ)
  have hu := unscaledProfile_fourier ((5:ℝ)⁻¹ • w)
  have hn : ‖(5:ℝ)⁻¹ • w‖ = ‖w‖ / 5 := by rw [norm_smul]; simp [div_eq_inv_mul]
  rw [hn] at hu
  simp_rw [hpt]
  rw [MeasureTheory.integral_const_mul, hsc, finrank_euclideanSpace_fin]
  change _ * (|((5:ℝ)^11)⁻¹| • ∫ y, g y) = _
  rw [show (∫ y, g y) = (fourierProfile (2*Real.pi*(‖w‖/5)):ℂ) from hu, Complex.real_smul,
    abs_of_pos (by positivity)]
  push_cast
  field_simp

lemma periodizedProfile_fourier (k : Frequency 11) :
    fourierCoeff periodizedProfile k = (fourierProfile (2*Real.pi*frequencyLength k/5):ℂ) := by
  rw [periodizedProfile_fourier_unfold]
  have h := (PiLp.volume_preserving_toLp (Fin 11)).integral_comp
    (MeasurableEquiv.toLp 2 _).measurableEmbedding
    (fun x : EuclideanSpace ℝ (Fin 11) =>
      StudentIntegral.phase (WithLp.toLp 2 (fun i => (k i:ℝ))) x *
        (euclideanProfile (fun i => x i):ℂ))
  have he : (∫ x : Fin 11 → ℝ, liftedCharacter k x * (euclideanProfile x:ℂ)) =
      ∫ x : EuclideanSpace ℝ (Fin 11),
        StudentIntegral.phase (WithLp.toLp 2 (fun i => (k i:ℝ))) x *
          (euclideanProfile (fun i => x i):ℂ) := by
    rw [← h]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => by dsimp only; rw [liftedCharacter_eq_phase])
  rw [he, euclideanProfile_fourier_via_unscaled]
  congr 2
  rw [EuclideanSpace.norm_eq]
  simp only [Real.norm_eq_abs, sq_abs]
  rfl

lemma periodizedProfile_fourier_pos (k : Frequency 11) :
    0 < (fourierCoeff periodizedProfile k).re := by
  rw [periodizedProfile_fourier, Complex.ofReal_re]
  have hk : 0 ≤ frequencyLength k := Real.sqrt_nonneg _
  unfold fourierProfile fourierPolynomial
  positivity

#print axioms periodizedProfile_fourier
end BecknerOnofri.HighDim.Eleven
