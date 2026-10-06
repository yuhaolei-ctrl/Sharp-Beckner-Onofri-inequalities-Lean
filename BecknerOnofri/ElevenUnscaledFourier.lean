module

public import BecknerOnofri.ElevenEuclideanFourier

@[expose] public section

/-! The unscaled Euclidean profile in the displayed Section 4 formula.
The actual Fourier integral is evaluated by Gamma–Gaussian subordination. -/
noncomputable section
open MeasureTheory Set
namespace BecknerOnofri.HighDim.Eleven

lemma unscaledProfile_fourier (w : EuclideanSpace ℝ (Fin 11)) :
    (∫ x : EuclideanSpace ℝ (Fin 11),
      StudentIntegral.phase w x * (((122880/Real.pi^6)*(1+‖x‖^2)^(-(11:ℝ)):ℝ):ℂ)) =
        (fourierProfile (2*Real.pi*‖w‖):ℂ) := by
  let z : ℝ := 2*Real.pi*‖w‖
  let R : ℝ := Real.pi^((11:ℝ)/2)
  let A : ℝ := Real.sqrt Real.pi*Real.exp (-z)*fourierPolynomial z/32
  let L : ℂ := ∫ x : EuclideanSpace ℝ (Fin 11),
    StudentIntegral.phase w x*((1+1*‖x‖^2)^(-(11:ℝ)):ℝ)
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have h := StudentIntegral.student_fourier_subordination 11
    (by norm_num : (11:ℝ)/2 < 11) (by norm_num : (0:ℝ)<1) w
  have hg : Real.Gamma 11 = 3628800 := by
    convert Real.Gamma_nat_eq_factorial 10 using 1 <;> norm_num
  have hi : (∫ t in Ioi (0:ℝ), t^((9:ℝ)/2)*
      Real.exp (-t-Real.pi^2*‖w‖^2/(1*t))) = A := by
    have he (t : ℝ) : Real.pi^2*‖w‖^2/(1*t) = z^2/(4*t) := by dsimp [z]; ring
    simp_rw [he]
    exact ReciprocalGaussian.laplace_half_eleven hz
  norm_num only [Nat.cast_ofNat] at h
  rw [hg, hi, div_one] at h
  change L*(3628800:ℂ) = (R:ℂ)*(A:ℂ) at h
  have hL : L = ((R*A/3628800:ℝ):ℂ) := by
    apply mul_right_cancel₀ (by norm_num : (3628800:ℂ)≠0)
    rw [h]
    push_cast
    ring
  have he (x : EuclideanSpace ℝ (Fin 11)) :
      StudentIntegral.phase w x * (((122880/Real.pi^6)*(1+‖x‖^2)^(-(11:ℝ)):ℝ):ℂ) =
        (((122880/Real.pi^6):ℝ):ℂ)*
          (StudentIntegral.phase w x*((1+1*‖x‖^2)^(-(11:ℝ)):ℝ)) := by
    simp only [one_mul]
    push_cast
    ring
  simp_rw [he]
  rw [integral_const_mul]
  change (((122880/Real.pi^6):ℝ):ℂ)*L = (fourierProfile z:ℂ)
  rw [hL, ← Complex.ofReal_mul]
  apply congrArg Complex.ofReal
  have hp : R = Real.pi^5*Real.sqrt Real.pi := by
    dsimp [R]
    rw [show (11:ℝ)/2 = (5:ℕ)+(1/2:ℝ) by norm_num,
      Real.rpow_add Real.pi_pos, Real.rpow_natCast, ← Real.sqrt_eq_rpow]
  rw [hp]
  dsimp [A, fourierProfile]
  have hs := Real.sq_sqrt Real.pi_pos.le
  field_simp
  rw [hs]
  ring


#print axioms unscaledProfile_fourier
end BecknerOnofri.HighDim.Eleven
