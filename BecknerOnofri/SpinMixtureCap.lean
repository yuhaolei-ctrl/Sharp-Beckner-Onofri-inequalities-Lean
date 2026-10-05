import BecknerOnofri.BinarySpinChannel
import BecknerOnofri.EntropyMixtureRigidity

/-! The all-minus probability cap for the actual positive cosine mixture.
This supplies the extra constraint in the thirteen-state feasible domain. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped BigOperators
namespace BecknerOnofri.HighDim.Spin
open Legacy.D10 Legacy.BecknerOnofri

theorem cosinePower_first_moment (n : ℕ) :
    (∫ x : UnitAddCircle,cosinePower n x*(fourier 1 x).re ∂AddCircle.haarAddCircle)=
      (n:ℝ)/((n:ℝ)+1) := by
  have hc := CosineFourier.coefficient_neg_nat n 1
  have hi : Integrable (fun x : UnitAddCircle => fourier 1 x*(cosinePower n x:ℂ))
      AddCircle.haarAddCircle := by
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    exact (fourier 1).continuous.mul ((Complex.continuous_ofReal.comp (cosinePower_continuous n)))
  simp only [_root_.fourierCoeff,neg_neg,Nat.cast_one,smul_eq_mul] at hc
  have hr := congrArg Complex.re hc
  have hre : (∫ x : UnitAddCircle, fourier 1 x*(cosinePower n x:ℂ) ∂AddCircle.haarAddCircle).re =
      ∫ x : UnitAddCircle, (fourier 1 x*(cosinePower n x:ℂ)).re ∂AddCircle.haarAddCircle :=
    (integral_re hi).symm
  rw [hre] at hr
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero] at hr
  simpa only [mul_comm,EntropyTail.first_coefficient] using hr

theorem cosinePower_minus_spin (n : ℕ) :
    (∫ x : UnitAddCircle,cosinePower n x*((1-(fourier 1 x).re)/2) ∂AddCircle.haarAddCircle)=
      1/(2*((n:ℝ)+1)) := by
  have hi : Integrable (fun x : UnitAddCircle => cosinePower n x*(fourier 1 x).re)
      AddCircle.haarAddCircle := by
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    exact (cosinePower_continuous n).mul (Complex.continuous_re.comp (fourier 1).continuous)
  simp_rw [mul_div,mul_sub,mul_one]
  rw [integral_div,integral_sub (cosinePower_integrable n) hi,CosineFourier.mass,cosinePower_first_moment]
  have hn : (n:ℝ)+1≠0 := by positivity
  field_simp [hn]
  ring

theorem tensor_minus_spin (N : Fin 12 → ℕ) :
    (∫ x : Torus 12,CosineMixture.tensor N x*channel (torusCosines x) ∅ ∂torusMeasure 12)=
      ∏ i : Fin 12,1/(2*((N i:ℝ)+1)) := by
  simp only [channel,Finset.prod_empty,Finset.compl_empty,one_mul,CosineMixture.tensor,
    ← Finset.prod_mul_distrib,torusCosines]
  unfold torusMeasure
  rw [integral_fintype_prod_eq_prod (fun i x => cosinePower (N i) x*((1-(fourier 1 x).re)/2))]
  simp_rw [cosinePower_minus_spin]

theorem tensor_minus_spin_bound (N : Fin 12 → ℕ) :
    (∫ x : Torus 12,CosineMixture.tensor N x*channel (torusCosines x) ∅ ∂torusMeasure 12)≤1/4096 := by
  rw [tensor_minus_spin]
  calc
    (∏ i : Fin 12,1/(2*((N i:ℝ)+1)))≤∏ _ : Fin 12,(1/2:ℝ) := by
      apply Finset.prod_le_prod (fun i _ => by positivity)
      intro i _
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      have hn : 0≤(N i:ℝ) := Nat.cast_nonneg _
      linarith
    _ =1/4096 := by norm_num

#print axioms tensor_minus_spin_bound
end BecknerOnofri.HighDim.Spin
