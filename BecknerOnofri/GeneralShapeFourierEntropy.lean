module

public import BecknerOnofri.GeneralShapeChannelEntropy

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped BigOperators
namespace BecknerOnofri.HighDim.ShapeEntropy
open Legacy.TorusEndpoint Legacy.BecknerOnofri
open TorusSobolev SmoothFourier ContinuousGibbs ContinuousSymmetry

theorem density_coefficient_real {ρ : ProbabilityDensity 12} (D : Data ρ) (k : HighDim.Frequency 12) :
    (HighDim.fourierCoeff ρ.value k).im = 0 := by
  obtain ⟨w,N,hw,hm,_,he⟩ := D.mixture
  change (densityFourier ρ.value k).im = 0
  rw [he, CosineMixtureTransfer.rho_fourier w N hw hm.summable]
  rfl

theorem density_axis_re {ρ : ProbabilityDensity 12} (D : Data ρ) (i : Fin 12) (n : ℤ) :
    (HighDim.fourierCoeff ρ.value (Pi.single i n)).re =
      ∫ x, ρ.value x * (fourier n (x i)).re ∂HighDim.torusMeasure 12 := by
  have hf := (continuous_density D)
  have hi : Integrable (fun x => UnitAddTorus.mFourier (-Pi.single i n) x *
      (ρ.value x : ℂ)) (HighDim.torusMeasure 12) :=
    ((UnitAddTorus.mFourier _).continuous.mul (Complex.continuous_ofReal.comp hf)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  unfold HighDim.fourierCoeff
  have hre := integral_re hi
  change (∫ x, (UnitAddTorus.mFourier (-Pi.single i n) x *
      (ρ.value x : ℂ)).re ∂HighDim.torusMeasure 12) =
    (∫ x, UnitAddTorus.mFourier (-Pi.single i n) x *
      (ρ.value x : ℂ) ∂HighDim.torusMeasure 12).re at hre
  rw [← hre]
  apply integral_congr_ae
  filter_upwards [] with x
  have hchar (k : ℤ) : UnitAddTorus.mFourier (Pi.single i k) x = fourier k (x i) := by
    classical
    change (∏ j, fourier ((Pi.single i k : HighDim.Frequency 12) j) (x j)) = _
    rw [Finset.prod_eq_single i]
    · simp
    · intro j _ hji; simp [Pi.single_eq_of_ne hji]
    · simp
  rw [← Pi.single_neg, hchar, fourier_neg]
  simp [Complex.mul_re, mul_comm]

theorem density_axis_norm_sq {ρ : ProbabilityDensity 12} (D : Data ρ) (i : Fin 12) (n : ℤ) :
    ‖HighDim.fourierCoeff ρ.value (Pi.single i n)‖^2 =
      (∫ x, ρ.value x * (fourier n (x i)).re ∂HighDim.torusMeasure 12)^2 := by
  have h := Complex.sq_norm_sub_sq_im (HighDim.fourierCoeff ρ.value (Pi.single i n))
  simpa only [density_coefficient_real D, zero_pow (by decide : 2 ≠ 0), sub_zero, density_axis_re D] using h

lemma density_axis_mean {ρ : ProbabilityDensity 12} (D : Data ρ) (i : Fin 12) :
    (∫ x,ρ.value x*(fourier 1 (x i)).re ∂torusMeasure 12)=
      Spin.mean (Spin.countLaw (Spin.channelLaw ρ)) := by
  rw [Spin.channel_count_mean ρ (exchangeable D)]
  rw [← ContinuousSymmetry.integral_pointPermutation (Equiv.swap (0 : Fin 12) i)]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [D.symmetric]
  congr 2
  simp [ContinuousSymmetry.pointPermutation_apply]

theorem channel_fourier_entropy {ρ : ProbabilityDensity 12} (D : Data ρ)
    (ψ : ℝ → ℝ) (hc : ContinuousOn ψ (Icc (0 : ℝ) 1))
    (hcv : ConvexOn ℝ (Icc (0 : ℝ) 1) ψ)
    (hminor : ∀ t ∈ Ico (0 : ℝ) 1, ψ t ≤ CircleScalar.gamma t) :
    (∀ i : Fin 12, Summable (fun n : ℕ =>
      ‖HighDim.fourierCoeff ρ.value (Pi.single i (n+3 : ℤ))‖^2 / (n+3 : ℝ))) ∧
    2 * Spin.relativeEntropy (Spin.countLaw (Spin.channelLaw ρ)) Spin.reference +
      12 * ψ (Spin.mean (Spin.countLaw (Spin.channelLaw ρ))) +
      (21/1000) * (∑ i : Fin 12, ‖HighDim.fourierCoeff ρ.value (Pi.single i (2 : ℤ))‖^2) +
      (67/100) * (∑ i : Fin 12, ∑' n : ℕ,
        ‖HighDim.fourierCoeff ρ.value (Pi.single i (n+3 : ℤ))‖^2 / (n+3 : ℝ)) ≤
      HighDim.entropy ρ := by
  have h := channel_entropy D ψ hc hcv hminor
  simpa only [density_axis_norm_sq D, density_axis_mean D, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat] using h

theorem spin_mean_range {ρ : ProbabilityDensity 12} (D : Data ρ) :
    Spin.mean (Spin.countLaw (Spin.channelLaw ρ)) ∈ Icc (0 : ℝ) 1 := by
  have heq : Spin.mean (Spin.countLaw (Spin.channelLaw ρ)) =
      (HighDim.fourierCoeff ρ.value (Pi.single (0 : Fin 12) (1 : ℤ))).re := by
    rw [density_axis_re D, density_axis_mean D]
  rw [heq]
  obtain ⟨w,N,hw,hm,hSup,he⟩ := D.mixture
  rw [he]
  change (densityFourier (CosineMixtureApproximation.rho w N) (Pi.single (0 : Fin 12) (1 : ℤ))).re ∈ Icc (0 : ℝ) 1
  rw [CosineMixtureTransfer.rho_fourier w N hw hm.summable, Complex.ofReal_re]
  constructor
  · exact tsum_nonneg (fun n => mul_nonneg (hw n) (RandomRectangles.componentCoeff_nonneg _ _))
  · have hsum := CosineMixtureTransfer.summable_mixture_coeff w N hw hm.summable
      (Pi.single (0 : Fin 12) (1 : ℤ))
    have hle := hsum.tsum_le_tsum (fun n => mul_le_of_le_one_right (hw n)
      (CosineMixtureTransfer.componentCoeff_le_one _ _)) hm.summable
    exact hle.trans_eq hm.tsum_eq


#print axioms channel_fourier_entropy
#print axioms spin_mean_range
end BecknerOnofri.HighDim.ShapeEntropy
