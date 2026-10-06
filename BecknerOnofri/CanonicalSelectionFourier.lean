module

public import BecknerOnofri.SteinerOptimizerMixture

@[expose] public section

/-! Nonnegative real Fourier coefficients of cosine mixtures, and propagation
to the prescribed mean-zero Green potential by the actual Euler equation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
namespace BecknerOnofri.HighDim.PrescribedSelection

lemma mixture_fourier_nonnegative {d : ℕ} (ρ : ProbabilityDensity d)
    (hρ : IsCountableCosineMixture ρ) (k : Frequency d) :
    0 ≤ (fourierCoeff ρ.value k).re ∧ (fourierCoeff ρ.value k).im=0 := by
  obtain ⟨w,N,hw,hs,he⟩ := hρ
  have hc : fourierCoeff ρ.value k =
      ((∑' n, w n * RandomRectangles.componentCoeff (N n) k : ℝ) : ℂ) := by
    rw [fourierCoeff_congr_ae he]
    exact CosineMixtureTransfer.rho_fourier w N hw hs.summable k
  rw [hc]
  exact ⟨tsum_nonneg (fun n => mul_nonneg (hw n) (RandomRectangles.componentCoeff_nonneg _ _)),rfl⟩

lemma minimizer_green_fourier_nonnegative {d : ℕ} (hd : 0 < d) {β : ℝ} (hβ : 0 < β)
    (ρ : ProbabilityDensity d) (hρ : IsGlobalMinimizer β ρ) (hM : IsCountableCosineMixture ρ)
    (u : Torus d → ℝ) (hm : MeanZero u)
    (hG : u =ᵐ[torusMeasure d] Gap.densityPotential β ρ.value) :
    ∀ k : Frequency d, 0 ≤ (fourierCoeff ρ.value k).re ∧ (fourierCoeff ρ.value k).im=0 ∧
      0 ≤ (fourierCoeff u k).re ∧ (fourierCoeff u k).im=0 := by
  intro k
  obtain ⟨hR,hI⟩ := mixture_fourier_nonnegative ρ hM k
  refine ⟨hR,hI,?_⟩
  by_cases hk : k=0
  · subst k
    have hz : fourierCoeff u 0=0 := by
      simp only [fourierCoeff,neg_zero,UnitAddTorus.mFourier_zero,ContinuousMap.one_apply,one_mul]
      rw [integral_complex_ofReal,show (∫ x,u x ∂torusMeasure d)=0 from hm]
      rfl
    simp [hz]
  · have he := (OptimizerDuality.minimizer_smooth_positive_kirkwood hd hβ ρ hρ).2.2 ⟨k,hk⟩
    rw [← fourierCoeff_congr_ae hG] at he
    have hp : 0 < frequencyLength k^d := lt_of_lt_of_le zero_lt_one
      (GreenCritical.nonzero_eigenvalue_ge_one ⟨k,hk⟩)
    have hβσ : 0 ≤ β/spectralThreshold d := (div_pos hβ (spectralThreshold_pos hd)).le
    have hr := congrArg Complex.re he
    have hi := congrArg Complex.im he
    simp only [← Complex.ofReal_pow,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul,mul_zero,sub_zero,add_zero,hI] at hr hi
    constructor
    · nlinarith [mul_nonneg hβσ hR]
    · nlinarith

#print axioms minimizer_green_fourier_nonnegative
end BecknerOnofri.HighDim.PrescribedSelection
