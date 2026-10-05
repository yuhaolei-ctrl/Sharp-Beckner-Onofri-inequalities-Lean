module

public import BecknerOnofri.SpinMixtureCap
public import BecknerOnofri.EntropyTailMixedHeat

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped BigOperators
namespace BecknerOnofri.HighDim.Spin
open Legacy.D10 Legacy.BecknerOnofri

def subsetFrequency (S : Finset (Fin 12)) : Frequency 12 := fun i => if i∈S then 1 else 0
def cosineMonomial (S : Finset (Fin 12)) (x : Torus 12) : ℝ := ∏ i ∈ S, (fourier 1 (x i)).re

theorem cosineMonomial_continuous (S : Finset (Fin 12)) : Continuous (cosineMonomial S) := by
  exact continuous_finsetProd _ (fun i _ => (Complex.continuous_re.comp (fourier 1).continuous).comp (continuous_apply i))

theorem cosineMonomial_norm_le (S : Finset (Fin 12)) (x : Torus 12) : ‖cosineMonomial S x‖ ≤ 1 := by
  rw [cosineMonomial, norm_prod]
  exact Finset.prod_le_one₀ (fun i _ => norm_nonneg _) (fun i _ => torusCosines_bound x i)

theorem cosineMonomial_eq_product (S : Finset (Fin 12)) (x : Torus 12) :
    cosineMonomial S x = ∏ i : Fin 12, if i∈S then (fourier 1 (x i)).re else 1 := by
  classical
  simp [cosineMonomial, Finset.prod_ite_mem]

theorem tensor_cosine_moment (N : Fin 12 → ℕ) (S : Finset (Fin 12)) :
    (∫ x : Torus 12, CosineMixture.tensor N x*cosineMonomial S x ∂torusMeasure 12) =
      RandomRectangles.componentCoeff N (subsetFrequency S) := by
  classical
  simp only [CosineMixture.tensor, cosineMonomial_eq_product, ← Finset.prod_mul_distrib]
  unfold torusMeasure
  rw [integral_fintype_prod_eq_prod
    (fun i x => cosinePower (N i) x*(if i∈S then (fourier 1 x).re else 1))]
  unfold RandomRectangles.componentCoeff binomialProduct subsetFrequency
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i∈S
  · simp only [if_pos hi, Int.natAbs_one, cosinePower_first_moment, EntropyTail.first_coefficient]
  · simp only [if_neg hi, mul_one, Int.natAbs_zero, RandomRectangles.coeff_zero, CosineFourier.mass]

theorem mixture_cosine_moment (w : ℕ → ℝ) (N : ℕ → Fin 12 → ℕ)
    (hw : ∀ n,0≤w n) (hs : Summable w)
    (hSup : Summable (fun n => w n*CosineMixture.tensor (N n) 0)) (S : Finset (Fin 12)) :
    (∫ x : Torus 12, CosineMixtureApproximation.rho w N x*cosineMonomial S x ∂torusMeasure 12) =
      (Legacy.TorusEndpoint.densityFourier (CosineMixtureApproximation.rho w N) (subsetFrequency S)).re := by
  let F (n : ℕ) (x : Torus 12) := w n*CosineMixture.tensor (N n) x*cosineMonomial S x
  have hi (n : ℕ) : Integrable (F n) (torusMeasure 12) := by
    exact (((CosineMixture.tensor_continuous (N n)).const_mul (w n)).mul
      (cosineMonomial_continuous S)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hpoint (n : ℕ) (x : Torus 12) : ‖F n x‖≤w n*CosineMixture.tensor (N n) 0 := by
    dsimp [F]
    rw [abs_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) (cosineMonomial_norm_le S x)).trans
      (CosineMixtureApproximation.term_norm_le w N hw n x)
  have hnorm (n : ℕ) : (∫ x, ‖F n x‖ ∂torusMeasure 12)≤w n*CosineMixture.tensor (N n) 0 := by
    simpa using integral_mono (hi n).norm (integrable_const _) (hpoint n)
  have hsumNorm : Summable (fun n => ∫ x, ‖F n x‖ ∂torusMeasure 12) :=
    hSup.of_nonneg_of_le (fun n => integral_nonneg (fun _ => norm_nonneg _)) hnorm
  have hswap := integral_tsum_of_summable_integral_norm hi hsumNorm
  have hint (n : ℕ) : (∫ x, F n x ∂torusMeasure 12) =
      w n*RandomRectangles.componentCoeff (N n) (subsetFrequency S) := by
    dsimp [F]
    simp_rw [mul_assoc]
    rw [integral_const_mul, tensor_cosine_moment]
  simp only [hint] at hswap
  have he : (fun x : Torus 12 => CosineMixtureApproximation.rho w N x*cosineMonomial S x) =
      (fun x => ∑' n, F n x) := by
    funext x
    dsimp [CosineMixtureApproximation.rho, F]
    rw [tsum_mul_right]
  rw [he, ← hswap, CosineMixtureTransfer.rho_fourier w N hw hs, Complex.ofReal_re]

theorem mixture_channel_joint_fourier (ρ : ProbabilityDensity 12)
    (hρ : GenericCosineRepresentation.HasPositiveCosineMixture ρ.value) (S : Finset (Fin 12)) :
    (∑ σ : Configuration, channelLaw ρ σ*jointSpin S σ) =
      (HighDim.fourierCoeff ρ.value (subsetFrequency S)).re := by
  rw [channelLaw_joint_moment]
  obtain ⟨w,N,hw,hm,hSup,he⟩ := hρ
  rw [he]
  exact mixture_cosine_moment w N hw hm.summable hSup S

#print axioms mixture_channel_joint_fourier
end BecknerOnofri.HighDim.Spin
