import Legacy.BecknerOnofri.CosineFourier
import Legacy.D10.BinomialCorrelated
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-! Actual finite correlated cosine-power mixtures on the unit-volume torus.
These statements include normalization, entropy integrability, and Fourier
coefficients. No independence of the coordinates of the outer index is used. -/

noncomputable section

open Finset MeasureTheory Legacy.TorusEndpoint

namespace Legacy.BecknerOnofri.CosineMixture

def tensor {d : ℕ} (N : Fin d → ℕ) (x : Torus d) : ℝ :=
  ∏ i, Legacy.D10.cosinePower (N i) (x i)

theorem tensor_nonneg {d : ℕ} (N : Fin d → ℕ) (x : Torus d) :
    0 ≤ tensor N x :=
  Finset.prod_nonneg (fun _ _ => Legacy.D10.cosinePower_nonneg _ _)

theorem tensor_continuous {d : ℕ} (N : Fin d → ℕ) : Continuous (tensor N) := by
  unfold tensor
  exact continuous_finsetProd _ (fun i _ => (Legacy.D10.cosinePower_continuous _).comp
    (continuous_apply i))

theorem tensor_integrable {d : ℕ} (N : Fin d → ℕ) :
    Integrable (tensor N) (torusMeasure d) :=
  (tensor_continuous N).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem tensor_mass {d : ℕ} (N : Fin d → ℕ) :
    (∫ x, tensor N x ∂torusMeasure d) = 1 := by
  unfold tensor
  rw [torusMeasure_explicit, integral_fintype_prod_eq_prod (fun i x => Legacy.D10.cosinePower (N i) x)]
  simp [CosineFourier.mass]

theorem tensor_fourier {d : ℕ} (N : Fin d → ℕ) (k : Frequency d) :
    densityFourier (tensor N) k =
      (Legacy.D10.binomialProduct N (fun i => (k i).natAbs) : ℂ) := by
  unfold densityFourier tensor Legacy.D10.binomialProduct
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Pi.neg_apply,
    Complex.ofReal_prod, ← Finset.prod_mul_distrib]
  rw [torusMeasure_explicit, integral_fintype_prod_eq_prod
    (fun i x => fourier (-(k i)) x * (Legacy.D10.cosinePower (N i) x : ℂ))]
  apply Finset.prod_congr rfl
  intro i hi
  exact CosineFourier.coefficient (N i) (k i)

variable {α : Type*} {d : ℕ}

def mixture (s : Finset α) (w : α → ℝ) (N : α → Fin d → ℕ) (x : Torus d) : ℝ :=
  ∑ a ∈ s, w a * tensor (N a) x

theorem mixture_nonneg (s : Finset α) (w : α → ℝ) (N : α → Fin d → ℕ)
    (hw : ∀ a ∈ s, 0 ≤ w a) (x : Torus d) : 0 ≤ mixture s w N x :=
  Finset.sum_nonneg (fun a ha => mul_nonneg (hw a ha) (tensor_nonneg _ _))

theorem mixture_continuous (s : Finset α) (w : α → ℝ) (N : α → Fin d → ℕ) :
    Continuous (mixture s w N) := by
  unfold mixture
  exact continuous_finsetSum _ (fun a _ => (tensor_continuous _).const_mul _)

theorem mixture_integrable (s : Finset α) (w : α → ℝ) (N : α → Fin d → ℕ) :
    Integrable (mixture s w N) (torusMeasure d) :=
  (mixture_continuous s w N).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem mixture_mass (s : Finset α) (w : α → ℝ) (N : α → Fin d → ℕ) :
    (∫ x, mixture s w N x ∂torusMeasure d) = ∑ a ∈ s, w a := by
  unfold mixture
  rw [integral_finsetSum]
  · simp_rw [integral_const_mul, tensor_mass, mul_one]
  · intro a ha
    exact (tensor_integrable _).const_mul _

def density (s : Finset α) (w : α → ℝ) (N : α → Fin d → ℕ)
    (hw : ∀ a ∈ s, 0 ≤ w a) (hm : ∑ a ∈ s, w a = 1) : ProbabilityDensity d where
  value := mixture s w N
  nonneg := ae_of_all _ (mixture_nonneg s w N hw)
  integrable := mixture_integrable s w N
  mass := (mixture_mass s w N).trans hm

theorem finiteEntropy (s : Finset α) (w : α → ℝ) (N : α → Fin d → ℕ)
    (hw : ∀ a ∈ s, 0 ≤ w a) (hm : ∑ a ∈ s, w a = 1) :
    (density s w N hw hm).FiniteEntropy := by
  exact (Real.continuous_mul_log.comp (mixture_continuous s w N)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem mixture_fourier (s : Finset α) (w : α → ℝ) (N : α → Fin d → ℕ)
    (k : Frequency d) :
    densityFourier (mixture s w N) k =
      ((∑ a ∈ s, w a * Legacy.D10.binomialProduct (N a) (fun i => (k i).natAbs) : ℝ) : ℂ) := by
  unfold densityFourier mixture
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum]
  rw [integral_finsetSum]
  · simp_rw [mul_left_comm (UnitAddTorus.mFourier (-k) _) (_ : ℂ), integral_const_mul]
    apply Finset.sum_congr rfl
    intro a ha
    rw [show (∫ x, UnitAddTorus.mFourier (-k) x * (tensor (N a) x : ℂ)
      ∂torusMeasure d) = densityFourier (tensor (N a)) k by rfl, tensor_fourier]
  · intro a ha
    exact ((UnitAddTorus.mFourier (-k)).continuous.mul
      (continuous_const.mul (Complex.continuous_ofReal.comp (tensor_continuous _)))).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem mixture_fourier_norm_sq (s : Finset α) (w : α → ℝ) (N : α → Fin d → ℕ)
    (k : Frequency d) :
    ‖densityFourier (mixture s w N) k‖ ^ 2 =
      ∑ a ∈ s, ∑ b ∈ s, w a * w b *
        (∑ L ∈ Legacy.D10.latentBox (N a), Legacy.D10.latentWeight (N a) (N b) L *
          Legacy.D10.binomialProduct L (fun i => (k i).natAbs)) := by
  rw [mixture_fourier, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  exact Legacy.D10.correlated_mixture_square s w N _

end Legacy.BecknerOnofri.CosineMixture
