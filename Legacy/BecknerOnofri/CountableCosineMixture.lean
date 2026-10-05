module

public import Legacy.BecknerOnofri.CosineMixture
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

/-! Genuine countable cosine mixtures under an explicit summable uniform majorant. -/
noncomputable section
open MeasureTheory Legacy.TorusEndpoint Filter
open scoped BigOperators Topology
namespace Legacy.BecknerOnofri.CosineMixtureApproximation
open CosineMixture

theorem cosinePower_le_zero (n : ℕ) (x : UnitAddCircle) :
    Legacy.D10.cosinePower n x ≤ Legacy.D10.cosinePower n 0 := by
  have hn : ‖1 + fourier 1 x‖ ≤ (2:ℝ) := by
    have h := norm_add_le (1:ℂ) (fourier 1 x)
    have hf : ‖fourier 1 x‖ = 1 := Circle.norm_coe _
    simpa only [norm_one, hf, one_add_one_eq_two] using h
  have hq : Complex.normSq (1+fourier 1 x) ≤ 4 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg (1+fourier 1 x)]
  unfold Legacy.D10.cosinePower
  rw [fourier_eval_zero]
  rw [show Complex.normSq ((1:ℂ)+1) = 4 by norm_num [Complex.normSq_apply]]
  exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (Complex.normSq_nonneg _) hq n)
    (Nat.cast_nonneg _)

theorem tensor_le_zero {d : ℕ} (N : Fin d → ℕ) (x : Torus d) :
    tensor N x ≤ tensor N 0 :=
  Finset.prod_le_prod₀ (fun i _ => Legacy.D10.cosinePower_nonneg _ _)
    (fun i _ => cosinePower_le_zero _ _)

@[simp] theorem tensor_zero_index {d : ℕ} (x : Torus d) :
    tensor (fun _ : Fin d => 0) x = 1 := by
  simp [tensor, Legacy.D10.cosinePower]

variable {d : ℕ}

def rho (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ) (x : Torus d) : ℝ :=
  ∑' n, w n * tensor (N n) x

def majorant (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ) : ℝ :=
  ∑' n, w n * tensor (N n) 0

variable (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ)

theorem term_norm_le (hw : ∀ n, 0 ≤ w n) (n : ℕ) (x : Torus d) :
    ‖w n * tensor (N n) x‖ ≤ w n * tensor (N n) 0 := by
  rw [Real.norm_of_nonneg (mul_nonneg (hw n) (tensor_nonneg _ _))]
  exact mul_le_mul_of_nonneg_left (tensor_le_zero _ _) (hw n)

theorem summable_terms (hw : ∀ n, 0 ≤ w n)
    (hSup : Summable (fun n => w n * tensor (N n) 0)) (x : Torus d) : Summable (fun n => w n * tensor (N n) x) :=
  hSup.of_norm_bounded (term_norm_le w N hw · x)

theorem rho_nonneg (hw : ∀ n, 0 ≤ w n) (x : Torus d) : 0 ≤ rho w N x :=
  tsum_nonneg (fun n => mul_nonneg (hw n) (tensor_nonneg _ _))

theorem rho_le_majorant (hw : ∀ n, 0 ≤ w n)
    (hSup : Summable (fun n => w n * tensor (N n) 0)) (x : Torus d) : rho w N x ≤ majorant w N :=
  (summable_terms w N hw hSup x).tsum_le_tsum
    (fun n => mul_le_mul_of_nonneg_left (tensor_le_zero _ _) (hw n)) hSup

theorem majorant_nonneg (hw : ∀ n, 0 ≤ w n) : 0 ≤ majorant w N := rho_nonneg w N hw 0

theorem rho_continuous (hw : ∀ n, 0 ≤ w n)
    (hSup : Summable (fun n => w n * tensor (N n) 0)) : Continuous (rho w N) :=
  continuous_tsum (fun n => (tensor_continuous _).const_mul _) hSup (term_norm_le w N hw)

theorem rho_integrable (hw : ∀ n, 0 ≤ w n)
    (hSup : Summable (fun n => w n * tensor (N n) 0)) : Integrable (rho w N) (torusMeasure d) :=
  (rho_continuous w N hw hSup).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem rho_mass (hw : ∀ n, 0 ≤ w n) (hm : HasSum w 1) : (∫ x, rho w N x ∂torusMeasure d) = 1 := by
  have hi (n : ℕ) : Integrable (fun x => w n * tensor (N n) x) (torusMeasure d) :=
    (tensor_integrable _).const_mul _
  have hn (n : ℕ) : (∫ x, ‖w n * tensor (N n) x‖ ∂torusMeasure d) = w n := by
    simp_rw [Real.norm_of_nonneg (mul_nonneg (hw n) (tensor_nonneg _ _))]
    rw [integral_const_mul, tensor_mass, mul_one]
  have hs : Summable (fun n => ∫ x, ‖w n * tensor (N n) x‖ ∂torusMeasure d) := by
    simpa only [hn] using hm.summable
  have h := integral_tsum_of_summable_integral_norm hi hs
  simp only [integral_const_mul, tensor_mass, mul_one] at h
  exact h.symm.trans hm.tsum_eq

def probabilityDensity (hw : ∀ n, 0 ≤ w n) (hm : HasSum w 1)
    (hSup : Summable (fun n => w n * tensor (N n) 0)) : ProbabilityDensity d where
  value := rho w N
  nonneg := ae_of_all _ (rho_nonneg w N hw)
  integrable := rho_integrable w N hw hSup
  mass := rho_mass w N hw hm

theorem rho_finiteEntropy (hw : ∀ n, 0 ≤ w n) (hm : HasSum w 1)
    (hSup : Summable (fun n => w n * tensor (N n) 0)) : (probabilityDensity w N hw hm hSup).FiniteEntropy :=
  (Real.continuous_mul_log.comp (rho_continuous w N hw hSup)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem partial_uniform (hw : ∀ n, 0 ≤ w n)
    (hSup : Summable (fun n => w n * tensor (N n) 0)) :
    TendstoUniformly (fun m x => ∑ n ∈ Finset.range m, w n * tensor (N n) x)
      (rho w N) atTop :=
  tendstoUniformly_tsum_nat hSup (term_norm_le w N hw)

#print axioms rho_mass
#print axioms rho_finiteEntropy
end Legacy.BecknerOnofri.CosineMixtureApproximation
