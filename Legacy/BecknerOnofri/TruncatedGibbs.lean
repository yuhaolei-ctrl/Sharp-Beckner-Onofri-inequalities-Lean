module

public import Legacy.BecknerOnofri.SubcriticalAttainmentDefs
public import Legacy.TorusEndpoint.PhysicalGreenL2
public import Mathlib.MeasureTheory.Function.LpOrder

@[expose] public section

/-! Upper-truncated Gibbs densities for actual L² potentials. The truncation
requires no prior exponential integrability of the untruncated potential. -/
noncomputable section
open Set Filter MeasureTheory Legacy.TorusEndpoint
open scoped BigOperators Topology ENNReal
namespace Legacy.BecknerOnofri.TruncatedGibbs

def truncated {d : ℕ} (f : Torus d → ℝ) (N : ℕ) (x : Torus d) : ℝ := min (f x) (N : ℝ)
def numerator {d : ℕ} (f : Torus d → ℝ) (N : ℕ) (x : Torus d) : ℝ := Real.exp (truncated f N x)
def partition {d : ℕ} (f : Torus d → ℝ) (N : ℕ) : ℝ := ∫ x, numerator f N x ∂torusMeasure d

theorem truncated_memLp {d : ℕ} {f : Torus d → ℝ} (hf : MemLp f 2 (torusMeasure d)) (N : ℕ) :
    MemLp (truncated f N) 2 (torusMeasure d) := hf.inf (memLp_const (N : ℝ))

theorem numerator_memLp {d : ℕ} {f : Torus d → ℝ} (hf : MemLp f 2 (torusMeasure d)) (N : ℕ) :
    MemLp (numerator f N) 2 (torusMeasure d) := by
  apply MemLp.of_bound (Real.continuous_exp.comp_aestronglyMeasurable (truncated_memLp hf N).aestronglyMeasurable)
    (Real.exp (N : ℝ))
  apply ae_of_all
  intro x
  simpa only [numerator, truncated, Real.norm_eq_abs, Real.abs_exp] using
    Real.exp_le_exp.mpr (min_le_right (f x) (N : ℝ))

theorem numerator_integrable {d : ℕ} {f : Torus d → ℝ}
    (hf : MemLp f 2 (torusMeasure d)) (N : ℕ) : Integrable (numerator f N) (torusMeasure d) :=
  (numerator_memLp hf N).integrable (by norm_num)

theorem partition_pos {d : ℕ} {f : Torus d → ℝ} (hf : MemLp f 2 (torusMeasure d)) (N : ℕ) :
    0 < partition f N := integral_exp_pos (numerator_integrable hf N)

def density {d : ℕ} {f : Torus d → ℝ} (hf : MemLp f 2 (torusMeasure d)) (N : ℕ) : ProbabilityDensity d where
  value x := numerator f N x / partition f N
  nonneg := ae_of_all _ (fun x => div_nonneg (Real.exp_nonneg _) (partition_pos hf N).le)
  integrable := (numerator_integrable hf N).div_const _
  mass := by rw [integral_div]; exact div_self (partition_pos hf N).ne'

theorem density_pos {d : ℕ} {f : Torus d → ℝ} (hf : MemLp f 2 (torusMeasure d)) (N : ℕ)
    (x : Torus d) : 0 < (density hf N).value x := div_pos (Real.exp_pos _) (partition_pos hf N)

theorem density_memLp {d : ℕ} {f : Torus d → ℝ} (hf : MemLp f 2 (torusMeasure d)) (N : ℕ) :
    MemLp (density hf N).value 2 (torusMeasure d) := by
  simpa only [density, div_eq_mul_inv] using (numerator_memLp hf N).mul_const (partition f N)⁻¹

theorem density_finiteEntropy {d : ℕ} {f : Torus d → ℝ} (hf : MemLp f 2 (torusMeasure d)) (N : ℕ) :
    (density hf N).FiniteEntropy := PhysicalGreenL2.finiteEntropy_of_memLp _ (density_memLp hf N)

theorem log_density {d : ℕ} {f : Torus d → ℝ} (hf : MemLp f 2 (torusMeasure d)) (N : ℕ)
    (x : Torus d) : Real.log ((density hf N).value x) = truncated f N x - Real.log (partition f N) := by
  change Real.log (Real.exp (truncated f N x) / partition f N) = _
  rw [Real.log_div (Real.exp_pos _).ne' (partition_pos hf N).ne', Real.log_exp]

theorem entropy_identity {d : ℕ} {f : Torus d → ℝ} (hf : MemLp f 2 (torusMeasure d)) (N : ℕ) :
    densityEntropy (density hf N).value =
      (∫ x, (density hf N).value x * truncated f N x ∂torusMeasure d) - Real.log (partition f N) := by
  unfold densityEntropy
  simp_rw [log_density, mul_sub]
  have hp : Integrable (fun x => (density hf N).value x * truncated f N x) (torusMeasure d) := by
    exact (density_memLp hf N).integrable_mul (truncated_memLp hf N)
  rw [integral_sub hp ((density hf N).integrable.mul_const _),
    integral_mul_const, (density hf N).mass, one_mul]

theorem log_partition_le_pairing_sub_entropy {d : ℕ} {f : Torus d → ℝ}
    (hf : MemLp f 2 (torusMeasure d)) (N : ℕ) :
    Real.log (partition f N) ≤
      (∫ x, (density hf N).value x * f x ∂torusMeasure d) - densityEntropy (density hf N).value := by
  have hh := integral_mono_ae ((density_memLp hf N).integrable_mul (truncated_memLp hf N))
    ((density_memLp hf N).integrable_mul hf)
    (ae_of_all _ (fun x => mul_le_mul_of_nonneg_left (min_le_left (f x) (N : ℝ))
      (density_pos hf N x).le))
  rw [entropy_identity]
  simp only [Pi.mul_apply] at hh
  linarith

/-- Monotone convergence turns a uniform truncated partition bound into actual
exponential integrability and the full logarithmic bound. -/
theorem integrable_exp_of_truncated_log_bound {d : ℕ} {f : Torus d → ℝ}
    (hf : MemLp f 2 (torusMeasure d)) {C : ℝ}
    (hbound : ∀ N, Real.log (partition f N) ≤ C) :
    Integrable (fun x => Real.exp (f x)) (torusMeasure d) ∧
      Real.log (∫ x, Real.exp (f x) ∂torusMeasure d) ≤ C := by
  have hZ : ∀ N, partition f N ≤ Real.exp C := by
    intro N
    rw [← Real.exp_log (partition_pos hf N)]
    exact Real.exp_le_exp.mpr (hbound N)
  have he (x : Torus d) : ENNReal.ofReal (Real.exp (f x)) =
      ⨆ N : ℕ, ENNReal.ofReal (numerator f N x) := by
    apply le_antisymm
    · obtain ⟨N, hN⟩ := exists_nat_ge (f x)
      have hn : numerator f N x = Real.exp (f x) := by simp [numerator, truncated, min_eq_left hN]
      rw [← hn]
      exact le_iSup (fun N : ℕ => ENNReal.ofReal (numerator f N x)) N
    · apply iSup_le
      intro N
      exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (min_le_left _ _))
  have hlin : (∫⁻ x, ENNReal.ofReal (Real.exp (f x)) ∂torusMeasure d) ≤ ENNReal.ofReal (Real.exp C) := by
    calc
      _ = ∫⁻ x, ⨆ N : ℕ, ENNReal.ofReal (numerator f N x) ∂torusMeasure d :=
        lintegral_congr he
      _ = ⨆ N : ℕ, ∫⁻ x, ENNReal.ofReal (numerator f N x) ∂torusMeasure d := by
        apply lintegral_iSup' (fun N => (numerator_memLp hf N).aemeasurable.ennreal_ofReal)
        apply ae_of_all
        intro x N M hNM
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.mpr
        exact min_le_min_left _ (by exact_mod_cast hNM)
      _ ≤ _ := by
        apply iSup_le
        intro N
        rw [← ofReal_integral_eq_lintegral_ofReal (numerator_integrable hf N)
          (ae_of_all _ (fun x => Real.exp_nonneg (truncated f N x)))]
        exact ENNReal.ofReal_le_ofReal (hZ N)
  have hi : Integrable (fun x => Real.exp (f x)) (torusMeasure d) := by
    refine ⟨Real.continuous_exp.comp_aestronglyMeasurable hf.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_norm]
    simpa only [Real.norm_eq_abs, Real.abs_exp] using hlin.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hi, ?_⟩
  have hI : (∫ x, Real.exp (f x) ∂torusMeasure d) ≤ Real.exp C := by
    rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun x => Real.exp_nonneg (f x)))] at hlin
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hlin
    simpa only [ENNReal.toReal_ofReal (integral_nonneg (fun x => Real.exp_nonneg (f x))),
      ENNReal.toReal_ofReal (Real.exp_nonneg C)] using hh
  exact (Real.log_le_iff_le_exp (integral_exp_pos hi)).mpr hI

#print axioms density_finiteEntropy
#print axioms entropy_identity
#print axioms log_partition_le_pairing_sub_entropy
#print axioms integrable_exp_of_truncated_log_bound

end Legacy.BecknerOnofri.TruncatedGibbs
