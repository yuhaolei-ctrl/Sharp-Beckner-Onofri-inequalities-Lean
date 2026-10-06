module

public import BecknerOnofri.CosineMixtureTransfer
public import Mathlib.Analysis.Normed.Group.Tannery

@[expose] public section

noncomputable section
set_option autoImplicit false
open scoped BigOperators Topology
open Finset MeasureTheory Filter

namespace BecknerOnofri.CosineMixtureTransfer
open RectangleLattice RandomRectangles Legacy.TorusEndpoint
open Legacy.BecknerOnofri Legacy.D10

variable {d : ℕ}

theorem coeff_le_one (n j : ℕ) : binomialCoeffReal n j ≤ 1 := by
  simpa using coeff_antitone n (Nat.zero_le j)

theorem componentCoeff_le_one (N : Fin d → ℕ) (k : Frequency d) : componentCoeff N k ≤ 1 := by
  unfold componentCoeff binomialProduct
  exact prod_le_one₀ (fun _ _ => coeff_nonneg _ _) (fun _ _ => coeff_le_one _ _)

theorem summable_mixture_coeff (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ)
    (hw : ∀ n, 0 ≤ w n) (hs : Summable w) (k : Frequency d) :
    Summable (fun n => w n * componentCoeff (N n) k) :=
  hs.of_nonneg_of_le (fun n => mul_nonneg (hw n) (componentCoeff_nonneg _ _))
    (fun n => by simpa using mul_le_mul_of_nonneg_left (componentCoeff_le_one (N n) k) (hw n))

/-- Countable cosine mixtures have exactly the summed nonnegative coefficients. -/
theorem rho_fourier (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ)
    (hw : ∀ n, 0 ≤ w n) (hs : Summable w) (k : Frequency d) :
    densityFourier (CosineMixtureApproximation.rho w N) k =
      ((∑' n, w n * componentCoeff (N n) k : ℝ) : ℂ) := by
  let F (n : ℕ) (x : Torus d) : ℂ :=
    UnitAddTorus.mFourier (-k) x * ((w n * CosineMixture.tensor (N n) x : ℝ) : ℂ)
  have hi (n : ℕ) : Integrable (F n) (torusMeasure d) := by
    exact ((UnitAddTorus.mFourier (-k)).continuous.mul
      (Complex.continuous_ofReal.comp ((CosineMixture.tensor_continuous _).const_mul _)))
        |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hn (n : ℕ) : (∫ x, ‖F n x‖ ∂torusMeasure d) = w n := by
    have he (x : Torus d) : ‖F n x‖ = w n * CosineMixture.tensor (N n) x := by
      simp only [F, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hw n), abs_of_nonneg (CosineMixture.tensor_nonneg _ _)]
      have hm : ‖UnitAddTorus.mFourier (-k) x‖ = 1 := by
        simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, norm_prod,
          fourier_apply, Circle.norm_coe, prod_const_one]
      rw [hm, one_mul]
    simp_rw [he]
    rw [integral_const_mul, CosineMixture.tensor_mass, mul_one]
  have hsum : Summable (fun n => ∫ x, ‖F n x‖ ∂torusMeasure d) := by simpa only [hn] using hs
  have h := integral_tsum_of_summable_integral_norm hi hsum
  have he (n : ℕ) : (∫ x, F n x ∂torusMeasure d) =
      ((w n * componentCoeff (N n) k : ℝ) : ℂ) := by
    simp only [F, Complex.ofReal_mul]
    rw [show (fun x => UnitAddTorus.mFourier (-k) x * ((w n:ℂ) *
      (CosineMixture.tensor (N n) x:ℂ))) =
      (fun x => (w n:ℂ) * (UnitAddTorus.mFourier (-k) x *
      (CosineMixture.tensor (N n) x:ℂ))) by funext x; ring]
    rw [integral_const_mul]
    change _ * densityFourier (CosineMixture.tensor (N n)) k = _
    rw [CosineMixture.tensor_fourier]
    rfl
  simp_rw [he] at h
  rw [← Complex.ofReal_tsum] at h
  rw [h]
  unfold densityFourier CosineMixtureApproximation.rho
  apply integral_congr_ae
  filter_upwards [] with x
  rw [Complex.ofReal_tsum, ← tsum_mul_left]

/-- Parseval supplies the summable bound needed for the limit of partial mixtures. -/
theorem summable_fourier_sq {f : Torus d → ℝ} (hf : Continuous f) :
    Summable (fun k : Frequency d => ‖densityFourier f k‖^2) := by
  have hm : MemLp f 2 (torusMeasure d) :=
    hf.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hmc : MemLp (fun x => (f x:ℂ)) 2 (torusMeasure d) := hm.ofReal
  have he (k : Frequency d) :
      UnitAddTorus.mFourierCoeff (hmc.toLp (fun x => (f x:ℂ))) k = densityFourier f k := by
    unfold UnitAddTorus.mFourierCoeff densityFourier
    apply integral_congr_ae
    have hae : hmc.toLp (fun x => (f x:ℂ)) =ᵐ[torusMeasure d] (fun x => (f x:ℂ)) := hmc.coeFn_toLp
    filter_upwards [hae] with x hx
    simp only [smul_eq_mul, hx]
  exact (UnitAddTorus.hasSum_sq_mFourierCoeff (hmc.toLp (fun x => (f x:ℂ)))).summable.congr
    (fun k => congrArg (fun z : ℂ => ‖z‖^2) (he k))

theorem normSq_ge_one {k : Frequency d} (hk : k ≠ 0) : 1 ≤ normSq k := by
  have hex : ∃ i, k i ≠ 0 := by contrapose! hk; exact funext hk
  obtain ⟨i, hi⟩ := hex
  have hi1 : (1:ℤ) ≤ (k i)^2 := by have h := sq_pos_of_ne_zero hi; omega
  have hi1r : (1:ℝ) ≤ (k i:ℝ)^2 := by exact_mod_cast hi1
  exact hi1r.trans (single_le_sum (fun j _ => sq_nonneg (k j:ℝ)) (mem_univ i))

theorem weight_nonneg (p : ℝ) (k : Frequency d) : 0 ≤ weight p k :=
  Real.rpow_nonneg (normSq_nonneg k) _

theorem weight_le_one {p : ℝ} (hp : 0 < p) (k : Frequency d) : weight p k ≤ 1 := by
  by_cases hk : k = 0
  · subst k
    rw [weight_zero hp]
    norm_num
  · exact Real.rpow_le_one_of_one_le_of_nonpos (normSq_ge_one hk) (by linarith)

/-- Partial mixtures converge in every bounded nonnegative weighted Fourier energy. -/
theorem partial_weighted_energy_tendsto (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ)
    (hw : ∀ n, 0 ≤ w n) (hs : Summable w)
    (hSup : Summable (fun n => w n * CosineMixture.tensor (N n) 0))
    (g : Frequency d → ℝ) (hg : ∀ k, 0 ≤ g k ∧ g k ≤ 1) :
    Tendsto (fun m : ℕ => ∑' k, g k *
      ‖densityFourier (CosineMixture.mixture (range m) w N) k‖^2) atTop
      (𝓝 (∑' k, g k * ‖densityFourier (CosineMixtureApproximation.rho w N) k‖^2)) := by
  have hc (k : Frequency d) :
      Tendsto (fun m : ℕ => ∑ n ∈ range m, w n * componentCoeff (N n) k) atTop
        (𝓝 (∑' n, w n * componentCoeff (N n) k)) :=
    (summable_mixture_coeff w N hw hs k).hasSum.tendsto_sum_nat
  apply tendsto_tsum_of_dominated_convergence
    (summable_fourier_sq (CosineMixtureApproximation.rho_continuous w N hw hSup))
  · intro k
    simp_rw [CosineMixture.mixture_fourier, rho_fourier w N hw hs,
      Complex.norm_real, Real.norm_eq_abs, sq_abs]
    exact (hc k).pow 2 |>.const_mul (g k)
  · exact Eventually.of_forall (fun m k => by
      have hpart : 0 ≤ ∑ n ∈ range m, w n * componentCoeff (N n) k :=
        sum_nonneg (fun n _ => mul_nonneg (hw n) (componentCoeff_nonneg _ _))
      have hle := (summable_mixture_coeff w N hw hs k).sum_le_tsum (range m)
        (fun n _ => mul_nonneg (hw n) (componentCoeff_nonneg _ _))
      simp only [CosineMixture.mixture_fourier, rho_fourier w N hw hs,
        Complex.norm_real, Real.norm_eq_abs, sq_abs]
      change |g k * (∑ n ∈ range m, w n * componentCoeff (N n) k)^2| ≤ _
      rw [abs_of_nonneg (mul_nonneg (hg k).1 (sq_nonneg _))]
      calc
        _ ≤ (∑ n ∈ range m, w n * componentCoeff (N n) k)^2 :=
          mul_le_of_le_one_left (sq_nonneg _) (hg k).2
        _ ≤ _ := sq_le_sq₀ hpart (hpart.trans hle) |>.mpr hle)

/-- Exact dimension transfer for countable correlated cosine mixtures with
summable uniform majorant. No independence of the latent coordinate indices is used. -/
theorem countable_mixture_comparison (hd : 13 ≤ d) (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ)
    (hw : ∀ n, 0 ≤ w n) (hs : Summable w)
    (hSup : Summable (fun n => w n * CosineMixture.tensor (N n) 0)) :
    energy (d:ℝ) (CosineMixtureApproximation.rho w N) ≤ (1 / ((d:ℝ)-1)) *
      ∑ i : Fin d, deletionEnergy ((d:ℝ)-1) (CosineMixtureApproximation.rho w N) i := by
  have hd0 : (0:ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hdm : (0:ℝ) < (d:ℝ)-1 := by
    have : (13:ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hleft := partial_weighted_energy_tendsto w N hw hs hSup (weight (d:ℝ))
    (fun k => ⟨weight_nonneg _ _, weight_le_one hd0 k⟩)
  have hright (i : Fin d) := partial_weighted_energy_tendsto w N hw hs hSup
    (fun k => if k i = 0 then weight ((d:ℝ)-1) k else 0)
    (fun k => by split_ifs; exact ⟨weight_nonneg _ _, weight_le_one hdm k⟩; norm_num)
  have hr := (tendsto_finsetSum univ (fun i _ => hright i)).const_mul (1/((d:ℝ)-1))
  exact le_of_tendsto_of_tendsto hleft hr (Eventually.of_forall fun m =>
    finite_mixture_comparison hd (range m) w N (fun n _ => hw n))

#print axioms rho_fourier
#print axioms countable_mixture_comparison

end BecknerOnofri.CosineMixtureTransfer
