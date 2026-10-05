module

public import BecknerOnofri.CountableMixtureTransfer
public import BecknerOnofri.EntropyShearer.Density

@[expose] public section

/-! Actual coordinate deletion for countable cosine mixtures, including the
lower-dimensional density, Fourier energy, and entropy identifications. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators Topology
open Finset MeasureTheory Filter

namespace BecknerOnofri.CosineMixtureTransfer
open RectangleLattice RandomRectangles Legacy.TorusEndpoint
open Legacy.BecknerOnofri Legacy.D10

variable {d : ℕ}

/-- Delete the indicated coordinate, retaining the canonical `Fin` ordering. -/
def drop {α : Type*} (i : Fin (d+1)) (x : Fin (d+1) → α) : Fin d → α :=
  fun j => x (i.succAbove j)

theorem tensor_insert (i : Fin (d+1)) (N : Fin (d+1) → ℕ)
    (t : UnitAddCircle) (x : Torus d) :
    CosineMixture.tensor N (i.insertNth t x) =
      cosinePower (N i) t * CosineMixture.tensor (drop i N) x := by
  unfold CosineMixture.tensor drop
  rw [Fin.prod_univ_succAbove _ i]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]

theorem componentCoeff_insert (i : Fin (d+1)) (N : Fin (d+1) → ℕ) (k : Frequency d) :
    componentCoeff N (i.insertNth 0 k) = componentCoeff (drop i N) k := by
  unfold componentCoeff binomialProduct drop
  rw [Fin.prod_univ_succAbove _ i]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove,
    Int.natAbs_zero, coeff_zero, one_mul]

theorem weight_insert (i : Fin (d+1)) (p : ℝ) (k : Frequency d) :
    weight p (i.insertNth 0 k) = weight p k := by
  unfold weight normSq
  rw [Fin.sum_univ_succAbove _ i]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove,
    Int.cast_zero, zero_pow (by decide : 2 ≠ 0), zero_add]

theorem rho_fourier_insert (i : Fin (d+1)) (w : ℕ → ℝ) (N : ℕ → Fin (d+1) → ℕ)
    (hw : ∀ n, 0 ≤ w n) (hs : Summable w) (k : Frequency d) :
    densityFourier (CosineMixtureApproximation.rho w N) (i.insertNth 0 k) =
      densityFourier (CosineMixtureApproximation.rho w (fun n => drop i (N n))) k := by
  simp only [rho_fourier w N hw hs, componentCoeff_insert,
    rho_fourier w (fun n => drop i (N n)) hw hs]

/-- The deleted-coordinate Fourier energy is exactly the actual energy of the
lower-dimensional mixture, with no scale or multiplicity correction. -/
theorem deletionEnergy_drop (i : Fin (d+1)) (p : ℝ) (w : ℕ → ℝ)
    (N : ℕ → Fin (d+1) → ℕ) (hw : ∀ n, 0 ≤ w n) (hs : Summable w) :
    deletionEnergy p (CosineMixtureApproximation.rho w N) i =
      energy p (CosineMixtureApproximation.rho w (fun n => drop i (N n))) := by
  let f : Frequency (d+1) → ℝ := fun k =>
    (if k i = 0 then weight p k else 0) *
      ‖densityFourier (CosineMixtureApproximation.rho w N) k‖^2
  have hsupport : Function.support f ⊆ Set.range (i.insertNth (0:ℤ)) := by
    intro k hk
    have hki : k i = 0 := by
      by_contra h
      exact hk (by simp [f, h])
    exact ⟨drop i k, (Fin.insertNth_eq_iff.mpr ⟨hki.symm, rfl⟩)⟩
  have ht := (Fin.insertNth_right_injective (α := fun _ => ℤ) (p := i) (0:ℤ)).tsum_eq hsupport
  change (∑' k, f k) = _
  rw [← ht]
  unfold energy
  apply tsum_congr
  intro k
  simp only [f, Fin.insertNth_apply_same, if_true, weight_insert,
    rho_fourier_insert i w N hw hs]

theorem cosinePower_zero_ge_one (n : ℕ) : 1 ≤ cosinePower n 0 := by
  have h := integral_mono (cosinePower_integrable n) (integrable_const (cosinePower n 0))
    (CosineMixtureApproximation.cosinePower_le_zero n)
  simpa only [CosineFourier.mass, integral_const, probReal_univ, smul_eq_mul, one_mul] using h

theorem tensor_drop_zero_le (i : Fin (d+1)) (N : Fin (d+1) → ℕ) :
    CosineMixture.tensor (drop i N) 0 ≤ CosineMixture.tensor N 0 := by
  have he : Fin.insertNth (α := fun _ => UnitAddCircle) i (0:UnitAddCircle) (0 : Torus d) = 0 := by
    apply Fin.insertNth_eq_iff.mpr
    exact ⟨rfl, rfl⟩
  rw [← he, tensor_insert]
  exact le_mul_of_one_le_left (CosineMixture.tensor_nonneg _ _) (cosinePower_zero_ge_one _)

theorem summable_drop_majorant (i : Fin (d+1)) (w : ℕ → ℝ)
    (N : ℕ → Fin (d+1) → ℕ) (hw : ∀ n, 0 ≤ w n)
    (hSup : Summable (fun n => w n * CosineMixture.tensor (N n) 0)) :
    Summable (fun n => w n * CosineMixture.tensor (drop i (N n)) 0) :=
  hSup.of_nonneg_of_le (fun n => mul_nonneg (hw n) (CosineMixture.tensor_nonneg _ _))
    (fun n => mul_le_mul_of_nonneg_left (tensor_drop_zero_le i (N n)) (hw n))

/-- Full dimension transfer to actual lower-dimensional cosine mixtures. -/
theorem countable_mixture_dimension_transfer (hd : 12 ≤ d) (w : ℕ → ℝ)
    (N : ℕ → Fin (d+1) → ℕ) (hw : ∀ n, 0 ≤ w n) (hs : Summable w)
    (hSup : Summable (fun n => w n * CosineMixture.tensor (N n) 0)) :
    energy ((d+1:ℕ):ℝ) (CosineMixtureApproximation.rho w N) ≤ (1/(d:ℝ)) *
      ∑ i : Fin (d+1), energy (d:ℝ)
        (CosineMixtureApproximation.rho w (fun n => drop i (N n))) := by
  have h := countable_mixture_comparison (by omega : 13 ≤ d+1) w N hw hs hSup
  simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right,
    deletionEnergy_drop _ _ w N hw hs] using h


theorem integral_drop (i : Fin (d+1)) (f : Torus d → ℝ) :
    (∫ x : Torus (d+1), f (drop i x) ∂torusMeasure (d+1)) =
      ∫ x : Torus d, f x ∂torusMeasure d := by
  have h := (measurePreserving_piFinSuccAbove
    (fun _ : Fin (d+1) => AddCircle.haarAddCircle) i).integral_comp'
      (fun z : UnitAddCircle × Torus d => f z.2)
  change (∫ x, f (drop i x) ∂Measure.pi (fun _ => AddCircle.haarAddCircle)) = _
  rw [show (fun x : Torus (d+1) => f (drop i x)) =
      (fun x => (fun z : UnitAddCircle × Torus d => f z.2)
        (MeasurableEquiv.piFinSuccAbove (fun _ => UnitAddCircle) i x)) by rfl, h]
  simp only [integral_fun_snd, probReal_univ, one_smul]
  rfl

/-- Actual Fubini marginal of a component, expressed by coordinate deletion. -/
theorem tensor_marginal (i : Fin (d+1)) (N : Fin (d+1) → ℕ) (x : Torus (d+1)) :
    (∫ t, CosineMixture.tensor N (Function.update x i t) ∂AddCircle.haarAddCircle) =
      CosineMixture.tensor (drop i N) (drop i x) := by
  have he (t : UnitAddCircle) : Function.update x i t = i.insertNth t (drop i x) :=
    (Fin.insertNth_removeNth i t x).symm
  simp_rw [he, tensor_insert]
  rw [integral_mul_const, CosineFourier.mass, one_mul]

/-- The infinite series commutes with actual marginalization, proved from its
summable uniform majorant. -/
theorem rho_marginal (i : Fin (d+1)) (w : ℕ → ℝ) (N : ℕ → Fin (d+1) → ℕ)
    (hw : ∀ n, 0 ≤ w n)
    (hSup : Summable (fun n => w n * CosineMixture.tensor (N n) 0)) (x : Torus (d+1)) :
    (∫ t, CosineMixtureApproximation.rho w N (Function.update x i t) ∂AddCircle.haarAddCircle) =
      CosineMixtureApproximation.rho w (fun n => drop i (N n)) (drop i x) := by
  let F (n : ℕ) (t : UnitAddCircle) : ℝ :=
    w n * CosineMixture.tensor (N n) (Function.update x i t)
  have hc (n : ℕ) : Continuous (F n) := by
    apply Continuous.const_mul
    apply (CosineMixture.tensor_continuous _).comp
    exact continuous_const.update i continuous_id
  have hi (n : ℕ) : Integrable (F n) AddCircle.haarAddCircle :=
    (hc n).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hbound (n : ℕ) : (∫ t, ‖F n t‖ ∂AddCircle.haarAddCircle) ≤
      w n * CosineMixture.tensor (N n) 0 := by
    have h := integral_mono (hi n).norm (integrable_const (w n * CosineMixture.tensor (N n) 0))
      (fun t => CosineMixtureApproximation.term_norm_le w N hw n (Function.update x i t))
    simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using h
  have hs : Summable (fun n => ∫ t, ‖F n t‖ ∂AddCircle.haarAddCircle) :=
    hSup.of_nonneg_of_le (fun n => integral_nonneg (fun _ => norm_nonneg _)) hbound
  have h := integral_tsum_of_summable_integral_norm hi hs
  change (∫ t, ∑' n, F n t ∂AddCircle.haarAddCircle) = _
  rw [← h]
  unfold CosineMixtureApproximation.rho
  apply tsum_congr
  intro n
  simp only [F, integral_const_mul, tensor_marginal]

theorem avg_rho (i : Fin (d+1)) (w : ℕ → ℝ) (N : ℕ → Fin (d+1) → ℕ)
    (hw : ∀ n, 0 ≤ w n)
    (hSup : Summable (fun n => w n * CosineMixture.tensor (N n) 0)) :
    HighDim.EntropyShearer.avg {i} (CosineMixtureApproximation.rho w N) =
      fun x => CosineMixtureApproximation.rho w (fun n => drop i (N n)) (drop i x) := by
  rw [HighDim.EntropyShearer.avg_singleton]
  funext x
  exact rho_marginal i w N hw hSup x

/-- Entropy of the true lower-dimensional mixture equals entropy of its
ambient-coordinate marginal. Both use normalized Haar measure. -/
theorem entropy_drop (i : Fin (d+1)) (w : ℕ → ℝ) (N : ℕ → Fin (d+1) → ℕ)
    (hw : ∀ n, 0 ≤ w n)
    (hSup : Summable (fun n => w n * CosineMixture.tensor (N n) 0)) :
    densityEntropy (CosineMixtureApproximation.rho w (fun n => drop i (N n))) =
      densityEntropy (HighDim.EntropyShearer.avg {i} (CosineMixtureApproximation.rho w N)) := by
  rw [avg_rho i w N hw hSup]
  unfold densityEntropy
  exact (integral_drop i (fun x =>
    CosineMixtureApproximation.rho w (fun n => drop i (N n)) x *
      Real.log (CosineMixtureApproximation.rho w (fun n => drop i (N n)) x))).symm


/-- Strict positivity also descends to every true lower-dimensional marginal. -/
theorem rho_drop_pos (i : Fin (d+1)) (w : ℕ → ℝ) (N : ℕ → Fin (d+1) → ℕ)
    (hw : ∀ n, 0 ≤ w n)
    (hSup : Summable (fun n => w n * CosineMixture.tensor (N n) 0))
    (hpos : ∀ x, 0 < CosineMixtureApproximation.rho w N x) (x : Torus d) :
    0 < CosineMixtureApproximation.rho w (fun n => drop i (N n)) x := by
  have h := ((HighDim.EntropyShearer.positiveBounded_of_continuous_pos
    (CosineMixtureApproximation.rho_continuous w N hw hSup) hpos).avg {i}).pos
      (i.insertNth (0 : UnitAddCircle) x)
  rw [avg_rho i w N hw hSup] at h
  have he : drop i (i.insertNth (0:UnitAddCircle) x) = x := by
    funext j
    exact Fin.insertNth_apply_succAbove i _ _ j
  change 0 < CosineMixtureApproximation.rho w (fun n => drop i (N n))
    (drop i (i.insertNth (0:UnitAddCircle) x)) at h
  rw [he] at h
  exact h

/-- Shearer in the exact lower-dimensional mixture notation used by the
Fourier transfer theorem. -/
theorem mixture_entropy_deletion_le (w : ℕ → ℝ) (N : ℕ → Fin (d+1) → ℕ)
    (hw : ∀ n, 0 ≤ w n) (hm : HasSum w 1)
    (hSup : Summable (fun n => w n * CosineMixture.tensor (N n) 0))
    (hpos : ∀ x, 0 < CosineMixtureApproximation.rho w N x) :
    (∑ i : Fin (d+1), densityEntropy (CosineMixtureApproximation.rho w
      (fun n => drop i (N n)))) ≤ (d : ℝ) * densityEntropy (CosineMixtureApproximation.rho w N) := by
  let r : HighDim.ProbabilityDensity (d+1) := {
    value := CosineMixtureApproximation.rho w N
    nonneg := Eventually.of_forall (fun x => (hpos x).le)
    integrable := CosineMixtureApproximation.rho_integrable w N hw hSup
    mass := CosineMixtureApproximation.rho_mass w N hw hm }
  have h := HighDim.EntropyShearer.deletion_of_continuous_pos r
    (CosineMixtureApproximation.rho_continuous w N hw hSup) hpos
  simp_rw [entropy_drop _ w N hw hSup]
  simpa only [r, HighDim.EntropyShearer.entropyIntegral, HighDim.entropy,
    Nat.cast_add, Nat.cast_one, add_sub_cancel_right, densityEntropy,
    HighDim.torusMeasure, torusMeasure_explicit] using h

#print axioms countable_mixture_dimension_transfer
#print axioms entropy_drop

end BecknerOnofri.CosineMixtureTransfer
