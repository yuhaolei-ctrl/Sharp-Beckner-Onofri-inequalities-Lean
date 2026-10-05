import Legacy.BecknerOnofri.GaussianLattice

/-!
The actual Gaussian sum on `Fin d → ℤ` is the d-th power of the real theta
series. Both a zero-valued zero mode and a nonzero-frequency subtype are
provided, with summability proved separately from their sum identities.
-/

open scoped BigOperators

namespace Legacy.BecknerOnofri.GaussianLattice

open Legacy.TorusEndpoint Legacy.TorusEndpoint.GreenMultiplierSummability
open Legacy.BecknerOnofri.ThetaDomination

/-- Factorization of the actual Euclidean lattice Gaussian. -/
theorem gaussian_eq_product {d : ℕ} (t : ℝ) (k : Frequency d) :
    gaussian t k = ∏ i : Fin d, Real.exp (-t * (k i : ℝ) ^ 2) := by
  unfold gaussian radiusSq
  rw [Finset.mul_sum, Real.exp_sum]

/-- The Gaussian lattice sum equals the theta power, with absolute convergence
supplied to the finite-product summation theorem. -/
theorem tsum_gaussian_eq_theta_pow (d : ℕ) {t : ℝ} (ht : 0 < t) :
    (∑' k : Frequency d, gaussian t k) = realTheta t ^ d := by
  have hnorm (i : Fin d) :
      Summable (fun n : ℤ ↦ ‖(Real.exp (-t * (n : ℝ) ^ 2) : ℂ)‖) := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
      summable_realTheta ht
  have hc := TorusHeatPositivity.finite_product_tsum d
    (fun _ n ↦ (Real.exp (-t * (n : ℝ) ^ 2) : ℂ)) hnorm
  simp only [← Complex.ofReal_prod, ← Complex.ofReal_tsum] at hc
  have hr := congrArg Complex.re hc
  simp_rw [gaussian_eq_product]
  simpa only [Complex.ofReal_re, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    realTheta] using hr

@[simp] theorem gaussian_zero (d : ℕ) (t : ℝ) : gaussian t (0 : Frequency d) = 1 := by
  simp [gaussian, radiusSq]

/-- The Gaussian with its single zero-frequency term removed. -/
noncomputable def nonzeroGaussian {d : ℕ} (t : ℝ) (k : Frequency d) : ℝ :=
  if k = 0 then 0 else gaussian t k

theorem nonzeroGaussian_nonneg {d : ℕ} (t : ℝ) (k : Frequency d) :
    0 ≤ nonzeroGaussian t k := by
  unfold nonzeroGaussian
  split_ifs
  · exact le_rfl
  · exact (Real.exp_pos _).le

theorem summable_nonzeroGaussian {d : ℕ} {t : ℝ} (ht : 0 < t) :
    Summable (nonzeroGaussian t : Frequency d → ℝ) := by
  refine Summable.of_nonneg_of_le (nonzeroGaussian_nonneg t) ?_ (summable_gaussian ht)
  intro k
  unfold nonzeroGaussian
  split_ifs
  · exact (Real.exp_pos _).le
  · exact le_rfl

/-- Zero-mode removal for the convergent full lattice Gaussian sum. -/
theorem tsum_nonzeroGaussian_eq_theta_pow_sub_one (d : ℕ) {t : ℝ} (ht : 0 < t) :
    (∑' k : Frequency d, nonzeroGaussian t k) = realTheta t ^ d - 1 := by
  have h := (summable_gaussian (d := d) ht).tsum_eq_add_tsum_ite (0 : Frequency d)
  rw [tsum_gaussian_eq_theta_pow d ht, gaussian_zero] at h
  change realTheta t ^ d = 1 + ∑' k : Frequency d, nonzeroGaussian t k at h
  linarith

/-- Absolute convergence also holds when the zero frequency is excluded by its type. -/
theorem summable_gaussian_nonzero {d : ℕ} {t : ℝ} (ht : 0 < t) :
    Summable (fun k : {k : Frequency d // k ≠ 0} ↦ gaussian t k.val) :=
  (summable_gaussian ht).subtype (fun k ↦ k ≠ 0)

/-- The subtype-indexed nonzero lattice sum is exactly `θ(t)^d - 1`. -/
theorem tsum_gaussian_nonzero_eq_theta_pow_sub_one (d : ℕ) {t : ℝ} (ht : 0 < t) :
    (∑' k : {k : Frequency d // k ≠ 0}, gaussian t k.val) = realTheta t ^ d - 1 := by
  have hsupp : Function.support (nonzeroGaussian t : Frequency d → ℝ) ⊆ {k | k ≠ 0} := by
    intro k hk hz
    subst k
    exact hk (by simp [nonzeroGaussian])
  have h := (hasSum_subtype_iff_of_support_subset hsupp).2
    (summable_nonzeroGaussian (d := d) ht).hasSum
  rw [tsum_nonzeroGaussian_eq_theta_pow_sub_one d ht] at h
  have hsub : HasSum (fun k : {k : Frequency d // k ≠ 0} ↦ gaussian t k.val)
      (realTheta t ^ d - 1) := h.congr_fun (fun k ↦ by
    simp only [Function.comp_apply, nonzeroGaussian, if_neg k.property])
  exact hsub.tsum_eq

end Legacy.BecknerOnofri.GaussianLattice
