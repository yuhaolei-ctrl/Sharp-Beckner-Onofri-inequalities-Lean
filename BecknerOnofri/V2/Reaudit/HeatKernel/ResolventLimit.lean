module

public import BecknerOnofri.V2.Reaudit.HeatKernel.ResolventComparison

@[expose] public section

/-! # Eigenfunction identity and strong resolvent limit for `B_m` (U05/S015, step 4)

For `m ≥ 1`, `c = m(m-1)`, `μ > 0`, the truncated resolvents `R_k` of `P_D + c + min(c cot², k)`
(file `ResolventComparison`) converge strongly, as `k → ∞`, to the spectral operator
`resOp hm μ = (B_m + μ)^{-1}`.

* `green_second`: Green's second identity for two smooth functions vanishing at `0` and `π`.
* `omegaL`: the function `ω_j = (λ_j - c) φ_j + φ_j''`, which equals `c cot² φ_j` on `(0,π)` by the
  eigenvalue equation; it is continuous, hence bounded.
* `key_identity`: `φ_j = (P_D + μ + c)^{-1}((λ_j+μ)φ_j - ω_j)` (coefficientwise in the sine basis, by
  two integrations by parts).
* `Rk_basis_tendsto`: `R_k φ_j → (λ_j+μ)^{-1} φ_j`.
* `tendsto_of_dense_basis`: uniform bound + convergence on a Hilbert basis gives strong convergence.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff
namespace BecknerOnofri.V2.Reaudit.HeatKernel.Engine
open Legacy.BecknerOnofri Legacy.BecknerOnofri.JacobiEigenfunctions
  Legacy.BecknerOnofri.JacobiHeatBounds Legacy.BecknerOnofri.JacobiHeatPositivity
  Legacy.BecknerOnofri.PositiveOperatorNeumann Legacy.BecknerOnofri.BoundedL2Multiplier

/-- The constant `c = m(m-1)` (the bottom of the potential `m(m-1)/sin²`). -/
def cc (m : ℕ) : ℝ := (m : ℝ) * ((m : ℝ) - 1)

theorem cc_nonneg {m : ℕ} (hm : 0 < m) : 0 ≤ cc m := by
  have hh : (1 : ℝ) ≤ m := by exact_mod_cast hm
  exact mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hh)

/-! ### Green's identity -/

theorem green_second {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hf0 : f 0 = 0) (hfp : f Real.pi = 0) (hg0 : g 0 = 0) (hgp : g Real.pi = 0) :
    ∫ x in Ioo 0 Real.pi, (f x * deriv (deriv g) x - deriv (deriv f) x * g x) = 0 := by
  have hf1 : ContDiff ℝ ∞ (deriv f) := (contDiff_infty_iff_deriv.mp hf).2
  have hg1 : ContDiff ℝ ∞ (deriv g) := (contDiff_infty_iff_deriv.mp hg).2
  have hf2 : ContDiff ℝ ∞ (deriv (deriv f)) := (contDiff_infty_iff_deriv.mp hf1).2
  have hg2 : ContDiff ℝ ∞ (deriv (deriv g)) := (contDiff_infty_iff_deriv.mp hg1).2
  have hF : ∀ x ∈ uIcc 0 Real.pi, HasDerivAt (fun x => f x * deriv g x - deriv f x * g x)
      (f x * deriv (deriv g) x - deriv (deriv f) x * g x) x := by
    intro x _
    have a1 := (hf.differentiable (by simp) x).hasDerivAt
    have a2 := (hg1.differentiable (by simp) x).hasDerivAt
    have a3 := (hf1.differentiable (by simp) x).hasDerivAt
    have a4 := (hg.differentiable (by simp) x).hasDerivAt
    convert (a1.mul a2).sub (a3.mul a4) using 1
    ring
  have hint : IntervalIntegrable (fun x => f x * deriv (deriv g) x - deriv (deriv f) x * g x)
      volume 0 Real.pi :=
    ((hf.continuous.mul hg2.continuous).sub (hf2.continuous.mul hg.continuous)).intervalIntegrable
      _ _
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hF hint
  rw [intervalIntegral.integral_of_le Real.pi_pos.le, integral_Ioc_eq_integral_Ioo] at h
  rw [h]
  simp [hf0, hfp, hg0, hgp]

theorem integrableOn_Ioo_of_continuous {h : ℝ → ℝ} (hh : Continuous h) :
    IntegrableOn h (Ioo 0 Real.pi) :=
  (hh.continuousOn.integrableOn_Icc (a := 0) (b := Real.pi)).mono_set Ioo_subset_Icc_self

theorem normalizedFunction_deriv_contDiff (m n : ℕ) :
    ContDiff ℝ ∞ (deriv (normalizedFunction m n)) :=
  (contDiff_infty_iff_deriv.mp (normalizedFunction_contDiff m n)).2

theorem normalizedFunction_deriv2_contDiff (m n : ℕ) :
    ContDiff ℝ ∞ (deriv (deriv (normalizedFunction m n))) :=
  (contDiff_infty_iff_deriv.mp (normalizedFunction_deriv_contDiff m n)).2

theorem sine_second (n : ℕ) {t : ℝ} (ht : t ∈ Ioo 0 Real.pi) :
    deriv (deriv (normalizedFunction 1 n)) t = - eigenvalue 1 n * normalizedFunction 1 n t := by
  have h := normalizedFunction_equation 1 n ht
  unfold JacobiAngular.angularOperator at h
  norm_num at h
  linarith

/-- The eigenvalue equation in the form `φ'' = (c/sin² - λ) φ`. -/
theorem eig_second (m n : ℕ) {t : ℝ} (ht : t ∈ Ioo 0 Real.pi) :
    deriv (deriv (normalizedFunction m n)) t =
      (cc m / Real.sin t ^ 2 - eigenvalue m n) * normalizedFunction m n t := by
  have h := normalizedFunction_equation m n ht
  unfold JacobiAngular.angularOperator at h
  unfold cc
  have : (m : ℝ) * ((m : ℝ) - 1) / Real.sin t ^ 2 * normalizedFunction m n t =
      (m : ℝ) * ((m : ℝ) - 1) / Real.sin t ^ 2 * normalizedFunction m n t := rfl
  linarith

/-! ### The function `ω_j = (λ_j - c)φ_j + φ_j''` -/

/-- `ω_j = (λ_j - c)φ_j + φ_j''`. -/
def omegaFn (m j : ℕ) (x : ℝ) : ℝ :=
  (eigenvalue m j - cc m) * normalizedFunction m j x + deriv (deriv (normalizedFunction m j)) x

theorem omegaFn_continuous (m j : ℕ) : Continuous (omegaFn m j) :=
  (continuous_const.mul (normalizedFunction_contDiff m j).continuous).add
    (normalizedFunction_deriv2_contDiff m j).continuous

/-- On `(0,π)`: `ω_j = c cot² φ_j = W φ_j`. -/
theorem omegaFn_eq (m j : ℕ) {t : ℝ} (ht : t ∈ Ioo 0 Real.pi) :
    omegaFn m j t = cot2 (cc m) t * normalizedFunction m j t := by
  have hs : Real.sin t ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2).ne'
  unfold omegaFn cot2
  rw [eig_second m j ht]
  have h2 := Real.sin_sq_add_cos_sq t
  field_simp
  rw [show Real.cos t ^ 2 = 1 - Real.sin t ^ 2 by linarith]
  ring

theorem memLp_of_continuous {h : ℝ → ℝ} (hh : Continuous h) : MemLp h 2 intervalMeasure := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := Real.pi)).exists_bound_of_continuousOn
    hh.continuousOn
  refine MemLp.of_bound hh.aestronglyMeasurable C ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  exact hC x ⟨hx.1.le, hx.2.le⟩

/-- `ω_j` as an element of `L²(0,π)`. -/
def omegaL (m j : ℕ) : JacobiL2 := (memLp_of_continuous (omegaFn_continuous m j)).toLp _

theorem omegaL_ae (m j : ℕ) : omegaL m j =ᵐ[intervalMeasure] omegaFn m j :=
  (memLp_of_continuous (omegaFn_continuous m j)).coeFn_toLp

theorem inner_basis_of_ae (m n : ℕ) (u : JacobiL2) (h : ℝ → ℝ) (hu : u =ᵐ[intervalMeasure] h) :
    inner ℝ (normalizedVector m n) u = ∫ y in Ioo 0 Real.pi, normalizedFunction m n y * h y := by
  rw [inner_basis_eq_integral]
  apply integral_congr_ae
  filter_upwards [hu] with y hy
  rw [hy]

theorem inner_basis_phi (m n : ℕ) (k l : ℕ) :
    inner ℝ (normalizedVector m n) (normalizedVector k l) =
      ∫ y in Ioo 0 Real.pi, normalizedFunction m n y * normalizedFunction k l y :=
  inner_basis_of_ae m n _ _ (normalizedVector_ae_eq k l)

theorem integral_b_omega {m : ℕ} (hm : 0 < m) (j n : ℕ) :
    ∫ y in Ioo 0 Real.pi, normalizedFunction 1 n y * omegaFn m j y =
      (eigenvalue m j - cc m - eigenvalue 1 n) *
        ∫ y in Ioo 0 Real.pi, normalizedFunction 1 n y * normalizedFunction m j y := by
  have hG := green_second (normalizedFunction_contDiff 1 n) (normalizedFunction_contDiff m j)
    (normalizedFunction_zero one_pos n) (normalizedFunction_pi one_pos n)
    (normalizedFunction_zero hm j) (normalizedFunction_pi hm j)
  have cb := (normalizedFunction_contDiff 1 n).continuous
  have cg := (normalizedFunction_contDiff m j).continuous
  have cb2 := (normalizedFunction_deriv2_contDiff 1 n).continuous
  have cg2 := (normalizedFunction_deriv2_contDiff m j).continuous
  have i1 : IntegrableOn (fun y => normalizedFunction 1 n y * deriv (deriv (normalizedFunction m j)) y)
      (Ioo 0 Real.pi) := integrableOn_Ioo_of_continuous (cb.mul cg2)
  have i2 : IntegrableOn (fun y => deriv (deriv (normalizedFunction 1 n)) y * normalizedFunction m j y)
      (Ioo 0 Real.pi) := integrableOn_Ioo_of_continuous (cb2.mul cg)
  have i3 : IntegrableOn (fun y => normalizedFunction 1 n y * normalizedFunction m j y)
      (Ioo 0 Real.pi) := integrableOn_Ioo_of_continuous (cb.mul cg)
  have hbg : ∫ y in Ioo 0 Real.pi, normalizedFunction 1 n y * deriv (deriv (normalizedFunction m j)) y =
      ∫ y in Ioo 0 Real.pi, deriv (deriv (normalizedFunction 1 n)) y * normalizedFunction m j y := by
    rw [← sub_eq_zero, ← integral_sub i1 i2]
    exact hG
  have hb2 : ∫ y in Ioo 0 Real.pi, deriv (deriv (normalizedFunction 1 n)) y * normalizedFunction m j y =
      (- eigenvalue 1 n) * ∫ y in Ioo 0 Real.pi, normalizedFunction 1 n y * normalizedFunction m j y := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro y hy
    simp only
    rw [sine_second n hy]
    ring
  have hsplit : ∫ y in Ioo 0 Real.pi, normalizedFunction 1 n y * omegaFn m j y =
      (eigenvalue m j - cc m) * (∫ y in Ioo 0 Real.pi, normalizedFunction 1 n y * normalizedFunction m j y) +
      ∫ y in Ioo 0 Real.pi, normalizedFunction 1 n y * deriv (deriv (normalizedFunction m j)) y := by
    symm
    rw [← integral_const_mul, ← integral_add (i3.const_mul _) i1]
    apply integral_congr_ae
    filter_upwards [] with y
    simp only [omegaFn]
    ring
  linarith [hsplit, hbg, hb2]

/-! ### The key identity -/

theorem key_identity {m : ℕ} (hm : 0 < m) {μ : ℝ} (hμ : 0 < μ) (j : ℕ) :
    S (μ + cc m) ((eigenvalue m j + μ) • normalizedVector m j - omegaL m j) =
      normalizedVector m j := by
  have hc := cc_nonneg hm
  apply dg_ext (hilbertBasis (one_pos : 0 < 1))
  intro n
  rw [repr_S (by linarith), repr_basis one_pos, repr_basis one_pos, inner_sub_right,
    inner_smul_right, inner_basis_of_ae 1 n _ _ (omegaL_ae m j), integral_b_omega hm,
    ← inner_basis_phi]
  have h1 := eigenvalue_nonneg' 1 n
  have h2 : 0 < eigenvalue 1 n + (μ + cc m) := by linarith
  field_simp
  ring

end BecknerOnofri.V2.Reaudit.HeatKernel.Engine
