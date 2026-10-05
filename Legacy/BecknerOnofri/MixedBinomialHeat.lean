module

public import Legacy.BecknerOnofri.GaussianMellin
public import Legacy.D10.BinomialCorrelated
public import Mathlib.Analysis.MeanInequalities

@[expose] public section

/-! The pointwise heat-polynomial comparison for arbitrary mixed degrees. -/
open scoped BigOperators
namespace Legacy.BecknerOnofri.MixedBinomialComparison
open Legacy.TorusEndpoint GaussianLattice ThetaDomination

/-- AM-GM on the d nonnegative heat factors, including zero factors. -/
theorem product_le_average_powers {d : ℕ} (hd : 0 < d) (b : Fin d → ℝ)
    (hb : ∀ i, 0 ≤ b i) :
    (∏ i, b i) ≤ (1/(d:ℝ)) * ∑ i, (b i)^d := by
  have hd' : (d:ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hd)
  have hw : (∑ _i : Fin d, 1/(d:ℝ)) = 1 := by
    simp [hd']
  have h := Real.geom_mean_le_arith_mean_weighted Finset.univ
    (fun _i : Fin d => 1/(d:ℝ)) (fun i => (b i)^d)
    (fun _ _ => by positivity) hw (fun i _ => pow_nonneg (hb i) d)
  have hp (i : Fin d) : ((b i)^d : ℝ)^(1/(d:ℝ)) = b i := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (hb i)]
    rw [mul_one_div_cancel hd', Real.rpow_one]
  simpa only [hp, ← Finset.mul_sum] using h

/-- Finite support of one coordinate's unsquared binomial coefficients. -/
theorem summable_weighted_binomialZ (n : ℕ) (w : ℤ → ℝ) :
    Summable (fun j : ℤ => w j * binomialZ n j) := by
  classical
  apply summable_of_ne_finset_zero (s := Finset.Icc (-(n:ℤ)) (n:ℤ))
  intro j hj
  have hn : n < j.natAbs := by
    simp only [Finset.mem_Icc] at hj
    omega
  simp [binomialZ, Legacy.D10.binomialCoeffReal, Legacy.D10.binomialCoeff_eq_zero hn]

noncomputable def heat (n : ℕ) (t : ℝ) : ℝ :=
  ∑' j : ℤ, binomialZ n j * Real.exp (-t*(j:ℝ)^2)

theorem heat_nonneg (n : ℕ) (t : ℝ) : 0 ≤ heat n t :=
  tsum_nonneg (fun j => mul_nonneg (binomialZ_nonneg n j) (Real.exp_pos _).le)

theorem summable_heat (n : ℕ) (t : ℝ) :
    Summable (fun j : ℤ => binomialZ n j * Real.exp (-t*(j:ℝ)^2)) := by
  simpa only [mul_comm] using summable_weighted_binomialZ n
    (fun j : ℤ => Real.exp (-t*(j:ℝ)^2))

/-- Exact full-lattice factorization, with the zero frequency still included. -/
theorem tsum_mixed_heat {d : ℕ} (N : Fin d → ℕ) (t : ℝ) :
    (∑' k : Frequency d,
      Legacy.D10.binomialProduct N (fun i => (k i).natAbs) * gaussian t k) =
        ∏ i, heat (N i) t := by
  have hnorm (i : Fin d) :
      Summable (fun j : ℤ => ‖((binomialZ (N i) j * Real.exp (-t*(j:ℝ)^2) : ℝ) : ℂ)‖) := by
    simpa only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (binomialZ_nonneg (N i) _) (Real.exp_pos _).le)] using
      summable_heat (N i) t
  have hc := TorusHeatPositivity.finite_product_tsum d
    (fun i j => ((binomialZ (N i) j * Real.exp (-t*(j:ℝ)^2) : ℝ) : ℂ)) hnorm
  simp only [← Complex.ofReal_prod, ← Complex.ofReal_tsum] at hc
  have hr := congrArg Complex.re hc
  simp only [Complex.ofReal_re] at hr
  simpa only [Legacy.D10.binomialProduct, gaussian_eq_product, Finset.prod_mul_distrib,
    binomialZ, heat] using hr

theorem mixed_heat_le {d : ℕ} (hd : 0 < d) (N : Fin d → ℕ) (t : ℝ) :
    (∏ i, heat (N i) t) - 1 ≤
      (1/(d:ℝ)) * ∑ i, ((heat (N i) t)^d - 1) := by
  have h := product_le_average_powers hd (fun i => heat (N i) t)
    (fun i => heat_nonneg (N i) t)
  have hd' : (d:ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hd)
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  rw [mul_sub, one_div_mul_cancel hd']
  linarith

#print axioms mixed_heat_le
#print axioms tsum_mixed_heat
end Legacy.BecknerOnofri.MixedBinomialComparison
