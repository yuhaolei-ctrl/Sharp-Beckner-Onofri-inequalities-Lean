import Legacy.D10.GaussianMajorantReal
import Legacy.TorusEndpoint.TorusHeatBounds
import Legacy.BecknerOnofri.ThetaDomination

/-! The binomial-to-Gaussian comparison on the actual integer lattice.
The sums have their zero mode explicitly removed. Their summability is
proved before comparing their values. -/

open scoped BigOperators

namespace Legacy.BecknerOnofri.GaussianLattice
open Legacy.TorusEndpoint Legacy.TorusEndpoint.GreenMultiplierSummability

/-- The even binomial coefficient at an integer frequency. -/
noncomputable def binomialZ (n : ℕ) (j : ℤ) : ℝ :=
  Legacy.D10.binomialCoeffReal n j.natAbs

theorem binomialZ_nonneg (n : ℕ) (j : ℤ) : 0 ≤ binomialZ n j := by
  simpa only [Rat.cast_zero, binomialZ, Legacy.D10.binomialCoeffReal] using
    (Rat.cast_le (K := ℝ)).mpr (Legacy.D10.binomialCoeff_nonneg n j.natAbs)

theorem binomialZ_gaussian (n : ℕ) (hn : 0 < n) (j : ℤ) :
    binomialZ n j ≤ Real.exp (-Real.log (1+1/(n : ℝ)) * (j : ℝ)^2) := by
  have habs : (j.natAbs : ℝ)^2 = (j : ℝ)^2 := by
    have h := Int.natCast_natAbs j
    have hr := congrArg (fun z : ℤ => (z : ℝ)) h
    simp only [Int.cast_natCast, Int.cast_abs] at hr
    rw [hr, sq_abs]
  simpa only [binomialZ, habs] using Legacy.D10.binomialCoeffReal_gaussian n j.natAbs hn

noncomputable def gaussian {d : ℕ} (a : ℝ) (k : Frequency d) : ℝ :=
  Real.exp (-a * radiusSq k)

noncomputable def binomialProduct {d : ℕ} (n : ℕ) (k : Frequency d) : ℝ :=
  ∏ i, binomialZ n (k i)

theorem binomialProduct_gaussian {d n : ℕ} (hn : 0 < n) (k : Frequency d) :
    binomialProduct n k ≤ gaussian (Real.log (1+1/(n : ℝ))) k := by
  unfold binomialProduct gaussian radiusSq
  rw [Finset.mul_sum, Real.exp_sum]
  exact Finset.prod_le_prod (fun i _ => binomialZ_nonneg n (k i))
    (fun i _ => binomialZ_gaussian n hn (k i))

theorem summable_gaussian {d : ℕ} {a : ℝ} (ha : 0 < a) :
    Summable (gaussian a : Frequency d → ℝ) := by
  have he : (gaussian a : Frequency d → ℝ) =
      TorusHeatBounds.heatWeight (a/Real.pi) := by
    funext k
    unfold gaussian TorusHeatBounds.heatWeight
    congr 1
    field_simp
  rw [he]
  exact TorusHeatBounds.heatWeight_summable (div_pos ha Real.pi_pos)

/-- `|k|⁻ᵈ`, with zero at the removed zero mode. -/
noncomputable def spectralWeight {d : ℕ} (k : Frequency d) : ℝ :=
  if k = 0 then 0 else 1 / Real.sqrt (radiusSq k ^ d)

theorem spectralWeight_nonneg {d : ℕ} (k : Frequency d) : 0 ≤ spectralWeight k := by
  unfold spectralWeight
  split_ifs <;> positivity

theorem spectralWeight_le_one {d : ℕ} (k : Frequency d) : spectralWeight k ≤ 1 := by
  unfold spectralWeight
  split_ifs with hk
  · norm_num
  · have hp : 1 ≤ radiusSq k ^ d := one_le_pow₀ (radiusSq_one_le hk)
    have hs : 1 ≤ Real.sqrt (radiusSq k ^ d) := by
      simpa using Real.sqrt_le_sqrt hp
    exact (div_le_one (by linarith : 0 < Real.sqrt (radiusSq k ^ d))).mpr hs

noncomputable def gaussianTerm {d : ℕ} (a : ℝ) (k : Frequency d) : ℝ :=
  spectralWeight k * gaussian a k

noncomputable def binomialTerm {d : ℕ} (n : ℕ) (k : Frequency d) : ℝ :=
  spectralWeight k * binomialProduct n k

theorem summable_gaussianTerm {d : ℕ} {a : ℝ} (ha : 0 < a) :
    Summable (gaussianTerm a : Frequency d → ℝ) := by
  refine Summable.of_nonneg_of_le
    (fun k => mul_nonneg (spectralWeight_nonneg k) (Real.exp_pos _).le) ?_
    (summable_gaussian ha)
  intro k
  exact mul_le_of_le_one_left (Real.exp_pos _).le (spectralWeight_le_one k)

theorem binomialTerm_le_gaussianTerm {d n : ℕ} (hn : 0 < n) (k : Frequency d) :
    binomialTerm n k ≤ gaussianTerm (Real.log (1+1/(n : ℝ))) k :=
  mul_le_mul_of_nonneg_left (binomialProduct_gaussian hn k) (spectralWeight_nonneg k)

theorem log_parameter_pos {n : ℕ} (hn : 0 < n) :
    0 < Real.log (1+1/(n : ℝ)) := by
  apply Real.log_pos
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have h : 0 < 1/(n : ℝ) := by positivity
  linarith

theorem summable_binomialTerm {d n : ℕ} (hn : 0 < n) :
    Summable (binomialTerm n : Frequency d → ℝ) := by
  refine Summable.of_nonneg_of_le ?_ (binomialTerm_le_gaussianTerm hn)
    (summable_gaussianTerm (log_parameter_pos hn))
  intro k
  exact mul_nonneg (spectralWeight_nonneg k)
    (Finset.prod_nonneg (fun i _ => binomialZ_nonneg n (k i)))

/-- The manuscript's unsquared-coefficient sum, on the actual lattice. -/
noncomputable def binomialEnergy (d n : ℕ) : ℝ :=
  ∑' k : Frequency d, binomialTerm n k

noncomputable def gaussianEnergy (d : ℕ) (a : ℝ) : ℝ :=
  ∑' k : Frequency d, gaussianTerm a k

/-- The first analytic inequality of the common Gaussian argument. -/
theorem binomialEnergy_le_gaussianEnergy {d n : ℕ} (hn : 0 < n) :
    binomialEnergy d n ≤ gaussianEnergy d (Real.log (1+1/(n : ℝ))) :=
  (summable_binomialTerm hn).tsum_le_tsum (binomialTerm_le_gaussianTerm hn)
    (summable_gaussianTerm (log_parameter_pos hn))

#print axioms binomialEnergy_le_gaussianEnergy
end Legacy.BecknerOnofri.GaussianLattice
