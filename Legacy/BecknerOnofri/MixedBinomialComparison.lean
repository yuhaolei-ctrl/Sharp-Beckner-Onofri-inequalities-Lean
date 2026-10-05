import Legacy.BecknerOnofri.MixedBinomialHeat
import Legacy.BecknerOnofri.CosineMixtureEnergy

/-! Mixed binomial lattice energies are bounded by the average of their
isotropic diagonal energies. Every coefficient occurs to the first power.
The normalized Mellin integrals are integrable because the Fourier support
is finite, including when some or all component degrees vanish. -/
open scoped BigOperators
namespace Legacy.BecknerOnofri.MixedBinomialComparison
open MeasureTheory Set Legacy.TorusEndpoint GaussianLattice CosineMixtureEnergy

noncomputable def componentIntegrand {d : ℕ} (N : Fin d → ℕ) (t : ℝ) : ℝ :=
  t^((d:ℝ)/2-1) / Real.Gamma ((d:ℝ)/2) * ((∏ i, heat (N i) t)-1)

theorem tsum_mixed_nonzero_heat {d : ℕ} (N : Fin d → ℕ) (t : ℝ) :
    (∑' k : Frequency d, componentCoeff N k * nonzeroGaussian t k) =
      (∏ i, heat (N i) t)-1 := by
  have hs : Summable (fun k : Frequency d => componentCoeff N k * gaussian t k) := by
    simpa only [mul_comm] using summable_weighted_component N (gaussian t)
  have h := hs.tsum_eq_add_tsum_ite (0 : Frequency d)
  rw [show (∑' k : Frequency d, componentCoeff N k * gaussian t k) =
      ∏ i, heat (N i) t from tsum_mixed_heat N t] at h
  have hz : componentCoeff N (0 : Frequency d) * gaussian t (0 : Frequency d) = 1 := by
    simp [componentCoeff, Legacy.D10.binomialProduct, Legacy.D10.binomialCoeffReal]
  rw [hz] at h
  have he (k : Frequency d) : componentCoeff N k * nonzeroGaussian t k =
      if k = 0 then 0 else componentCoeff N k * gaussian t k := by
    unfold nonzeroGaussian
    split_ifs <;> simp
  simp_rw [he]
  linarith

/-- Pointwise identification of the normalized finite Mellin sum. -/
theorem tsum_component_mellin {d : ℕ} (N : Fin d → ℕ) (t : ℝ) :
    (∑' k : Frequency d, componentCoeff N k * mellinTerm 0 k t) =
      componentIntegrand N t := by
  unfold componentIntegrand mellinTerm
  simp only [sub_zero]
  calc
    _ = t^((d:ℝ)/2-1) / Real.Gamma ((d:ℝ)/2) *
        ∑' k : Frequency d, componentCoeff N k * nonzeroGaussian t k := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro k
      ring
    _ = _ := by rw [tsum_mixed_nonzero_heat]

/-- A finite sum representation valid for every real t, with no convergence convention hidden. -/
theorem componentIntegrand_eq_sum {d : ℕ} (N : Fin d → ℕ) (t : ℝ) :
    componentIntegrand N t =
      ∑ k ∈ LatticePolynomial.latticeBox d (∑ i, N i),
        componentCoeff N k * mellinTerm 0 k t := by
  rw [← tsum_component_mellin]
  apply tsum_eq_sum
  intro k hk
  rw [componentCoeff_eq_zero_outside N k hk, zero_mul]

theorem componentIntegrand_integrable {d : ℕ} (hd : 0 < d) (N : Fin d → ℕ) :
    IntegrableOn (componentIntegrand N) (Ioi 0) := by
  simp_rw [show componentIntegrand N = fun t =>
    ∑ k ∈ LatticePolynomial.latticeBox d (∑ i, N i),
      componentCoeff N k * mellinTerm 0 k t from funext (componentIntegrand_eq_sum N)]
  exact integrable_finsetSum _ (fun k _ => (mellinTerm_integrable hd 0 k).const_mul _)

theorem component_mellin_integral {d : ℕ} (hd : 0 < d) (N : Fin d → ℕ)
    (k : Frequency d) :
    (∫ t in Ioi 0, componentCoeff N k * mellinTerm 0 k t) = componentTerm N k := by
  rw [integral_const_mul, mellinTerm_integral hd 0]
  simp [gaussianTerm, gaussian, componentTerm, mul_comm]

/-- Exact Mellin representation of the complete mixed lattice energy. -/
theorem componentEnergy_mellin {d : ℕ} (hd : 0 < d) (N : Fin d → ℕ) :
    componentEnergy N = ∫ t in Ioi 0, componentIntegrand N t := by
  unfold componentEnergy
  rw [tsum_eq_sum (s := LatticePolynomial.latticeBox d (∑ i, N i))
    (fun k hk => by simp [componentTerm, componentCoeff_eq_zero_outside N k hk])]
  simp_rw [componentIntegrand_eq_sum]
  rw [integral_finsetSum _ (fun k _ => (mellinTerm_integrable hd 0 k).const_mul _)]
  apply Finset.sum_congr rfl
  intro k hk
  exact (component_mellin_integral hd N k).symm

theorem componentIntegrand_diagonal (d n : ℕ) (t : ℝ) :
    componentIntegrand (fun _ : Fin d => n) t =
      t^((d:ℝ)/2-1) / Real.Gamma ((d:ℝ)/2) * ((heat n t)^d-1) := by
  simp [componentIntegrand]

theorem componentIntegrand_le_diagonal {d : ℕ} (hd : 0 < d)
    (N : Fin d → ℕ) {t : ℝ} (ht : 0 < t) :
    componentIntegrand N t ≤
      (1/(d:ℝ)) * ∑ i, componentIntegrand (fun _ : Fin d => N i) t := by
  have hw : 0 ≤ t^((d:ℝ)/2-1) / Real.Gamma ((d:ℝ)/2) := by
    exact div_nonneg (Real.rpow_nonneg ht.le _)
      (Real.Gamma_pos_of_pos (div_pos (Nat.cast_pos.mpr hd) (by norm_num))).le
  have h := mul_le_mul_of_nonneg_left (mixed_heat_le hd N t) hw
  simp_rw [componentIntegrand_diagonal]
  rw [← Finset.mul_sum]
  simpa only [componentIntegrand, mul_assoc, mul_left_comm] using h

/-- The full mixed-index comparison, valid for all positive dimensions and all degrees. -/
theorem componentEnergy_le_average_diagonal {d : ℕ} (hd : 0 < d)
    (N : Fin d → ℕ) :
    componentEnergy N ≤ (1/(d:ℝ)) * ∑ i, binomialEnergy d (N i) := by
  have hi : IntegrableOn (fun t => (1/(d:ℝ)) *
      ∑ i, componentIntegrand (fun _ : Fin d => N i) t) (Ioi 0) :=
    (integrable_finsetSum Finset.univ
      (fun i _ => componentIntegrand_integrable hd (fun _ : Fin d => N i))).const_mul _
  rw [componentEnergy_mellin hd N]
  calc
    _ ≤ ∫ t in Ioi 0, (1/(d:ℝ)) *
        ∑ i, componentIntegrand (fun _ : Fin d => N i) t := by
      apply setIntegral_mono_on (componentIntegrand_integrable hd N) hi measurableSet_Ioi
      intro t ht
      exact componentIntegrand_le_diagonal hd N ht
    _ = _ := by
      rw [integral_const_mul, integral_finsetSum _
        (fun i _ => componentIntegrand_integrable hd (fun _ : Fin d => N i))]
      simp_rw [← componentEnergy_mellin hd, componentEnergy_diagonal]

#print axioms componentEnergy_mellin
#print axioms componentEnergy_le_average_diagonal
end Legacy.BecknerOnofri.MixedBinomialComparison
