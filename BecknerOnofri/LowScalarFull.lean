import BecknerOnofri.LowScalarDefinitions
import Legacy.BecknerOnofri.GaussianScalarTwo

/-! Exact source-facing Section 3 identities, including the infinite harmonic
sum and the whole d=2,...,10 scalar range. No finite cutoff is a premise. -/
noncomputable section
open scoped BigOperators
namespace BecknerOnofri.HighDim.LowScalar
open Legacy.BecknerOnofri

lemma energy_eq_legacy (d n : ℕ) : energy d n = GaussianLattice.binomialEnergy d n := by
  apply tsum_congr
  intro k
  unfold GaussianLattice.binomialTerm GaussianLattice.binomialProduct
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  exact (Legacy.D10.binomialCoeffReal_formula n (k i).natAbs).symm

lemma harmonic_eq (n : ℕ) : Legacy.D10.FiniteScalar.harmonic n = _root_.harmonic n := by
  unfold Legacy.D10.FiniteScalar.harmonic _root_.harmonic
  have h := List.sum_toFinset (fun j : ℕ => (1 : ℚ) / ((j : ℚ)+1))
    (List.nodup_range (n := n))
  have hr : (List.range n).toFinset = Finset.range n := by ext k; simp
  simpa [hr, Nat.cast_add, Nat.cast_one] using h.symm

theorem scalar_gap (d n : ℕ) (hd2 : 2 ≤ d) (hd10 : d ≤ 10) (hn : 1 ≤ n) :
    (3/1100 : ℝ) < (d:ℝ)*(_root_.harmonic n:ℝ) -
      (2*(d:ℝ)/spectralThreshold d)*energy d n := by
  rw [energy_eq_legacy,← harmonic_eq]
  have he : 2*(d:ℝ)/spectralThreshold d = 2*endpointConstant d := by
    unfold endpointConstant spectralThreshold Legacy.TorusEndpoint.endpointSigma
    ring
  rw [he]
  by_cases hd : d = 2
  · subst d
    simpa using GaussianScalarTwo.all_indices_lattice_gap hn
  · exact GaussianScalarTail.all_indices_lattice_gap (by omega) hd10 hn

lemma weight_eq (n m l : ℕ) : mixingWeight n m l = Legacy.D10.hypergeometricWeightReal n m l := by
  simp [mixingWeight,Legacy.D10.hypergeometricWeightReal,Legacy.D10.hypergeometricWeight]

theorem hypergeometric_identity (n m : ℕ) :
    (∀ l, 0 ≤ mixingWeight n m l) ∧
    (∑ l ∈ Finset.range (n+1), mixingWeight n m l) = 1 ∧
    (∀ l, min n m < l → mixingWeight n m l = 0) ∧
    ∀ j : ℤ, EntropyTail.scalarCoefficient n j.natAbs * EntropyTail.scalarCoefficient m j.natAbs =
      ∑ l ∈ Finset.range (n+1), mixingWeight n m l * EntropyTail.scalarCoefficient l j.natAbs := by
  refine ⟨fun l => ?_, ?_, ?_, ?_⟩
  · rw [weight_eq]
    exact Legacy.D10.hypergeometricWeightReal_nonneg n m l
  · simp only [weight_eq]
    exact Legacy.D10.sum_hypergeometricWeightReal n m
  · intro l hl
    rcases min_lt_iff.mp hl with h | h
    · simp [mixingWeight,Nat.choose_eq_zero_of_lt (by omega : n < l)]
    · simp [mixingWeight,Nat.choose_eq_zero_of_lt (by omega : m < l)]
  · intro j
    simp only [weight_eq]
    simpa only [Legacy.D10.binomialCoeffReal_formula,EntropyTail.scalarCoefficient] using
      (Legacy.D10.hypergeometric_product_real n m j.natAbs).symm

theorem harmonic_identity (n : ℕ) :
    HasSum (fun j : ℕ => EntropyTail.scalarCoefficient n (j+1)/(j+1:ℝ))
      ((_root_.harmonic n:ℝ)/2) := by
  have he := Legacy.D10.binomialCoeffReal_harmonic n
  simp only [Legacy.D10.binomialCoeffReal_formula] at he
  rw [Finset.sum_range_succ'] at he
  simp only [Nat.cast_zero,div_zero,add_zero,Nat.cast_add,Nat.cast_one] at he
  have hH : (∑ k ∈ Finset.range n, (k+1:ℝ)⁻¹) = (_root_.harmonic n:ℝ) := by
    simp [_root_.harmonic]
  rw [hH] at he
  have hs : HasSum (fun j : ℕ => EntropyTail.scalarCoefficient n (j+1)/(j+1:ℝ))
      (∑ j ∈ Finset.range n, EntropyTail.scalarCoefficient n (j+1)/(j+1:ℝ)) := by
    apply hasSum_sum_of_ne_finset_zero
    intro j hj
    have hjn : n < j+1 := by simpa using (Nat.lt_succ_of_le (Nat.le_of_not_gt (by simpa using hj)))
    simp [EntropyTail.scalarCoefficient,Nat.choose_eq_zero_of_lt (by omega : 2*n<n+(j+1))]
  convert! hs using 1
  simp only [EntropyTail.scalarCoefficient]
  linarith

theorem theta_integral_ten : thetaIntegral 10 < (41/25 : ℝ) :=
  Legacy.BecknerOnofri.ThetaBound.realThetaIntegral_ten_lt

theorem theta_dimension_bound (d : ℕ) (hd : 0 < d) (hd10 : d ≤ 10) :
    thetaIntegral d < (d:ℝ)/10*(41/25 : ℝ) :=
  Legacy.BecknerOnofri.ThetaBound.realThetaIntegral_lt hd hd10

#print axioms theta_integral_ten
#print axioms theta_dimension_bound
#print axioms scalar_gap
#print axioms hypergeometric_identity
#print axioms harmonic_identity
end BecknerOnofri.HighDim.LowScalar
