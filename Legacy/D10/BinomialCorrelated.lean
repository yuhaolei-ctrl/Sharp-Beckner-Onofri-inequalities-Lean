import Legacy.D10.BinomialReal

/-!
# Exact finite correlated-mixture identities

The component indices are arbitrary functions of a common latent sample; no
independence of the coordinates is assumed. Two latent samples are weighted
independently. All sums below are finite and are identities over `ℝ`.
-/

namespace Legacy.D10

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def binomialProduct (N k : ι → ℕ) : ℝ :=
  ∏ i, binomialCoeffReal (N i) (k i)

def latentBox (N : ι → ℕ) : Finset (ι → ℕ) :=
  Fintype.piFinset (fun i => range (N i + 1))

def latentWeight (N M L : ι → ℕ) : ℝ :=
  ∏ i, hypergeometricWeightReal (N i) (M i) (L i)

omit [DecidableEq ι] in
lemma latentWeight_nonneg (N M L : ι → ℕ) : 0 ≤ latentWeight N M L := by
  apply Finset.prod_nonneg
  intro i hi
  exact hypergeometricWeightReal_nonneg _ _ _

theorem sum_latentWeight (N M : ι → ℕ) :
    ∑ L ∈ latentBox N, latentWeight N M L = 1 := by
  unfold latentBox latentWeight
  rw [← Finset.prod_univ_sum]
  simp only [sum_hypergeometricWeightReal, Finset.prod_const_one]

/-- The coordinatewise hypergeometric average reproduces the product of the
two tensor component coefficients. -/
theorem latent_product (N M k : ι → ℕ) :
    (∑ L ∈ latentBox N, latentWeight N M L * binomialProduct L k) =
      binomialProduct N k * binomialProduct M k := by
  unfold latentBox latentWeight binomialProduct
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Finset.prod_univ_sum (fun i => range (N i + 1))
    (fun i l => hypergeometricWeightReal (N i) (M i) l * binomialCoeffReal l (k i))]
  simp only [hypergeometric_product_real]

variable {α β : Type*}

/-- Two arbitrary weighted finite correlated mixtures satisfy the exact latent
coefficient product identity. This algebraic statement needs no sign or
normalization assumptions on the two outer weights. -/
theorem correlated_mixture_product (s : Finset α) (t : Finset β)
    (w : α → ℝ) (v : β → ℝ) (N : α → ι → ℕ) (M : β → ι → ℕ) (k : ι → ℕ) :
    (∑ a ∈ s, w a * binomialProduct (N a) k) *
        (∑ b ∈ t, v b * binomialProduct (M b) k) =
      ∑ a ∈ s, ∑ b ∈ t, w a * v b *
        (∑ L ∈ latentBox (N a), latentWeight (N a) (M b) L * binomialProduct L k) := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  rw [latent_product]
  ring

/-- The actual coefficient of a finite correlated mixture is squared by taking
two independent copies of its full latent index. -/
theorem correlated_mixture_square (s : Finset α) (w : α → ℝ)
    (N : α → ι → ℕ) (k : ι → ℕ) :
    (∑ a ∈ s, w a * binomialProduct (N a) k)^2 =
      ∑ a ∈ s, ∑ b ∈ s, w a * w b *
        (∑ L ∈ latentBox (N a), latentWeight (N a) (N b) L * binomialProduct L k) := by
  rw [pow_two]
  exact correlated_mixture_product s s w w N N k

/-- Every finite weighted Fourier energy of the actual mixture is exactly the
latent average of the unsquared component coefficient sum. The finite kernel
weights are arbitrary; no positivity relaxation is used in this identity. -/
theorem correlated_finite_energy (s : Finset α) (w : α → ℝ)
    (N : α → ι → ℕ) (K : Finset (ι → ℕ)) (γ : (ι → ℕ) → ℝ) :
    (∑ k ∈ K, γ k * (∑ a ∈ s, w a * binomialProduct (N a) k)^2) =
      ∑ a ∈ s, ∑ b ∈ s, w a * w b *
        (∑ L ∈ latentBox (N a), latentWeight (N a) (N b) L *
          (∑ k ∈ K, γ k * binomialProduct L k)) := by
  simp_rw [correlated_mixture_square, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro L hL
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- If both outer laws have unit mass, the full joint latent law has unit mass. -/
theorem correlated_latent_mass (s : Finset α) (t : Finset β)
    (w : α → ℝ) (v : β → ℝ) (N : α → ι → ℕ) (M : β → ι → ℕ)
    (hw : ∑ a ∈ s, w a = 1) (hv : ∑ b ∈ t, v b = 1) :
    (∑ a ∈ s, ∑ b ∈ t, ∑ L ∈ latentBox (N a),
      w a * v b * latentWeight (N a) (M b) L) = 1 := by
  simp_rw [← Finset.mul_sum, sum_latentWeight, mul_one]
  simp_rw [← Finset.mul_sum, hv, mul_one]
  exact hw

omit [DecidableEq ι] in
lemma correlated_latent_nonneg (w : α → ℝ) (v : β → ℝ)
    (N : α → ι → ℕ) (M : β → ι → ℕ) (a : α) (b : β) (L : ι → ℕ)
    (hw : 0 ≤ w a) (hv : 0 ≤ v b) :
    0 ≤ w a * v b * latentWeight (N a) (M b) L :=
  mul_nonneg (mul_nonneg hw hv) (latentWeight_nonneg _ _ _)

end Legacy.D10
