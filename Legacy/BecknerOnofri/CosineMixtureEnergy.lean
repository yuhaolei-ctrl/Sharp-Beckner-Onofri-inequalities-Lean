import Legacy.BecknerOnofri.CosineMixture
import Legacy.BecknerOnofri.LatticePolynomialBridge
import Legacy.BecknerOnofri.Endpoint

/-! Full lattice energies for mixed-index cosine components and their actual
finite correlated mixtures. Summability is proved from finite Fourier support. -/

noncomputable section
open Finset MeasureTheory Legacy.TorusEndpoint

namespace Legacy.BecknerOnofri.CosineMixtureEnergy

def componentCoeff {d : ℕ} (N : Fin d → ℕ) (k : Frequency d) : ℝ :=
  Legacy.D10.binomialProduct N (fun i => (k i).natAbs)

def componentTerm {d : ℕ} (N : Fin d → ℕ) (k : Frequency d) : ℝ :=
  GaussianLattice.spectralWeight k * componentCoeff N k

def componentEnergy {d : ℕ} (N : Fin d → ℕ) : ℝ := ∑' k, componentTerm N k

theorem componentCoeff_nonneg {d : ℕ} (N : Fin d → ℕ) (k : Frequency d) :
    0 ≤ componentCoeff N k := by
  unfold componentCoeff Legacy.D10.binomialProduct
  exact Finset.prod_nonneg (fun i _ => GaussianLattice.binomialZ_nonneg (N i) (k i))

theorem componentCoeff_eq_zero_outside {d : ℕ} (N : Fin d → ℕ) (k : Frequency d)
    (hk : k ∉ LatticePolynomial.latticeBox d (∑ i, N i)) : componentCoeff N k = 0 := by
  classical
  rw [LatticePolynomial.mem_latticeBox] at hk
  push Not at hk
  obtain ⟨i, hi⟩ := hk
  have hNi : N i ≤ ∑ j, N j := single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ i)
  apply Finset.prod_eq_zero (mem_univ i)
  simp only [Legacy.D10.binomialCoeffReal,
    Legacy.D10.binomialCoeff_eq_zero (lt_of_le_of_lt hNi hi), Rat.cast_zero]

theorem summable_weighted_component {d : ℕ} (N : Fin d → ℕ) (w : Frequency d → ℝ) :
    Summable (fun k => w k * componentCoeff N k) := by
  apply summable_of_ne_finset_zero (s := LatticePolynomial.latticeBox d (∑ i, N i))
  intro k hk
  rw [componentCoeff_eq_zero_outside N k hk, mul_zero]

theorem summable_componentCoeff {d : ℕ} (N : Fin d → ℕ) : Summable (componentCoeff N) := by
  simpa using summable_weighted_component N (fun _ => 1)

theorem summable_componentTerm {d : ℕ} (N : Fin d → ℕ) : Summable (componentTerm N) :=
  summable_weighted_component N GaussianLattice.spectralWeight

theorem componentEnergy_diagonal (d n : ℕ) :
    componentEnergy (fun _ : Fin d => n) = GaussianLattice.binomialEnergy d n := rfl

theorem spectralWeight_nonzero {d : ℕ} (k : NonzeroFrequency d) :
    GaussianLattice.spectralWeight k.val = 1 / frequencyRadius k.val ^ d := by
  rw [GaussianLattice.spectralWeight, if_neg k.property]
  congr 1
  unfold frequencyRadius
  have hr : 0 ≤ GreenMultiplierSummability.radiusSq k.val :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  change Real.sqrt (GreenMultiplierSummability.radiusSq k.val ^ d) =
    Real.sqrt (GreenMultiplierSummability.radiusSq k.val) ^ d
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (pow_nonneg (Real.sqrt_nonneg _) _)).mp
  rw [Real.sq_sqrt (pow_nonneg hr _), pow_right_comm, Real.sq_sqrt hr]

variable {α : Type*} {d : ℕ}

def latentTerm (s : Finset α) (w : α → ℝ) (N : α → Fin d → ℕ) (k : Frequency d) : ℝ :=
  ∑ a ∈ s, ∑ b ∈ s, ∑ L ∈ Legacy.D10.latentBox (N a),
    w a * w b * Legacy.D10.latentWeight (N a) (N b) L * componentTerm L k

theorem weighted_mixture_eq_latentTerm (s : Finset α) (w : α → ℝ)
    (N : α → Fin d → ℕ) (k : Frequency d) :
    GaussianLattice.spectralWeight k *
      ‖densityFourier (CosineMixture.mixture s w N) k‖ ^ 2 = latentTerm s w N k := by
  rw [CosineMixture.mixture_fourier_norm_sq]
  unfold latentTerm componentTerm componentCoeff
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro L hL
  ring

theorem summable_latentTerm (s : Finset α) (w : α → ℝ) (N : α → Fin d → ℕ) :
    Summable (latentTerm s w N) := by
  unfold latentTerm
  apply summable_sum
  intro a ha
  apply summable_sum
  intro b hb
  apply summable_sum
  intro L hL
  exact (summable_componentTerm L).mul_left _

theorem tsum_latentTerm (s : Finset α) (w : α → ℝ) (N : α → Fin d → ℕ) :
    ∑' k, latentTerm s w N k =
      ∑ a ∈ s, ∑ b ∈ s, ∑ L ∈ Legacy.D10.latentBox (N a),
        w a * w b * Legacy.D10.latentWeight (N a) (N b) L * componentEnergy L := by
  unfold latentTerm componentEnergy
  rw [Summable.tsum_finsetSum]
  · apply Finset.sum_congr rfl
    intro a ha
    rw [Summable.tsum_finsetSum]
    · apply Finset.sum_congr rfl
      intro b hb
      rw [Summable.tsum_finsetSum]
      · simp_rw [tsum_mul_left]
      · intro L hL
        exact (summable_componentTerm L).mul_left _
    · intro b hb
      exact summable_sum (fun L hL => (summable_componentTerm L).mul_left _)
  · intro a ha
    exact summable_sum (fun b hb =>
      summable_sum (fun L hL => (summable_componentTerm L).mul_left _))

theorem spectralTerm_eq_latentTerm (s : Finset α) (w : α → ℝ) (N : α → Fin d → ℕ)
    (hw : ∀ a ∈ s, 0 ≤ w a) (hm : ∑ a ∈ s, w a = 1) (k : NonzeroFrequency d) :
    densitySpectralTerm (CosineMixture.density s w N hw hm) k = latentTerm s w N k.val := by
  rw [← weighted_mixture_eq_latentTerm, spectralWeight_nonzero]
  simp [densitySpectralTerm, CosineMixture.density, div_eq_mul_inv, mul_comm]

theorem spectral_summable (s : Finset α) (w : α → ℝ) (N : α → Fin d → ℕ)
    (hw : ∀ a ∈ s, 0 ≤ w a) (hm : ∑ a ∈ s, w a = 1) :
    Summable (densitySpectralTerm (CosineMixture.density s w N hw hm)) := by
  exact ((summable_latentTerm s w N).subtype (fun k => k ≠ 0)).congr
    (fun k => (spectralTerm_eq_latentTerm s w N hw hm k).symm)

theorem fourierEnergy_eq_latent (s : Finset α) (w : α → ℝ) (N : α → Fin d → ℕ)
    (hw : ∀ a ∈ s, 0 ≤ w a) (hm : ∑ a ∈ s, w a = 1) :
    fourierEnergy (CosineMixture.density s w N hw hm) =
      ∑ a ∈ s, ∑ b ∈ s, ∑ L ∈ Legacy.D10.latentBox (N a),
        w a * w b * Legacy.D10.latentWeight (N a) (N b) L * componentEnergy L := by
  unfold fourierEnergy
  simp_rw [spectralTerm_eq_latentTerm]
  have hs : Function.support (latentTerm s w N) ⊆ {k | k ≠ 0} := by
    intro k hk
    change k ≠ 0
    intro hzero
    subst k
    have hz : latentTerm s w N 0 = 0 := by
      rw [← weighted_mixture_eq_latentTerm]
      simp [GaussianLattice.spectralWeight]
    exact hk hz
  exact (tsum_subtype_eq_of_support_subset hs).trans (tsum_latentTerm s w N)

end Legacy.BecknerOnofri.CosineMixtureEnergy
