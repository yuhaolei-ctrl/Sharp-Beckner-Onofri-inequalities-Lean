import Legacy.BecknerOnofri.CosineMixtureEnergy
import Legacy.BecknerOnofri.TorusMarginals
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-! The actual axis Fourier energy of a correlated cosine mixture equals
the latent expectation of the sum of harmonic numbers. -/

noncomputable section
open Finset Legacy.TorusEndpoint

namespace Legacy.BecknerOnofri.CosineMixtureAxis
open CosineMixtureEnergy TorusMarginals

def circleIntTerm (n : ℕ) (j : ℤ) : ℝ :=
  |(j : ℝ)|⁻¹ * Legacy.D10.binomialCoeffReal n j.natAbs

theorem summable_circleIntTerm (n : ℕ) : Summable (circleIntTerm n) := by
  apply summable_of_ne_finset_zero (s := Icc (-(n : ℤ)) (n : ℤ))
  intro j hj
  have hn : n < j.natAbs := by
    simp only [mem_Icc, not_and_or, not_le] at hj
    omega
  simp [circleIntTerm, Legacy.D10.binomialCoeffReal, Legacy.D10.binomialCoeff_eq_zero hn]

theorem circleIntTerm_nat (n j : ℕ) :
    circleIntTerm n j = Legacy.D10.binomialCoeffReal n j / j := by
  simp [circleIntTerm, div_eq_mul_inv, mul_comm]

theorem circleIntTerm_neg (n : ℕ) (j : ℤ) : circleIntTerm n (-j) = circleIntTerm n j := by
  simp [circleIntTerm]

theorem circleIntTerm_tsum (n : ℕ) :
    ∑' j : ℤ, circleIntTerm n j = (Legacy.D10.FiniteScalar.harmonic n : ℝ) := by
  have hn := (summable_circleIntTerm n).hasSum.nat_add_neg.tsum_eq
  simp only [circleIntTerm_neg, circleIntTerm_nat, ← two_mul] at hn
  have hzero : circleIntTerm n 0 = 0 := by simp [circleIntTerm]
  rw [hzero, add_zero, tsum_mul_left] at hn
  have hs : (∑' j : ℕ, Legacy.D10.binomialCoeffReal n j / (j : ℝ)) =
      ∑ j ∈ range (n+1), Legacy.D10.binomialCoeffReal n j / (j : ℝ) := by
    apply tsum_eq_sum
    intro j hj
    have hjn : n < j := by simp only [mem_range] at hj; omega
    simp [Legacy.D10.binomialCoeffReal, Legacy.D10.binomialCoeff_eq_zero hjn]
  rw [hs, Legacy.D10.binomialCoeffReal_harmonic] at hn
  rw [← hn]
  have h := List.sum_toFinset (fun j : ℕ => (1 : ℚ) / ((j : ℚ)+1))
    (List.nodup_range (n := n))
  have hr : (List.range n).toFinset = Finset.range n := by ext k; simp
  have hh : Legacy.D10.FiniteScalar.harmonic n = Legacy.D10.harmonicNumber n := by
    simpa [Legacy.D10.FiniteScalar.harmonic, Legacy.D10.harmonicNumber, hr, div_eq_mul_inv] using h.symm
  rw [hh]
  simp [Legacy.D10.harmonicNumber]

theorem componentCoeff_axis {d : ℕ} (N : Fin d → ℕ) (i : Fin d) (k : Frequency 1) :
    componentCoeff N (axisFrequency i k) = Legacy.D10.binomialCoeffReal (N i) (k 0).natAbs := by
  classical
  unfold componentCoeff Legacy.D10.binomialProduct axisFrequency
  rw [Finset.prod_eq_single i]
  · simp
  · intro j hj hji
    simp [Pi.single_eq_of_ne hji, Legacy.D10.binomialCoeffReal]
  · simp

def frequencyOneEquivInt : Frequency 1 ≃ ℤ where
  toFun k := k 0
  invFun j := fun _ => j
  left_inv k := by funext i; have hi : i = 0 := Subsingleton.elim _ _; simp [hi]
  right_inv j := rfl

def componentAxisTerm {d : ℕ} (N : Fin d → ℕ) (i : Fin d) (k : NonzeroFrequency 1) : ℝ :=
  Legacy.D10.CircleEntropy.weight k.val * componentCoeff N (axisFrequency i k.val)

theorem componentAxisTerm_eq {d : ℕ} (N : Fin d → ℕ) (i : Fin d) (k : NonzeroFrequency 1) :
    componentAxisTerm N i k = circleIntTerm (N i) (k.val 0) := by
  rw [componentAxisTerm, componentCoeff_axis]
  rfl

theorem summable_componentAxisTerm {d : ℕ} (N : Fin d → ℕ) (i : Fin d) :
    Summable (componentAxisTerm N i) := by
  have h : Summable (fun k : Frequency 1 => circleIntTerm (N i) (k 0)) :=
    frequencyOneEquivInt.summable_iff.mpr (summable_circleIntTerm (N i))
  exact (h.subtype (fun k => k ≠ 0)).congr (fun k => (componentAxisTerm_eq N i k).symm)

theorem componentAxisTerm_tsum {d : ℕ} (N : Fin d → ℕ) (i : Fin d) :
    ∑' k : NonzeroFrequency 1, componentAxisTerm N i k =
      (Legacy.D10.FiniteScalar.harmonic (N i) : ℝ) := by
  simp_rw [componentAxisTerm_eq]
  have hs : Function.support (fun k : Frequency 1 => circleIntTerm (N i) (k 0)) ⊆
      {k | k ≠ 0} := by
    intro k hk hz
    subst k
    exact hk (by simp [circleIntTerm])
  exact (tsum_subtype_eq_of_support_subset hs).trans
    ((frequencyOneEquivInt.tsum_eq (circleIntTerm (N i))).trans (circleIntTerm_tsum (N i)))

variable {α : Type*} {d : ℕ}

def latentAxisTerm (s : Finset α) (w : α → ℝ) (N : α → Fin d → ℕ)
    (i : Fin d) (k : NonzeroFrequency 1) : ℝ :=
  ∑ a ∈ s, ∑ b ∈ s, ∑ L ∈ Legacy.D10.latentBox (N a),
    w a * w b * Legacy.D10.latentWeight (N a) (N b) L * componentAxisTerm L i k

theorem mixture_axis_eq_latentTerm (s : Finset α) (w : α → ℝ)
    (N : α → Fin d → ℕ) (i : Fin d) (k : NonzeroFrequency 1) :
    Legacy.D10.CircleEntropy.weight k.val *
      ‖densityFourier (CosineMixture.mixture s w N) (axisFrequency i k.val)‖ ^ 2 =
        latentAxisTerm s w N i k := by
  rw [CosineMixture.mixture_fourier_norm_sq]
  unfold latentAxisTerm componentAxisTerm componentCoeff
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro L hL
  ring

theorem summable_latentAxisTerm (s : Finset α) (w : α → ℝ)
    (N : α → Fin d → ℕ) (i : Fin d) : Summable (latentAxisTerm s w N i) := by
  unfold latentAxisTerm
  exact summable_sum (fun a ha => summable_sum (fun b hb =>
    summable_sum (fun L hL => (summable_componentAxisTerm L i).mul_left _)))

theorem tsum_latentAxisTerm (s : Finset α) (w : α → ℝ)
    (N : α → Fin d → ℕ) (i : Fin d) :
    ∑' k, latentAxisTerm s w N i k =
      ∑ a ∈ s, ∑ b ∈ s, ∑ L ∈ Legacy.D10.latentBox (N a),
        w a * w b * Legacy.D10.latentWeight (N a) (N b) L * (Legacy.D10.FiniteScalar.harmonic (L i) : ℝ) := by
  unfold latentAxisTerm
  rw [Summable.tsum_finsetSum]
  · apply Finset.sum_congr rfl
    intro a ha
    rw [Summable.tsum_finsetSum]
    · apply Finset.sum_congr rfl
      intro b hb
      rw [Summable.tsum_finsetSum]
      · simp_rw [tsum_mul_left, componentAxisTerm_tsum]
      · intro L hL
        exact (summable_componentAxisTerm L i).mul_left _
    · intro b hb
      exact summable_sum (fun L hL => (summable_componentAxisTerm L i).mul_left _)
  · intro a ha
    exact summable_sum (fun b hb =>
      summable_sum (fun L hL => (summable_componentAxisTerm L i).mul_left _))

/-- Actual axis Fourier energy, with no sign or normalization hypotheses on
the finite coefficients, equals the latent harmonic-number expression. -/
theorem mixture_axis_sum_eq (s : Finset α) (w : α → ℝ) (N : α → Fin d → ℕ) :
    (∑ i, ∑' k : NonzeroFrequency 1, Legacy.D10.CircleEntropy.weight k.val *
      ‖densityFourier (CosineMixture.mixture s w N) (axisFrequency i k.val)‖ ^ 2) =
      ∑ a ∈ s, ∑ b ∈ s, ∑ L ∈ Legacy.D10.latentBox (N a),
        w a * w b * Legacy.D10.latentWeight (N a) (N b) L *
          (∑ i, (Legacy.D10.FiniteScalar.harmonic (L i) : ℝ)) := by
  simp_rw [mixture_axis_eq_latentTerm, tsum_latentAxisTerm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro L hL
  rw [Finset.mul_sum]

theorem axisEnergyTerm_eq_latentTerm (s : Finset α) (w : α → ℝ)
    (N : α → Fin d → ℕ) (hw : ∀ a ∈ s, 0 ≤ w a) (hm : ∑ a ∈ s, w a = 1)
    (i : Fin d) (k : NonzeroFrequency 1) :
    axisEnergyTerm (CosineMixture.density s w N hw hm) i k = latentAxisTerm s w N i k := by
  exact mixture_axis_eq_latentTerm s w N i k

theorem density_axis_sum_eq (s : Finset α) (w : α → ℝ) (N : α → Fin d → ℕ)
    (hw : ∀ a ∈ s, 0 ≤ w a) (hm : ∑ a ∈ s, w a = 1) :
    (∑ i, ∑' k : NonzeroFrequency 1, axisEnergyTerm (CosineMixture.density s w N hw hm) i k) =
      ∑ a ∈ s, ∑ b ∈ s, ∑ L ∈ Legacy.D10.latentBox (N a),
        w a * w b * Legacy.D10.latentWeight (N a) (N b) L *
          (∑ i, (Legacy.D10.FiniteScalar.harmonic (L i) : ℝ)) := by
  exact mixture_axis_sum_eq s w N

#print axioms mixture_axis_sum_eq
#print axioms density_axis_sum_eq
end Legacy.BecknerOnofri.CosineMixtureAxis
