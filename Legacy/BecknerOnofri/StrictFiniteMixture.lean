module

public import Legacy.BecknerOnofri.LowDimensionMixtureEndpoint

@[expose] public section

/-! A quantitative strict endpoint gap for a genuine finite cosine mixture.
A single positive nonconstant component supplies a fixed latent diagonal event. -/
noncomputable section
open Finset MeasureTheory Legacy.TorusEndpoint
namespace Legacy.BecknerOnofri.StrictMixture
open CosineMixtureEnergy GaussianScalarTail

def componentDefect {d : ℕ} (N : Fin d → ℕ) : ℝ :=
  (∑ i, (Legacy.D10.FiniteScalar.harmonic (N i) : ℝ)) -
    (2 * endpointConstant d) * componentEnergy N

def gap (d : ℕ) : ℝ := 3 / (1100 * (d : ℝ))

theorem gap_pos {d : ℕ} (hd : 0 < d) : 0 < gap d := by
  unfold gap
  positivity

theorem componentDefect_nonneg {d : ℕ} (hd2 : 2 ≤ d) (hd10 : d ≤ 10)
    (N : Fin d → ℕ) : 0 ≤ componentDefect N :=
  sub_nonneg.mpr (LowDimensionMixtureEndpoint.component_bound hd2 hd10 N)

theorem scalar_indicator_bound {d : ℕ} (hd2 : 2 ≤ d) (hd10 : d ≤ 10) (n : ℕ) :
    (2 * endpointConstant d) * GaussianLattice.binomialEnergy d n +
      (if n = 0 then 0 else (3 / 1100 : ℝ)) ≤
        (d : ℝ) * (Legacy.D10.FiniteScalar.harmonic n : ℝ) := by
  by_cases hd : d = 2
  · subst d
    exact GaussianScalarTwo.all_indices_lattice_indicator_bound n
  · exact GaussianScalarTail.all_indices_lattice_indicator_bound (by omega) hd10 n

theorem componentDefect_gap {d : ℕ} (hd2 : 2 ≤ d) (hd10 : d ≤ 10)
    (N : Fin d → ℕ) (hN : N ≠ 0) : gap d ≤ componentDefect N := by
  classical
  have hd0 : 0 < d := by omega
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd0
  obtain ⟨i, hi⟩ : ∃ i, N i ≠ 0 := by
    by_contra h
    push Not at h
    exact hN (funext h)
  have hsum := sum_le_sum (fun j (_ : j ∈ (univ : Finset (Fin d))) =>
    scalar_indicator_bound hd2 hd10 (N j))
  rw [sum_add_distrib, ← mul_sum, ← mul_sum] at hsum
  have hind : (3 / 1100 : ℝ) ≤ ∑ j, if N j = 0 then 0 else (3 / 1100 : ℝ) := by
    simpa [hi] using single_le_sum (f := fun j => if N j = 0 then 0 else (3 / 1100 : ℝ))
      (fun j _ => by split_ifs <;> norm_num) (mem_univ i)
  have havg := mul_le_mul_of_nonneg_left
    (MixedBinomialComparison.componentEnergy_le_average_diagonal hd0 N)
    (coefficient_nonneg hd0)
  have hmul := (mul_le_mul_of_nonneg_left havg hdR.le)
  have heq : (d : ℝ) * ((2 * endpointConstant d) *
      ((1 / (d : ℝ)) * ∑ j, GaussianLattice.binomialEnergy d (N j))) =
      (2 * endpointConstant d) * ∑ j, GaussianLattice.binomialEnergy d (N j) := by
    field_simp
  rw [heq] at hmul
  have hg : gap d = (3 / 1100 : ℝ) / (d : ℝ) := by unfold gap; ring
  rw [hg]
  apply (div_le_iff₀ hdR).mpr
  unfold componentDefect
  nlinarith

theorem latentWeight_self_pos {d : ℕ} (N : Fin d → ℕ) : 0 < Legacy.D10.latentWeight N N N := by
  unfold Legacy.D10.latentWeight
  apply prod_pos
  intro i hi
  unfold Legacy.D10.hypergeometricWeightReal Legacy.D10.hypergeometricWeight
  have hc : 0 < (N i + N i).choose (N i) := Nat.choose_pos (by omega)
  norm_cast
  simp only [Nat.choose_self, Nat.cast_one, mul_one]
  exact div_pos (by norm_num) (Nat.cast_pos.mpr hc)

theorem mem_latentBox_self {d : ℕ} (N : Fin d → ℕ) : N ∈ Legacy.D10.latentBox N := by
  simp [Legacy.D10.latentBox]

variable {α : Type*} {d : ℕ}

def latentDefect (w : α → ℝ) (N : α → Fin d → ℕ) (a b : α) (L : Fin d → ℕ) : ℝ :=
  w a * w b * Legacy.D10.latentWeight (N a) (N b) L * componentDefect L

theorem latentDefect_nonneg (hd2 : 2 ≤ d) (hd10 : d ≤ 10)
    (w : α → ℝ) (N : α → Fin d → ℕ) (a b : α) (L : Fin d → ℕ)
    (ha : 0 ≤ w a) (hb : 0 ≤ w b) : 0 ≤ latentDefect w N a b L :=
  mul_nonneg (Legacy.D10.correlated_latent_nonneg w w N N a b L ha hb)
    (componentDefect_nonneg hd2 hd10 L)

theorem finite_mixture_gap (hd2 : 2 ≤ d) (hd10 : d ≤ 10)
    (s : Finset α) (w : α → ℝ) (N : α → Fin d → ℕ)
    (hw : ∀ a ∈ s, 0 ≤ w a) (hm : ∑ a ∈ s, w a = 1)
    (hpos : ∀ x, 0 < CosineMixture.mixture s w N x)
    (a : α) (ha : a ∈ s) (hN : N a ≠ 0) :
    endpointConstant d * fourierEnergy (CosineMixture.density s w N hw hm) +
      w a * w a * Legacy.D10.latentWeight (N a) (N a) (N a) * gap d / 2 ≤
        densityEntropy (CosineMixture.density s w N hw hm).value := by
  have hsmall : w a * w a * Legacy.D10.latentWeight (N a) (N a) (N a) * gap d ≤
      latentDefect w N a a (N a) :=
    mul_le_mul_of_nonneg_left (componentDefect_gap hd2 hd10 (N a) hN)
      (Legacy.D10.correlated_latent_nonneg w w N N a a (N a) (hw a ha) (hw a ha))
  have hsum : latentDefect w N a a (N a) ≤
      ∑ b ∈ s, ∑ c ∈ s, ∑ L ∈ Legacy.D10.latentBox (N b), latentDefect w N b c L := by
    calc
      _ ≤ ∑ L ∈ Legacy.D10.latentBox (N a), latentDefect w N a a L :=
        single_le_sum (fun L _ => latentDefect_nonneg hd2 hd10 w N a a L
          (hw a ha) (hw a ha)) (mem_latentBox_self (N a))
      _ ≤ ∑ c ∈ s, ∑ L ∈ Legacy.D10.latentBox (N a), latentDefect w N a c L :=
        single_le_sum (fun c hc => sum_nonneg (fun L _ =>
          latentDefect_nonneg hd2 hd10 w N a c L (hw a ha) (hw c hc))) ha
      _ ≤ _ := single_le_sum
        (f := fun b => ∑ c ∈ s, ∑ L ∈ Legacy.D10.latentBox (N b), latentDefect w N b c L)
        (fun b hb => sum_nonneg (fun c hc => sum_nonneg (fun L _ =>
        latentDefect_nonneg hd2 hd10 w N b c L (hw b hb) (hw c hc)))) ha
  have heq : (∑ b ∈ s, ∑ c ∈ s, ∑ L ∈ Legacy.D10.latentBox (N b), latentDefect w N b c L) =
      (∑ b ∈ s, ∑ c ∈ s, ∑ L ∈ Legacy.D10.latentBox (N b),
        w b * w c * Legacy.D10.latentWeight (N b) (N c) L *
          ∑ i, (Legacy.D10.FiniteScalar.harmonic (L i) : ℝ)) -
        (2 * endpointConstant d) * fourierEnergy (CosineMixture.density s w N hw hm) := by
    rw [fourierEnergy_eq_latent]
    simp only [latentDefect, componentDefect, mul_sub, sum_sub_distrib, mul_sum]
    congr 1
    apply sum_congr rfl
    intro b hb
    apply sum_congr rfl
    intro c hc
    apply sum_congr rfl
    intro L hL
    ring
  rw [heq] at hsum
  have haxis := (TorusMarginals.axis_entropy_bound (by omega : 0 < d)
    (CosineMixture.density s w N hw hm) (CosineMixture.mixture_continuous s w N) hpos).2
  rw [CosineMixtureAxis.density_axis_sum_eq] at haxis
  linarith

#print axioms componentDefect_gap
#print axioms finite_mixture_gap
end Legacy.BecknerOnofri.StrictMixture
