module

public import BecknerOnofri.V2.Section3.Marginal
public import BecknerOnofri.ExtendedMixtureEnergy
public import BecknerOnofri.LowScalarFull
public import BecknerOnofri.EntropyTailScalarBasic
public import Legacy.BecknerOnofri.MixedBinomialComparison

@[expose] public section

/-! # The written mixture derivation, finite stage (G04, Props 3.3--3.4)

Following Subsection 3.3 of the manuscript.  For a finite family of components with nonnegative
(possibly correlated) weights, the pair `(N, M)` of independent draws and the conditional
coordinatewise hypergeometric draw `L` are encoded by the finite *latent average*
`latAvg s w N F = ∑_{a, b} w_a w_b ∑_L P(L | N_a, N_b) F(L)`.

* `eq:mixture-fourier-square`: `|ρ̂(k)|² = E ∏_i a_{L_i}(k_i)` (Lemma 3.3 via `weighted_mixture_eq_latent`);
* `eq:mixture-energy-harmonic-expectations`: Tonelli for finite sums and `harmonic_identity`;
* `eq:AMGM` / `eq:mixed-index-strict-gap`: `scalar_gap` (Prop 3.4) and the mixed-index average.

The output is `finite_mixture_gap`: the finite-mixture form of `eq:mixture-strict-entropy-gap`. -/

noncomputable section
open Finset
open scoped BigOperators

namespace BecknerOnofri.V2.Section3
open BecknerOnofri.HighDim Legacy.TorusEndpoint
open Legacy.D10 (latentBox latentWeight latentWeight_nonneg sum_latentWeight binomialCoeffReal)

variable {d : ℕ}

/-- The finite latent average of `F(L)` for the mixture with weights `w` and indices `N`. -/
def latAvg {α : Type*} (s : Finset α) (w : α → ℝ) (N : α → Fin d → ℕ)
    (F : (Fin d → ℕ) → ℝ) : ℝ :=
  ∑ a ∈ s, ∑ b ∈ s, ∑ L ∈ latentBox (N a), w a * w b * latentWeight (N a) (N b) L * F L

theorem latAvg_mono {α : Type*} (s : Finset α) (w : α → ℝ) (N : α → Fin d → ℕ)
    (hw : ∀ a ∈ s, 0 ≤ w a) {F G : (Fin d → ℕ) → ℝ} (h : ∀ L, F L ≤ G L) :
    latAvg s w N F ≤ latAvg s w N G := by
  apply sum_le_sum
  intro a ha
  apply sum_le_sum
  intro b hb
  apply sum_le_sum
  intro L _
  exact mul_le_mul_of_nonneg_left (h L)
    (mul_nonneg (mul_nonneg (hw a ha) (hw b hb)) (latentWeight_nonneg _ _ _))

theorem latAvg_add {α : Type*} (s : Finset α) (w : α → ℝ) (N : α → Fin d → ℕ)
    (F G : (Fin d → ℕ) → ℝ) :
    latAvg s w N (fun L => F L + G L) = latAvg s w N F + latAvg s w N G := by
  simp only [latAvg, mul_add, sum_add_distrib]

theorem latAvg_mul {α : Type*} (s : Finset α) (w : α → ℝ) (N : α → Fin d → ℕ)
    (c : ℝ) (F : (Fin d → ℕ) → ℝ) :
    latAvg s w N (fun L => c * F L) = c * latAvg s w N F := by
  simp only [latAvg, mul_sum]
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro b _
  apply sum_congr rfl
  intro L _
  ring

theorem latAvg_sum {α ι : Type*} (s : Finset α) (w : α → ℝ) (N : α → Fin d → ℕ)
    (t : Finset ι) (F : ι → (Fin d → ℕ) → ℝ) :
    latAvg s w N (fun L => ∑ i ∈ t, F i L) = ∑ i ∈ t, latAvg s w N (F i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [latAvg]
  | @insert i t hi ih =>
    simp only [sum_insert hi]
    rw [latAvg_add, ih]

/-- Tonelli for the finite latent average and a nonnegative-term series. -/
theorem latAvg_tsum {α : Type*} (s : Finset α) (w : α → ℝ) (N : α → Fin d → ℕ)
    (F : ℕ → (Fin d → ℕ) → ℝ) (hF : ∀ L, Summable (fun j => F j L)) :
    (∑' j, latAvg s w N (F j)) = latAvg s w N (fun L => ∑' j, F j L) := by
  unfold latAvg
  rw [Summable.tsum_finsetSum]
  · apply sum_congr rfl
    intro a _
    rw [Summable.tsum_finsetSum]
    · apply sum_congr rfl
      intro b _
      rw [Summable.tsum_finsetSum]
      · simp_rw [tsum_mul_left]
      · intro L _
        exact (hF L).mul_left _
    · intro b _
      exact summable_sum (fun L _ => (hF L).mul_left _)
  · intro a _
    exact summable_sum (fun b _ => summable_sum (fun L _ => (hF L).mul_left _))

theorem latAvg_const {α : Type*} (s : Finset α) (w : α → ℝ) (N : α → Fin d → ℕ) (c : ℝ) :
    latAvg s w N (fun _ => c) = c * (∑ a ∈ s, w a) ^ 2 := by
  unfold latAvg
  have h : ∀ a b : α, ∑ L ∈ latentBox (N a), w a * w b * latentWeight (N a) (N b) L * c =
      w a * w b * c := by
    intro a b
    rw [← sum_mul, ← mul_sum, sum_latentWeight, mul_one]
  simp_rw [h]
  rw [sq, sum_mul_sum]
  simp only [Finset.mul_sum]
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro b _
  ring

/-! ### The axis identities -/

open BecknerOnofri.RandomRectangles (componentCoeff) in
theorem componentCoeff_axis (L : Fin d → ℕ) (i : Fin d) (m : ℕ) :
    componentCoeff L (Pi.single i (m : ℤ)) = binomialCoeffReal (L i) m := by
  classical
  unfold componentCoeff Legacy.D10.binomialProduct
  rw [Finset.prod_eq_single i]
  · simp
  · intro r _ hr
    simp [hr]
  · simp

/-- `E[a_{L_i}(m)] = |ρ̂(m e_i)|²` (`eq:mixture-fourier-square` on the axes). -/
theorem latAvg_axis {α : Type*} (s : Finset α) (w : α → ℝ) (N : α → Fin d → ℕ)
    (i : Fin d) (m : ℕ) :
    latAvg s w N (fun L => binomialCoeffReal (L i) m) =
      ‖densityFourier (Legacy.BecknerOnofri.CosineMixture.mixture s w N)
        (Pi.single i (m : ℤ))‖ ^ 2 := by
  have h := CosineMixtureTransfer.weighted_mixture_eq_latent s w N (fun _ => (1 : ℝ))
    (Pi.single i (m : ℤ))
  simp only [one_mul, CosineMixtureTransfer.latentTerm, componentCoeff_axis] at h
  exact h.symm

/-- `E[H_{L_i}] = 2 ∑_{j ≥ 1} |ρ̂(j e_i)|² / j` (`eq:mixture-energy-harmonic-expectations`,
second identity; Lemma 3.3's harmonic identity). -/
theorem latAvg_harmonic {α : Type*} (s : Finset α) (w : α → ℝ) (N : α → Fin d → ℕ)
    (i : Fin d) :
    latAvg s w N (fun L => ((harmonic (L i) : ℚ) : ℝ)) =
      2 * ∑' j : ℕ, ‖densityFourier (Legacy.BecknerOnofri.CosineMixture.mixture s w N)
        (Pi.single i ((j : ℤ) + 1))‖ ^ 2 / ((j : ℝ) + 1) := by
  let F : ℕ → (Fin d → ℕ) → ℝ := fun j L =>
    HighDim.EntropyTail.scalarCoefficient (L i) (j + 1) / ((j : ℝ) + 1)
  have hF (L : Fin d → ℕ) : HasSum (fun j => F j L) ((harmonic (L i) : ℝ) / 2) :=
    HighDim.LowScalar.harmonic_identity (L i)
  have hH (L : Fin d → ℕ) : ((harmonic (L i) : ℚ) : ℝ) = 2 * ∑' j, F j L := by
    rw [(hF L).tsum_eq]; ring
  have hsw : latAvg s w N (fun L => ((harmonic (L i) : ℚ) : ℝ)) =
      latAvg s w N (fun L => 2 * ∑' j, F j L) := by
    congr 1; funext L; exact hH L
  rw [hsw, latAvg_mul, ← latAvg_tsum s w N F (fun L => (hF L).summable)]
  congr 1
  apply tsum_congr
  intro j
  have hj : latAvg s w N (F j) = (1 / ((j : ℝ) + 1)) * latAvg s w N
      (fun L => binomialCoeffReal (L i) (j + 1)) := by
    rw [← latAvg_mul]
    congr 1
    funext L
    simp only [F, HighDim.EntropyTail.scalarCoefficient_eq]
    ring
  rw [hj, latAvg_axis]
  push_cast
  ring

/-! ### The scalar estimate for one latent index vector -/

theorem energy_zero (d : ℕ) : HighDim.LowScalar.energy d 0 = 0 := by
  unfold HighDim.LowScalar.energy
  refine (tsum_congr (g := fun _ => (0 : ℝ)) ?_).trans tsum_zero
  intro k
  by_cases hk : k = 0
  · simp [hk]
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp hk
    have hj : (k i).natAbs ≠ 0 := by simpa using hi
    have h0 : HighDim.EntropyTail.scalarCoefficient 0 (k i).natAbs = 0 := by
      simp [HighDim.EntropyTail.scalarCoefficient,
        Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hj)]
    rw [Finset.prod_eq_zero (Finset.mem_univ i) h0, mul_zero]

theorem endpoint_two_eq (d : ℕ) :
    2 * (d : ℝ) / spectralThreshold d = 2 * Legacy.BecknerOnofri.endpointConstant d := by
  unfold Legacy.BecknerOnofri.endpointConstant spectralThreshold Legacy.TorusEndpoint.endpointSigma
  ring

/-- Prop 3.4 together with the normalisation, for one index: with `c = 2 d / β_s(d)`,
`(c / d) G_{d,n} + 3/(1100 d) 1_{n ≥ 1} ≤ H_n`. -/
theorem index_scalar (hd2 : 2 ≤ d) (hd10 : d ≤ 10) (n : ℕ) :
    2 * Legacy.BecknerOnofri.endpointConstant d * (1 / (d : ℝ)) *
        Legacy.BecknerOnofri.GaussianLattice.binomialEnergy d n +
      (3 / (1100 * (d : ℝ))) * (if 1 ≤ n then 1 else 0) ≤ ((harmonic n : ℚ) : ℝ) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [← HighDim.LowScalar.energy_eq_legacy, energy_zero]
    simp
  · have h := HighDim.LowScalar.scalar_gap d n hd2 hd10 hn
    rw [endpoint_two_eq, HighDim.LowScalar.energy_eq_legacy] at h
    have h1 : (if 1 ≤ n then (1 : ℝ) else 0) = 1 := by simp; omega
    rw [h1]
    set E := Legacy.BecknerOnofri.GaussianLattice.binomialEnergy d n
    set c := 2 * Legacy.BecknerOnofri.endpointConstant d
    have h2 : (c * E + 3 / 1100) / (d : ℝ) ≤ ((harmonic n : ℚ) : ℝ) := by
      rw [div_le_iff₀ hd0]
      linarith
    have h3 : c * (1 / (d : ℝ)) * E + 3 / (1100 * (d : ℝ)) * 1 = (c * E + 3 / 1100) / (d : ℝ) := by
      field_simp
    linarith

open BecknerOnofri.RandomRectangles (componentCoeff) in
/-- Prop 3.4 plus `eq:mixed-index-average` for one index vector `L`:
`(2d/β_s) G_d(L) + (3/(1100 d)) #{i : L_i ≥ 1} ≤ ∑_i H_{L_i}`. -/
theorem component_scalar (hd2 : 2 ≤ d) (hd10 : d ≤ 10) (L : Fin d → ℕ) :
    2 * Legacy.BecknerOnofri.endpointConstant d *
        (∑' k : Fin d → ℤ, Legacy.BecknerOnofri.GaussianLattice.spectralWeight k *
          componentCoeff L k) +
      (3 / (1100 * (d : ℝ))) * ∑ i, (if 1 ≤ L i then (1 : ℝ) else 0) ≤
      ∑ i, ((harmonic (L i) : ℚ) : ℝ) := by
  have hd0 : 0 < d := by omega
  have hc : 0 ≤ 2 * Legacy.BecknerOnofri.endpointConstant d := by
    unfold Legacy.BecknerOnofri.endpointConstant
    have : 0 < Legacy.TorusEndpoint.endpointSigma d := Vocab.spectralThreshold_pos' hd0
    positivity
  have hcomp := Legacy.BecknerOnofri.MixedBinomialComparison.componentEnergy_le_average_diagonal
    hd0 L
  have hE : (∑' k : Fin d → ℤ, Legacy.BecknerOnofri.GaussianLattice.spectralWeight k *
      componentCoeff L k) = Legacy.BecknerOnofri.CosineMixtureEnergy.componentEnergy L := rfl
  rw [hE]
  calc _ ≤ 2 * Legacy.BecknerOnofri.endpointConstant d *
        ((1 / (d : ℝ)) * ∑ i, Legacy.BecknerOnofri.GaussianLattice.binomialEnergy d (L i)) +
        (3 / (1100 * (d : ℝ))) * ∑ i, (if 1 ≤ L i then (1 : ℝ) else 0) := by
        gcongr
    _ = ∑ i, (2 * Legacy.BecknerOnofri.endpointConstant d * (1 / (d : ℝ)) *
        Legacy.BecknerOnofri.GaussianLattice.binomialEnergy d (L i) +
        (3 / (1100 * (d : ℝ))) * (if 1 ≤ L i then (1 : ℝ) else 0)) := by
        rw [sum_add_distrib, ← mul_sum, ← mul_sum]
        ring
    _ ≤ _ := sum_le_sum fun i _ => index_scalar hd2 hd10 (L i)

/-- The mass `E ∑_i 1_{L_i ≥ 1}` of the latent positive indices. -/
def posMass {α : Type*} (s : Finset α) (w : α → ℝ) (N : α → Fin d → ℕ) : ℝ :=
  latAvg s w N (fun L => ∑ i, (if 1 ≤ L i then (1 : ℝ) else 0))

/-- **Finite mixtures, `eq:mixture-strict-entropy-gap` in the form before the entropy bound.**
For finitely many components with arbitrary nonnegative (correlated) weights and `2 ≤ d ≤ 10`,
`(2d/β_s(d)) ∑_{k≠0} |k|^{-d} |ρ̂(k)|² + (3/(1100 d)) E ∑_i 1_{L_i ≥ 1}
   ≤ 2 ∑_i ∑_{j ≥ 1} |ρ̂(j e_i)|² / j`. -/
theorem finite_mixture_gap (hd2 : 2 ≤ d) (hd10 : d ≤ 10) {α : Type*} (s : Finset α)
    (w : α → ℝ) (N : α → Fin d → ℕ) (hw : ∀ a ∈ s, 0 ≤ w a) :
    2 * Legacy.BecknerOnofri.endpointConstant d *
        (∑' k : Fin d → ℤ, Legacy.BecknerOnofri.GaussianLattice.spectralWeight k *
          ‖densityFourier (Legacy.BecknerOnofri.CosineMixture.mixture s w N) k‖ ^ 2) +
      (3 / (1100 * (d : ℝ))) * posMass s w N ≤
      2 * ∑ i : Fin d, ∑' j : ℕ, ‖densityFourier (Legacy.BecknerOnofri.CosineMixture.mixture s w N)
        (Pi.single i ((j : ℤ) + 1))‖ ^ 2 / ((j : ℝ) + 1) := by
  have hE : (∑' k : Fin d → ℤ, Legacy.BecknerOnofri.GaussianLattice.spectralWeight k *
      ‖densityFourier (Legacy.BecknerOnofri.CosineMixture.mixture s w N) k‖ ^ 2) =
      latAvg s w N (fun L => ∑' k : Fin d → ℤ,
        Legacy.BecknerOnofri.GaussianLattice.spectralWeight k *
          BecknerOnofri.RandomRectangles.componentCoeff L k) :=
    CosineMixtureTransfer.weighted_mixture_tsum s w N _
  rw [hE, posMass, ← latAvg_mul, ← latAvg_mul, ← latAvg_add]
  calc _ ≤ latAvg s w N (fun L => ∑ i, ((harmonic (L i) : ℚ) : ℝ)) :=
        latAvg_mono s w N hw (fun L => component_scalar hd2 hd10 L)
    _ = ∑ i, latAvg s w N (fun L => ((harmonic (L i) : ℚ) : ℝ)) := latAvg_sum s w N _ _
    _ = _ := by
        rw [mul_sum]
        exact sum_congr rfl fun i _ => latAvg_harmonic s w N i

end BecknerOnofri.V2.Section3
