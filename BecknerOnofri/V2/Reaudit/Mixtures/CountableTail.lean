module

public import BecknerOnofri.V2.Reaudit.Mixtures.PrintedGap
public import BecknerOnofri.V2.Reaudit.Mixtures.HarmonicRecurrence
public import BecknerOnofri.V2.Reaudit.Mixtures.LayerCake
public import BecknerOnofri.V2.Mixture.Countable

@[expose] public section

/-! # Proposition 5.11 `prop:section5-singular-fourier-tail` with Tonelli on the countable pair law

The printed proof draws independent index vectors `(N, M)` from the countable (correlated) weight
sequence `w`, then the coordinatewise hypergeometric vector `L` given `(N, M)`.  Here the law of
`L` is the explicit countable sum `latentExpect` (`PrintedGap.lean`; the pair `(N, M) ∈ ℕ × ℕ`,
a finite box for `L`).  The proof follows the printed one:

* `|ρ̂(k)|² = E ∏_i a_{L_i}(k_i)` (Lemma `lem:hypergeometric`): `fourier_sq_eq_latentExpect`;
* Fubini--Tonelli for the nonnegative double series `∑_k ∑_{(N,M)}` (`tonelli_tsum_comm`),
  applied **directly to the countable pair index**, never through finite partial mixtures;
* `eq:section5-global-tail-arbitrary-indices` for each realisation of `L`
  (`tail_arbitrary_indices_direct`, continuous layer cake, `LayerCake.lean`);
* `T_n ≤ R_n` (`RouteM.Tn_le_Rn`, the scalar lemma `lem:section5-global-scalar-tail`);
* the nonnegative representation `eq:section5-global-harmonic-tail`
  (`HarmonicRecurrence.Rn_eq_positive_printed`) and Tonelli once more for the `j ≥ 4` series.

No finite truncation of the mixture occurs in this file. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Finset Filter
open scoped Topology BigOperators

namespace BecknerOnofri.V2.Reaudit.Mixtures

open BecknerOnofri.V2.ThetaTail (aCoef Tn Rn cube12 latticeNorm)
open BecknerOnofri.HighDim.EntropyTail (scalarTailWeight scalarTailWeight_nonneg
  scalarTailWeight_le_one mixedTail mixedCoefficient mixedCoefficient_component
  mixedCoefficient_axis mixedTail_summable scalarTail)
open Legacy.TorusEndpoint Legacy.BecknerOnofri
open BecknerOnofri.CosineMixtureTransfer
open Legacy.D10 (latentBox latentWeight latentWeight_nonneg sum_latentWeight)

/-! ## Fubini--Tonelli for nonnegative real double series -/

/-- Tonelli for a nonnegative double series: if every row is summable and the row sums are
summable, the double family is summable, the column sums are summable, and the two iterated sums
agree. -/
theorem tonelli_tsum_comm {ι κ : Type*} (f : ι → κ → ℝ) (hf : ∀ i k, 0 ≤ f i k)
    (hrow : ∀ i, Summable (f i)) (hout : Summable fun i => ∑' k, f i k) :
    Summable (Function.uncurry f) ∧ Summable (fun k => ∑' i, f i k) ∧
      ∑' k, ∑' i, f i k = ∑' i, ∑' k, f i k := by
  have hu : Summable (Function.uncurry f) :=
    (summable_prod_of_nonneg (f := Function.uncurry f) (fun p => hf p.1 p.2)).2 ⟨hrow, hout⟩
  exact ⟨hu, hu.prod_symm.prod, hu.tsum_comm⟩

/-! ## Linearity of the pair mass -/

section PairMass
variable {d : ℕ}

theorem pairMass_add (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ) (F G : (Fin d → ℕ) → ℝ) (a b : ℕ) :
    pairMass w N (fun L => F L + G L) a b = pairMass w N F a b + pairMass w N G a b := by
  unfold pairMass
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl (fun L _ => by ring)

theorem pairMass_const_mul (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ) (c : ℝ) (F : (Fin d → ℕ) → ℝ)
    (a b : ℕ) : pairMass w N (fun L => c * F L) a b = c * pairMass w N F a b := by
  unfold pairMass
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun L _ => by ring)

theorem pairMass_finsetSum {ι : Type*} (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ) (t : Finset ι)
    (F : ι → (Fin d → ℕ) → ℝ) (a b : ℕ) :
    pairMass w N (fun L => ∑ i ∈ t, F i L) a b = ∑ i ∈ t, pairMass w N (F i) a b := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [pairMass]
  | @insert i t hi ih =>
    simp only [Finset.sum_insert hi]
    rw [pairMass_add, ih]

theorem pairMass_mono (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ) (hw : ∀ n, 0 ≤ w n)
    {F G : (Fin d → ℕ) → ℝ} (h : ∀ L, F L ≤ G L) (a b : ℕ) :
    pairMass w N F a b ≤ pairMass w N G a b := by
  unfold pairMass
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (hw a) (hw b))
  exact Finset.sum_le_sum fun L _ => mul_le_mul_of_nonneg_left (h L) (latentWeight_nonneg _ _ _)

end PairMass

/-! ## The hypergeometric identity `|ρ̂(k)|² = E ∏_i a_{L_i}(k_i)` over the countable pair law -/

theorem pairMass_componentCoeff {d : ℕ} (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ) (k : Fin d → ℤ)
    (a b : ℕ) :
    pairMass w N (fun L => RandomRectangles.componentCoeff L k) a b =
      (w a * RandomRectangles.componentCoeff (N a) k) *
        (w b * RandomRectangles.componentCoeff (N b) k) := by
  unfold pairMass
  have h := Legacy.D10.latent_product (N a) (N b) (fun i => (k i).natAbs)
  have e : ∀ M : Fin d → ℕ, RandomRectangles.componentCoeff M k =
      Legacy.D10.binomialProduct M (fun i => (k i).natAbs) := fun M => rfl
  simp only [e]
  rw [mul_assoc, h]
  ring

theorem summable_pairMass_componentCoeff {d : ℕ} (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ)
    (hw : ∀ n, 0 ≤ w n) (hs : Summable w) (k : Fin d → ℤ) :
    Summable (fun p : ℕ × ℕ =>
      pairMass w N (fun L => RandomRectangles.componentCoeff L k) p.1 p.2) :=
  summable_pairMass w N hw hs (fun L => RandomRectangles.componentCoeff_nonneg L k)
    (fun L => CosineMixtureTransfer.componentCoeff_le_one L k)

/-- `eq:mixture-fourier-square` for the countable mixture:
`|ρ̂(k)|² = E ∏_i a_{L_i}(k_i)`, with `E` the countable pair law `latentExpect`. -/
theorem fourier_sq_eq_latentExpect {d : ℕ} (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ)
    (hw : ∀ n, 0 ≤ w n) (hs : Summable w) (k : Fin d → ℤ) :
    ‖densityFourier (CosineMixtureApproximation.rho w N) k‖ ^ 2 =
      latentExpect w N (fun L => RandomRectangles.componentCoeff L k) := by
  rw [rho_fourier w N hw hs, Complex.norm_real, Real.norm_eq_abs, sq_abs, sq]
  have hsum := summable_mixture_coeff w N hw hs k
  have hn : Summable (fun n => ‖w n * RandomRectangles.componentCoeff (N n) k‖) := by
    refine hsum.congr (fun n => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (hw n) (RandomRectangles.componentCoeff_nonneg _ _))]
  rw [tsum_mul_tsum_of_summable_norm hn hn]
  unfold latentExpect
  exact tsum_congr (fun p => (pairMass_componentCoeff w N k p.1 p.2).symm)

/-! ## Axis coefficients as latent expectations -/

theorem aCoef_eq_axis (L : Fin 12 → ℕ) (i : Fin 12) (m : ℕ) :
    aCoef (L i) (m : ℤ) = RandomRectangles.componentCoeff L (Pi.single i (m : ℤ)) := by
  rw [← mixedCoefficient_component, mixedCoefficient_axis,
    BecknerOnofri.V2.Mixture.scalarCoefficient_eq_aCoef]

theorem aCoef_axis_le_one (L : Fin 12 → ℕ) (i : Fin 12) (m : ℕ) : aCoef (L i) (m : ℤ) ≤ 1 := by
  rw [aCoef_eq_axis]
  exact CosineMixtureTransfer.componentCoeff_le_one _ _

/-- `E[a_{L_i}(m)] = |ρ̂(m e_i)|²`. -/
theorem latentExpect_axis (w : ℕ → ℝ) (N : ℕ → Fin 12 → ℕ) (hw : ∀ n, 0 ≤ w n)
    (hs : Summable w) (i : Fin 12) (m : ℕ) :
    latentExpect w N (fun L => aCoef (L i) (m : ℤ)) =
      ‖densityFourier (CosineMixtureApproximation.rho w N) (Pi.single i (m : ℤ))‖ ^ 2 := by
  rw [fourier_sq_eq_latentExpect w N hw hs]
  have h : (fun L : Fin 12 → ℕ => aCoef (L i) (m : ℤ)) =
      fun L => RandomRectangles.componentCoeff L (Pi.single i (m : ℤ)) :=
    funext fun L => aCoef_eq_axis L i m
  rw [h]

theorem summable_pairMass_axis (w : ℕ → ℝ) (N : ℕ → Fin 12 → ℕ) (hw : ∀ n, 0 ≤ w n)
    (hs : Summable w) (i : Fin 12) (m : ℕ) :
    Summable (fun p : ℕ × ℕ => pairMass w N (fun L => aCoef (L i) (m : ℤ)) p.1 p.2) :=
  summable_pairMass w N hw hs (fun _ => aCoef_nonneg' _ _) (fun L => aCoef_axis_le_one L i m)

/-! ## The series `∑_{j≥4} a_{L_i}(j)/j` and Tonelli in `(j, (N, M))` -/

/-- The `j`-th term `a_{L_i}(j+4)/(j+4)` of the series in `eq:section5-global-harmonic-tail`. -/
def tailTerm (i : Fin 12) (j : ℕ) (L : Fin 12 → ℕ) : ℝ := aCoef (L i) ((j : ℤ) + 4) / ((j : ℝ) + 4)

theorem tailTerm_nonneg (i : Fin 12) (j : ℕ) (L : Fin 12 → ℕ) : 0 ≤ tailTerm i j L :=
  div_nonneg (aCoef_nonneg' _ _) (by positivity)

theorem tailTerm_le_one (i : Fin 12) (j : ℕ) (L : Fin 12 → ℕ) : tailTerm i j L ≤ 1 := by
  unfold tailTerm
  have h1 : aCoef (L i) ((j : ℤ) + 4) ≤ 1 := by
    have := aCoef_axis_le_one L i (j + 4)
    simpa using this
  have h4 : (1 : ℝ) ≤ (j : ℝ) + 4 := by
    have := Nat.cast_nonneg (α := ℝ) j
    linarith
  exact (div_le_self (aCoef_nonneg' _ _) h4).trans h1

theorem summable_tailTerm (L : Fin 12 → ℕ) (i : Fin 12) : Summable (fun j => tailTerm i j L) := by
  have := (summable_aCoef_div (L i)).comp_injective (add_left_injective 3)
  refine this.congr (fun j => ?_)
  simp only [Function.comp_apply, tailTerm]
  push_cast
  ring_nf

theorem latentExpect_tailTerm (w : ℕ → ℝ) (N : ℕ → Fin 12 → ℕ) (hw : ∀ n, 0 ≤ w n)
    (hs : Summable w) (i : Fin 12) (j : ℕ) :
    ∑' p : ℕ × ℕ, pairMass w N (tailTerm i j) p.1 p.2 =
      ‖densityFourier (CosineMixtureApproximation.rho w N) (Pi.single i ((j : ℤ) + 4))‖ ^ 2 /
        ((j : ℝ) + 4) := by
  have h : tailTerm i j = fun L => ((j : ℝ) + 4)⁻¹ * aCoef (L i) ((j + 4 : ℕ) : ℤ) := by
    funext L
    unfold tailTerm
    push_cast
    rw [div_eq_inv_mul]
  have e := latentExpect_axis w N hw hs i (j + 4)
  unfold latentExpect at e
  have hp : ∀ p : ℕ × ℕ, pairMass w N (tailTerm i j) p.1 p.2 =
      ((j : ℝ) + 4)⁻¹ * pairMass w N (fun L => aCoef (L i) ((j + 4 : ℕ) : ℤ)) p.1 p.2 := by
    intro p
    rw [h]
    exact pairMass_const_mul w N _ _ _ _
  rw [tsum_congr hp, tsum_mul_left, e]
  push_cast
  rw [div_eq_inv_mul]

/-- Tonelli in `(j, (N, M))` for the series `∑_{j≥4} a_{L_i}(j)/j`: the pair-law mass of the
series is summable with total `∑_{j≥4} |ρ̂(j e_i)|²/j`. -/
theorem tail_axis_pair (w : ℕ → ℝ) (N : ℕ → Fin 12 → ℕ) (hw : ∀ n, 0 ≤ w n) (hs : Summable w)
    (hSup : Summable (fun n => w n * CosineMixture.tensor (N n) 0)) (i : Fin 12) :
    Summable (fun p : ℕ × ℕ => pairMass w N (fun L => ∑' j, tailTerm i j L) p.1 p.2) ∧
      ∑' p : ℕ × ℕ, pairMass w N (fun L => ∑' j, tailTerm i j L) p.1 p.2 =
        ∑' j : ℕ, ‖densityFourier (CosineMixtureApproximation.rho w N)
          (Pi.single i ((j : ℤ) + 4))‖ ^ 2 / ((j : ℝ) + 4) := by
  let f : ℕ → ℕ × ℕ → ℝ := fun j p => pairMass w N (tailTerm i j) p.1 p.2
  have hf : ∀ j p, 0 ≤ f j p := fun j p =>
    pairMass_nonneg w N hw (tailTerm_nonneg i j) p.1 p.2
  have hrow : ∀ j, Summable (f j) := fun j =>
    summable_pairMass w N hw hs (tailTerm_nonneg i j) (tailTerm_le_one i j)
  have hrowsum : ∀ j, ∑' p, f j p =
      ‖densityFourier (CosineMixtureApproximation.rho w N) (Pi.single i ((j : ℤ) + 4))‖ ^ 2 /
        ((j : ℝ) + 4) := fun j => latentExpect_tailTerm w N hw hs i j
  have hdom := (summable_fourier_sq
    (CosineMixtureApproximation.rho_continuous w N hw hSup)).comp_injective
    (BecknerOnofri.V2.Mixture.axis_tail_injective i)
  have hout : Summable fun j => ∑' p, f j p := by
    simp_rw [hrowsum]
    refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_) hdom
    exact div_le_self (sq_nonneg _) (by have := Nat.cast_nonneg (α := ℝ) j; linarith)
  obtain ⟨_, hsum, hcomm⟩ := tonelli_tsum_comm f hf hrow hout
  have hpt : ∀ p : ℕ × ℕ, ∑' j, f j p =
      pairMass w N (fun L => ∑' j, tailTerm i j L) p.1 p.2 := by
    intro p
    simp only [f, pairMass]
    rw [tsum_mul_left]
    congr 1
    rw [Summable.tsum_finsetSum (fun L _ => (summable_tailTerm L i).mul_left _)]
    exact Finset.sum_congr rfl (fun L _ => tsum_mul_left)
  refine ⟨hsum.congr hpt, ?_⟩
  rw [← tsum_congr hpt, hcomm]
  exact tsum_congr hrowsum

/-! ## The budget `(1/12) ∑_i R_{L_i}` and its pair-law mass -/

/-- The integrand `L ↦ (1/12) ∑_i R_{L_i}` of the last display
`eq:section5-global-tail-mixture-calculation`. -/
def budgetFn (L : Fin 12 → ℕ) : ℝ := (1 / 12 : ℝ) * ∑ i : Fin 12, Rn (L i)

theorem budgetFn_eq (L : Fin 12 → ℕ) :
    budgetFn L = (1 / 12 : ℝ) * ∑ i : Fin 12,
      (3 / 5 * aCoef (L i) 2 + 16 / 5 * aCoef (L i) 3 + 81 / 5 * ∑' j, tailTerm i j L) := by
  unfold budgetFn
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Rn_eq_positive_printed]
  rfl

theorem budget_pair (w : ℕ → ℝ) (N : ℕ → Fin 12 → ℕ) (hw : ∀ n, 0 ≤ w n) (hs : Summable w)
    (hSup : Summable (fun n => w n * CosineMixture.tensor (N n) 0)) :
    Summable (fun p : ℕ × ℕ => pairMass w N budgetFn p.1 p.2) ∧
      ∑' p : ℕ × ℕ, pairMass w N budgetFn p.1 p.2 =
        (1 / 12 : ℝ) * ∑ i : Fin 12,
          (3 / 5 * ‖densityFourier (CosineMixtureApproximation.rho w N) (Pi.single i (2 : ℤ))‖ ^ 2 +
            16 / 5 * ‖densityFourier (CosineMixtureApproximation.rho w N)
              (Pi.single i (3 : ℤ))‖ ^ 2 +
            81 / 5 * ∑' j : ℕ, ‖densityFourier (CosineMixtureApproximation.rho w N)
              (Pi.single i ((j : ℤ) + 4))‖ ^ 2 / ((j : ℝ) + 4)) := by
  -- the three pieces for a fixed coordinate `i`
  have h2 (i : Fin 12) := summable_pairMass_axis w N hw hs i 2
  have h3 (i : Fin 12) := summable_pairMass_axis w N hw hs i 3
  have ht (i : Fin 12) := tail_axis_pair w N hw hs hSup i
  have e2 (i : Fin 12) : ∑' p : ℕ × ℕ, pairMass w N (fun L => aCoef (L i) 2) p.1 p.2 =
      ‖densityFourier (CosineMixtureApproximation.rho w N) (Pi.single i (2 : ℤ))‖ ^ 2 := by
    have := latentExpect_axis w N hw hs i 2
    simpa [latentExpect] using this
  have e3 (i : Fin 12) : ∑' p : ℕ × ℕ, pairMass w N (fun L => aCoef (L i) 3) p.1 p.2 =
      ‖densityFourier (CosineMixtureApproximation.rho w N) (Pi.single i (3 : ℤ))‖ ^ 2 := by
    have := latentExpect_axis w N hw hs i 3
    simpa [latentExpect] using this
  have h2' (i : Fin 12) : Summable (fun p : ℕ × ℕ =>
      pairMass w N (fun L => aCoef (L i) 2) p.1 p.2) := by simpa using h2 i
  have h3' (i : Fin 12) : Summable (fun p : ℕ × ℕ =>
      pairMass w N (fun L => aCoef (L i) 3) p.1 p.2) := by simpa using h3 i
  -- the pair mass of the budget is the stated finite combination
  have hpt (p : ℕ × ℕ) : pairMass w N budgetFn p.1 p.2 =
      (1 / 12 : ℝ) * ∑ i : Fin 12,
        (3 / 5 * pairMass w N (fun L => aCoef (L i) 2) p.1 p.2 +
          16 / 5 * pairMass w N (fun L => aCoef (L i) 3) p.1 p.2 +
          81 / 5 * pairMass w N (fun L => ∑' j, tailTerm i j L) p.1 p.2) := by
    have e : budgetFn = fun L => (1 / 12 : ℝ) * ∑ i : Fin 12,
        ((3 / 5 * aCoef (L i) 2 + 16 / 5 * aCoef (L i) 3) + 81 / 5 * ∑' j, tailTerm i j L) := by
      funext L
      rw [budgetFn_eq]
    rw [e, pairMass_const_mul, pairMass_finsetSum]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [pairMass_add, pairMass_add, pairMass_const_mul, pairMass_const_mul, pairMass_const_mul]
  have hsumi (i : Fin 12) : Summable (fun p : ℕ × ℕ =>
      3 / 5 * pairMass w N (fun L => aCoef (L i) 2) p.1 p.2 +
        16 / 5 * pairMass w N (fun L => aCoef (L i) 3) p.1 p.2 +
        81 / 5 * pairMass w N (fun L => ∑' j, tailTerm i j L) p.1 p.2) :=
    (((h2' i).mul_left _).add ((h3' i).mul_left _)).add (((ht i).1).mul_left _)
  have hsum_all : Summable (fun p : ℕ × ℕ => pairMass w N budgetFn p.1 p.2) := by
    simp_rw [hpt]
    exact (summable_sum (fun i _ => hsumi i)).mul_left _
  refine ⟨hsum_all, ?_⟩
  simp_rw [hpt]
  rw [tsum_mul_left, Summable.tsum_finsetSum (fun i _ => hsumi i)]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Summable.tsum_add (((h2' i).mul_left _).add ((h3' i).mul_left _)) (((ht i).1).mul_left _),
    Summable.tsum_add ((h2' i).mul_left _) ((h3' i).mul_left _), tsum_mul_left, tsum_mul_left,
    tsum_mul_left, e2, e3, (ht i).2]

/-! ## Proposition 5.11 for countable correlated mixtures -/

/-- For each realisation of `L`: `eq:section5-global-tail-arbitrary-indices` (continuous layer
cake) followed by `T_n ≤ R_n` (`lem:section5-global-scalar-tail`):
`∑_k |k|^{-12} ∏_i a_{L_i}(k_i) ≤ (1/12) ∑_i T_{L_i} ≤ (1/12) ∑_i R_{L_i}`. -/
theorem mixedTail_le_budget (L : Fin 12 → ℕ) : mixedTail L ≤ budgetFn L := by
  refine (mixedTail_le_diagonal_cont L).trans ?_
  unfold budgetFn
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum
  intro i _
  rw [BecknerOnofri.V2.Mixture.scalarTail_eq_Tn]
  exact BecknerOnofri.V2.ThetaTail.RouteM.Tn_le_Rn _

/-- The pair-law mass of the tail integrand: the `k`-sum of `|k|^{-12} E ∏_i a_{L_i}(k_i)`
equals the pair-law mass of `L ↦ ∑_k |k|^{-12} ∏_i a_{L_i}(k_i)`. -/
theorem tail_sum_pair (w : ℕ → ℝ) (N : ℕ → Fin 12 → ℕ) (p : ℕ × ℕ) :
    ∑' k : Fin 12 → ℤ, scalarTailWeight k *
        pairMass w N (fun L => RandomRectangles.componentCoeff L k) p.1 p.2 =
      pairMass w N mixedTail p.1 p.2 := by
  have hk (k : Fin 12 → ℤ) : scalarTailWeight k *
        pairMass w N (fun L => RandomRectangles.componentCoeff L k) p.1 p.2 =
      w p.1 * w p.2 * ∑ L ∈ latentBox (N p.1), latentWeight (N p.1) (N p.2) L *
        (scalarTailWeight k * RandomRectangles.componentCoeff L k) := by
    unfold pairMass
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun L _ => by ring)
  have hsm (L : Fin 12 → ℕ) : Summable (fun k : Fin 12 → ℤ =>
      scalarTailWeight k * RandomRectangles.componentCoeff L k) := by
    simpa only [mixedCoefficient_component] using mixedTail_summable L
  rw [tsum_congr hk, tsum_mul_left,
    Summable.tsum_finsetSum (fun L _ => (hsm L).mul_left _)]
  unfold pairMass
  congr 1
  refine Finset.sum_congr rfl (fun L _ => ?_)
  rw [tsum_mul_left]
  congr 1
  unfold mixedTail
  exact tsum_congr (fun k => by rw [mixedCoefficient_component])

/-- **Proposition 5.11 (`prop:section5-singular-fourier-tail`) for countable correlated
mixtures**, proved by Tonelli directly on the countable pair `(N, M) ∈ ℕ × ℕ`; the statement is
that of `Mixture.countable_mixture_singular_tail`.  The coefficients are `1/40, 2/15, 27/40`. -/
theorem countable_mixture_singular_tail_direct
    (w : ℕ → ℝ) (N : ℕ → Fin 12 → ℕ) (hw : ∀ n, 0 ≤ w n) (hs : Summable w)
    (hSup : Summable (fun n => w n * CosineMixture.tensor (N n) 0)) :
    (1 / 2 : ℝ) * ∑' k : Fin 12 → ℤ, (cube12ᶜ).indicator
        (fun k => (latticeNorm k ^ 12)⁻¹ *
          ‖densityFourier (CosineMixtureApproximation.rho w N) k‖ ^ 2) k ≤
      ∑ i : Fin 12,
        (1 / 40 * ‖densityFourier (CosineMixtureApproximation.rho w N) (Pi.single i (2 : ℤ))‖ ^ 2 +
          2 / 15 * ‖densityFourier (CosineMixtureApproximation.rho w N) (Pi.single i (3 : ℤ))‖ ^ 2 +
          27 / 40 * ∑' j : ℕ,
            ‖densityFourier (CosineMixtureApproximation.rho w N) (Pi.single i ((j : ℤ) + 4))‖ ^ 2 /
              ((j : ℝ) + 4)) := by
  have hcont := CosineMixtureApproximation.rho_continuous w N hw hSup
  have hsq := summable_fourier_sq hcont
  -- the double family over `(k, (N, M))`
  let f : (Fin 12 → ℤ) → ℕ × ℕ → ℝ := fun k p =>
    scalarTailWeight k * pairMass w N (fun L => RandomRectangles.componentCoeff L k) p.1 p.2
  have hf : ∀ k p, 0 ≤ f k p := fun k p =>
    mul_nonneg (scalarTailWeight_nonneg k)
      (pairMass_nonneg w N hw (fun L => RandomRectangles.componentCoeff_nonneg L k) p.1 p.2)
  have hrow : ∀ k, Summable (f k) := fun k =>
    (summable_pairMass_componentCoeff w N hw hs k).mul_left _
  have hrowsum : ∀ k, ∑' p, f k p =
      scalarTailWeight k * ‖densityFourier (CosineMixtureApproximation.rho w N) k‖ ^ 2 := by
    intro k
    simp only [f]
    rw [tsum_mul_left, fourier_sq_eq_latentExpect w N hw hs k]
    rfl
  have hout : Summable fun k => ∑' p, f k p := by
    simp_rw [hrowsum]
    refine Summable.of_nonneg_of_le
      (fun k => mul_nonneg (scalarTailWeight_nonneg k) (sq_nonneg _)) (fun k => ?_) hsq
    exact mul_le_of_le_one_left (sq_nonneg _) (scalarTailWeight_le_one k)
  obtain ⟨_, hsumP, hcomm⟩ := tonelli_tsum_comm f hf hrow hout
  have hpt : ∀ p : ℕ × ℕ, ∑' k, f k p = pairMass w N mixedTail p.1 p.2 :=
    fun p => tail_sum_pair w N p
  -- Tonelli
  have hL : ∑' k, scalarTailWeight k *
      ‖densityFourier (CosineMixtureApproximation.rho w N) k‖ ^ 2 =
        ∑' p : ℕ × ℕ, pairMass w N mixedTail p.1 p.2 := by
    rw [← tsum_congr hrowsum, ← hcomm]
    exact tsum_congr hpt
  have hsumM : Summable (fun p : ℕ × ℕ => pairMass w N mixedTail p.1 p.2) := hsumP.congr hpt
  obtain ⟨hsumB, hB⟩ := budget_pair w N hw hs hSup
  have hle : ∑' p : ℕ × ℕ, pairMass w N mixedTail p.1 p.2 ≤
      ∑' p : ℕ × ℕ, pairMass w N budgetFn p.1 p.2 :=
    Summable.tsum_le_tsum
      (fun p => pairMass_mono w N hw (fun L => mixedTail_le_budget L) p.1 p.2) hsumM hsumB
  have hI : ∑' k : Fin 12 → ℤ, (cube12ᶜ).indicator
      (fun k => (latticeNorm k ^ 12)⁻¹ *
        ‖densityFourier (CosineMixtureApproximation.rho w N) k‖ ^ 2) k =
      ∑' k, scalarTailWeight k * ‖densityFourier (CosineMixtureApproximation.rho w N) k‖ ^ 2 :=
    tsum_congr (fun k => (BecknerOnofri.V2.Mixture.tailWeight_mul_eq_indicator k _).symm)
  rw [hI, hL]
  refine (mul_le_mul_of_nonneg_left (hle.trans_eq hB) (by norm_num)).trans_eq ?_
  rw [← mul_assoc, show (1 / 2 : ℝ) * (1 / 12) = 1 / 24 by norm_num, one_div, one_div, mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

#print axioms countable_mixture_singular_tail_direct

/-- **Proposition 5.11** (`prop:section5-singular-fourier-tail`, `eq:section5-global-tail-energy`),
for every smooth probability density of the form `eq:mixture` on `𝕋¹²`; the statement is that of
`Mixture.singular_fourier_tail`, proved through the countable pair-law Tonelli argument. -/
theorem singular_fourier_tail_direct (ρ : HighDim.ProbabilityDensity 12)
    (hs : HighDim.SmoothOnTorus ρ.value) (hρ : HighDim.IsCountableCosineMixture ρ) :
    (1 / 2 : ℝ) * ∑' k : Fin 12 → ℤ, (cube12ᶜ).indicator
        (fun k => (latticeNorm k ^ 12)⁻¹ * ‖HighDim.fourierCoeff ρ.value k‖ ^ 2) k ≤
      ∑ i : Fin 12,
        (1 / 40 * ‖HighDim.fourierCoeff ρ.value (Pi.single i (2 : ℤ))‖ ^ 2 +
          2 / 15 * ‖HighDim.fourierCoeff ρ.value (Pi.single i (3 : ℤ))‖ ^ 2 +
          27 / 40 * ∑' j : ℕ,
            ‖HighDim.fourierCoeff ρ.value (Pi.single i ((j : ℤ) + 4))‖ ^ 2 / ((j : ℝ) + 4)) := by
  obtain ⟨w, N, hw, hm, he⟩ := hρ
  have he' : ρ.value =ᵐ[HighDim.torusMeasure 12]
      Legacy.BecknerOnofri.CosineMixtureApproximation.rho w N := he
  have hSup := CosineMixtureTransfer.mixture_majorant_of_continuous ρ.value
    (HighDim.UniformFourier.smooth_continuous hs) w N hw hm.summable he'
  have htail := countable_mixture_singular_tail_direct w N hw hm.summable hSup
  have hf (k : Fin 12 → ℤ) : HighDim.fourierCoeff ρ.value k =
      HighDim.fourierCoeff (Legacy.BecknerOnofri.CosineMixtureApproximation.rho w N) k := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards [he'] with x hx
    rw [hx]
  simp_rw [hf]
  exact htail

#print axioms singular_fourier_tail_direct

end BecknerOnofri.V2.Reaudit.Mixtures
