module

public import BecknerOnofri.V2.Section3.Written
public import BecknerOnofri.V2.Reaudit.Mixtures.ChainRule

@[expose] public section

/-! # The strict mixture gap in the printed form, over the countable pair law (S023, U06)

The manuscript's `eq:mixture-strict-entropy-gap` reads
`Ent(ρ) - d c_d ‖ρ‖² ≥ (3 / (2200 d)) ∑_i P(L_i ≥ 1)`
where `(N, M)` is a pair of independent draws from the (countable, correlated) mixture weights and
`L` is drawn coordinatewise from the hypergeometric laws.  Here the law of `L` is the explicit
countable sum `latentExpect` (nonnegative terms, `ℕ × ℕ` for `(N, M)`, a finite box for `L`);
`latentProb w N i = P(L_i ≥ 1)`.  The quantitative bound is the existing
`Section3.mixture_energy_gap`, multiplied by `1/2` (the Lean statement is the printed inequality
multiplied by `2`); no new quantitative gap is proved. -/

noncomputable section
open Finset Filter MeasureTheory
open scoped BigOperators ENNReal Topology

namespace BecknerOnofri.V2.Reaudit.Mixtures
open BecknerOnofri.HighDim BecknerOnofri.V2.Vocab BecknerOnofri.V2.Section3
open Legacy.D10 (latentBox latentWeight latentWeight_nonneg sum_latentWeight)

variable {d : ℕ}

/-- The contribution of the pair `(N_a, N_b)` to `E F(L)`:
`w_a w_b ∑_L P(L | N_a, N_b) F(L)`. -/
def pairMass (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ) (F : (Fin d → ℕ) → ℝ) (a b : ℕ) : ℝ :=
  w a * w b * ∑ L ∈ latentBox (N a), latentWeight (N a) (N b) L * F L

/-- `E F(L)` for the pair-and-latent law of a countable mixture, as a sum over `(N, M) ∈ ℕ × ℕ`. -/
def latentExpect (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ) (F : (Fin d → ℕ) → ℝ) : ℝ :=
  ∑' p : ℕ × ℕ, pairMass w N F p.1 p.2

/-- `P(L_i ≥ 1)`. -/
def latentProb (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ) (i : Fin d) : ℝ :=
  latentExpect w N (fun L => if 1 ≤ L i then 1 else 0)

theorem latAvg_eq_sum_pairMass (s : Finset ℕ) (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ)
    (F : (Fin d → ℕ) → ℝ) :
    latAvg s w N F = ∑ p ∈ s ×ˢ s, pairMass w N F p.1 p.2 := by
  unfold latAvg pairMass
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun L _ => by ring)

theorem pairMass_nonneg (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ) (hw : ∀ n, 0 ≤ w n)
    {F : (Fin d → ℕ) → ℝ} (hF : ∀ L, 0 ≤ F L) (a b : ℕ) : 0 ≤ pairMass w N F a b :=
  mul_nonneg (mul_nonneg (hw a) (hw b))
    (Finset.sum_nonneg fun L _ => mul_nonneg (latentWeight_nonneg _ _ _) (hF L))

theorem pairMass_le (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ) (hw : ∀ n, 0 ≤ w n)
    {F : (Fin d → ℕ) → ℝ} {C : ℝ} (hC : ∀ L, F L ≤ C) (a b : ℕ) :
    pairMass w N F a b ≤ w a * w b * C := by
  unfold pairMass
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (hw a) (hw b))
  calc ∑ L ∈ latentBox (N a), latentWeight (N a) (N b) L * F L
      ≤ ∑ L ∈ latentBox (N a), latentWeight (N a) (N b) L * C :=
        Finset.sum_le_sum fun L _ => mul_le_mul_of_nonneg_left (hC L) (latentWeight_nonneg _ _ _)
    _ = C := by rw [← Finset.sum_mul, sum_latentWeight, one_mul]

theorem summable_pairMass (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ) (hw : ∀ n, 0 ≤ w n) (hs : Summable w)
    {F : (Fin d → ℕ) → ℝ} {C : ℝ} (hF : ∀ L, 0 ≤ F L) (hC : ∀ L, F L ≤ C) :
    Summable (fun p : ℕ × ℕ => pairMass w N F p.1 p.2) := by
  have h2 : Summable (fun p : ℕ × ℕ => w p.1 * w p.2 * C) :=
    ((Summable.mul_of_nonneg hs hs (fun n => hw n) (fun n => hw n))).mul_right C
  exact Summable.of_nonneg_of_le (fun p => pairMass_nonneg w N hw hF p.1 p.2)
    (fun p => pairMass_le w N hw hC p.1 p.2) h2

theorem tendsto_latAvg (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ) (hw : ∀ n, 0 ≤ w n) (hs : Summable w)
    {F : (Fin d → ℕ) → ℝ} {C : ℝ} (hF : ∀ L, 0 ≤ F L) (hC : ∀ L, F L ≤ C) :
    Tendsto (fun m => latAvg (range m) w N F) atTop (𝓝 (latentExpect w N F)) := by
  have hsum := (summable_pairMass w N hw hs hF hC).hasSum
  have hmono : Monotone (fun m : ℕ => range m ×ˢ range m) := by
    intro m m' h
    exact Finset.product_subset_product (Finset.range_mono h) (Finset.range_mono h)
  have hat : Tendsto (fun m : ℕ => range m ×ˢ range m) atTop atTop := by
    refine tendsto_atTop_finset_of_monotone hmono (fun p => ?_)
    refine ⟨max p.1 p.2 + 1, ?_⟩
    simp only [Finset.mem_product, Finset.mem_range]
    omega
  simp_rw [latAvg_eq_sum_pairMass]
  exact hsum.comp hat

theorem latAvg_le_latentExpect (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ) (hw : ∀ n, 0 ≤ w n)
    (hs : Summable w) {F : (Fin d → ℕ) → ℝ} {C : ℝ} (hF : ∀ L, 0 ≤ F L) (hC : ∀ L, F L ≤ C)
    (m : ℕ) : latAvg (range m) w N F ≤ latentExpect w N F := by
  rw [latAvg_eq_sum_pairMass]
  exact (summable_pairMass w N hw hs hF hC).sum_le_tsum _
    (fun p _ => pairMass_nonneg w N hw hF p.1 p.2)

/-- The indicator-sum functional whose mean is `∑_i P(L_i ≥ 1)`. -/
def posIndex (L : Fin d → ℕ) : ℝ := ∑ i, (if 1 ≤ L i then (1 : ℝ) else 0)

theorem posIndex_nonneg (L : Fin d → ℕ) : 0 ≤ posIndex L :=
  Finset.sum_nonneg fun i _ => by split_ifs <;> norm_num

theorem posIndex_le (L : Fin d → ℕ) : posIndex L ≤ d := by
  unfold posIndex
  calc ∑ i, (if 1 ≤ L i then (1 : ℝ) else 0) ≤ ∑ _i : Fin d, (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => by split_ifs <;> norm_num
    _ = d := by simp

theorem posMass_eq_latAvg (s : Finset ℕ) (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ) :
    posMass s w N = latAvg s w N posIndex := rfl

/-- `E ∑_i 1_{L_i ≥ 1} = ∑_i P(L_i ≥ 1)`: Tonelli for the finite sum over `i`. -/
theorem latentExpect_posIndex (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ) (hw : ∀ n, 0 ≤ w n)
    (hs : Summable w) : latentExpect w N posIndex = ∑ i, latentProb w N i := by
  have hind (i : Fin d) := summable_pairMass w N hw hs (F := fun L : Fin d → ℕ =>
    (if 1 ≤ L i then (1 : ℝ) else 0)) (C := 1) (fun L => by split_ifs <;> norm_num)
    (fun L => by split_ifs <;> norm_num)
  simp only [latentProb]
  unfold latentExpect
  rw [← Summable.tsum_finsetSum (fun i _ => hind i)]
  refine tsum_congr (fun p => ?_)
  simp only [pairMass, posIndex, Finset.mul_sum]
  exact Finset.sum_comm

theorem latentExpect_posIndex_nonneg (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ) (hw : ∀ n, 0 ≤ w n) :
    0 ≤ latentExpect w N posIndex :=
  tsum_nonneg fun p => pairMass_nonneg w N hw posIndex_nonneg p.1 p.2

/-- **`eq:mixture-strict-entropy-gap`** in the printed normalization, for every finite-entropy
countable cosine-power mixture `ρ = ∑ w_n ⊗_i h_{N_n,i}` (a.e.):
`Ent(ρ) - d c_d ‖ρ‖²_{Ḣ^{-d/2}} ≥ (3 / (2200 d)) ∑_i P(L_i ≥ 1)`.
This is `Section3.mixture_energy_gap` (the Lean inequality is the printed one multiplied by `2`)
with `γ` taken to the countable limit `E ∑_i 1_{L_i ≥ 1}` of the partial latent masses. -/
theorem mixture_strict_entropy_gap (hd2 : 2 ≤ d) (hd10 : d ≤ 10) (ρ : ProbabilityDensity d)
    (hρ : ρ.FiniteEntropy) (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ) (hw : ∀ n, 0 ≤ w n)
    (hm : HasSum w 1)
    (he : ρ.value =ᵐ[torusMeasure d] Legacy.BecknerOnofri.CosineMixtureApproximation.rho w N) :
    spectralEnergy ρ ≠ ⊤ ∧
      3 / (2200 * (d : ℝ)) * ∑ i, latentProb w N i ≤
        (torusEntropy ρ.value).toReal -
          (d : ℝ) * kernelConstant d * (negSobolevEnergy ρ.value).toReal := by
  have hd0 : 0 < d := by omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
  have hs : Summable w := hm.summable
  set T := latentExpect w N posIndex with hT
  have htend := tendsto_latAvg w N hw hs (F := posIndex) (C := (d : ℝ)) posIndex_nonneg posIndex_le
  have hkey : ∀ ε : ℝ, 0 < ε →
      spectralEnergy ρ ≠ ⊤ ∧
      2 * Legacy.BecknerOnofri.endpointConstant d * (spectralEnergy ρ).toReal +
        (3 / (1100 * (d : ℝ))) * (T - ε) ≤ 2 * entropy ρ := by
    intro ε hε
    refine mixture_energy_gap hd2 hd10 ρ hρ w N hw hm he (T - ε) ?_
    exact ((tendsto_order.1 htend).1 (T - ε) (by linarith)).mono fun m h => h.le
  obtain ⟨hfin, -⟩ := hkey 1 one_pos
  refine ⟨hfin, ?_⟩
  have hc : 0 < 3 / (1100 * (d : ℝ)) := by positivity
  have hE := energy_toReal_eq hd0 ρ
  have hent := entropy_eq_toReal_torusEntropy ρ hρ
  have hle : ∀ ε : ℝ, 0 < ε → (3 / (1100 * (d : ℝ))) * T ≤
      2 * ((torusEntropy ρ.value).toReal -
        (d : ℝ) * kernelConstant d * (negSobolevEnergy ρ.value).toReal) +
        (3 / (1100 * (d : ℝ))) * ε := by
    intro ε hε
    have := (hkey ε hε).2
    rw [hent] at this
    rw [hE]
    nlinarith
  have hfinal : (3 / (1100 * (d : ℝ))) * T ≤
      2 * ((torusEntropy ρ.value).toReal -
        (d : ℝ) * kernelConstant d * (negSobolevEnergy ρ.value).toReal) := by
    by_contra hcon
    push Not at hcon
    set R := 2 * ((torusEntropy ρ.value).toReal -
        (d : ℝ) * kernelConstant d * (negSobolevEnergy ρ.value).toReal)
    have hpos : 0 < ((3 / (1100 * (d : ℝ))) * T - R) / (2 * (3 / (1100 * (d : ℝ)))) := by
      apply div_pos (by linarith) (by positivity)
    have := hle _ hpos
    have hne : (3 / (1100 * (d : ℝ))) * (((3 / (1100 * (d : ℝ))) * T - R) /
        (2 * (3 / (1100 * (d : ℝ))))) = ((3 / (1100 * (d : ℝ))) * T - R) / 2 := by
      field_simp
    rw [hne] at this
    linarith
  have hsum : ∑ i, latentProb w N i = T := (latentExpect_posIndex w N hw hs).symm
  rw [hsum]
  have : 3 / (2200 * (d : ℝ)) * T = (3 / (1100 * (d : ℝ))) * T / 2 := by
    field_simp; ring
  rw [this]
  linarith

/-- First hypothesis of Lemma 3.1 from the printed strict gap: the right side of
`eq:mixture-strict-entropy-gap` is nonnegative. -/
theorem mixtureInequality_printed (hd2 : 2 ≤ d) (hd10 : d ≤ 10) : MixtureInequality d := by
  intro ρ hρ hmix
  obtain ⟨w, N, hw, hm, he⟩ := hmix
  have he' : ρ.value =ᵐ[torusMeasure d] Legacy.BecknerOnofri.CosineMixtureApproximation.rho w N := he
  obtain ⟨-, h⟩ := mixture_strict_entropy_gap hd2 hd10 ρ hρ w N hw hm he'
  have hs : Summable w := hm.summable
  have h0 : 0 ≤ ∑ i, latentProb w N i := by
    rw [← latentExpect_posIndex w N hw hs]
    exact latentExpect_posIndex_nonneg w N hw
  have hd : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  unfold EntropyBound
  have : 0 ≤ 3 / (2200 * (d : ℝ)) * ∑ i, latentProb w N i := by positivity
  linarith

/-- Second hypothesis of Lemma 3.1: for a nonuniform mixture some component has `w_a > 0` and
`N_a ≠ 0`, so `∑_i P(L_i ≥ 1) ≥ w_a² P(L = N_a | N_a, N_a) > 0`. -/
theorem mixtureStrictness_printed (hd2 : 2 ≤ d) (hd10 : d ≤ 10) : MixtureStrictness d := by
  intro ρ hρ hmix hnon
  obtain ⟨w, N, hw, hm, he⟩ := hmix
  have he' : ρ.value =ᵐ[torusMeasure d] Legacy.BecknerOnofri.CosineMixtureApproximation.rho w N := he
  have hs : Summable w := hm.summable
  have hd0 : 0 < d := by omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
  have hcomp : ∃ a, 0 < w a ∧ N a ≠ 0 := by
    by_contra hno
    push Not at hno
    apply hnon
    filter_upwards [he'] with x hx
    rw [hx]
    exact rho_uniform_of_no_component w N hw hm hno x
  obtain ⟨a, ha, hNa⟩ := hcomp
  have hγpos : 0 < w a * w a * latentWeight (N a) (N a) (N a) :=
    mul_pos (mul_pos ha ha) (latentWeight_self_pos' _)
  have hlow : w a * w a * latentWeight (N a) (N a) (N a) ≤ ∑ i, latentProb w N i := by
    rw [← latentExpect_posIndex w N hw hs]
    exact (posMass_lower (range (a + 1)) w N (fun a _ => hw a) (mem_range.mpr (by omega)) hNa).trans
      (latAvg_le_latentExpect w N hw hs posIndex_nonneg posIndex_le _)
  obtain ⟨-, h⟩ := mixture_strict_entropy_gap hd2 hd10 ρ hρ w N hw hm he'
  unfold EntropyStrict
  have : 0 < 3 / (2200 * (d : ℝ)) * ∑ i, latentProb w N i :=
    mul_pos (by positivity) (lt_of_lt_of_le hγpos hlow)
  linarith

/-- **`prop:equality`** (Proposition 3.7), as printed: for `2 ≤ d ≤ 10`, equality in
`eq:collapse-entropy-full` holds only for the uniform density, and equality in the dual potential
inequality, for `u ∈ H^{d/2}`, holds only for constants.  Proof as printed: the strict mixture gap
`mixture_strict_entropy_gap` (through `mixtureInequality_printed`, `mixtureStrictness_printed`) and
Lemma `lem:collapse-conditional-reduction` (`Section3.lemma_3_1`). -/
theorem prop_equality_printed (hd2 : 2 ≤ d) (hd10 : d ≤ 10) :
    (∀ ρ : ProbabilityDensity d, ρ.FiniteEntropy → EntropyEquality d ρ →
      ρ.value =ᵐ[torusMeasure d] fun _ => 1) ∧
    (∀ u : Torus d → ℝ, InCriticalSobolev u →
      logPartition u = ((collapseCoefficient d * potentialEnergy u : ℝ) : EReal) →
        ∃ c : ℝ, u =ᵐ[torusMeasure d] fun _ => c) := by
  obtain ⟨-, hdens, -, -, hpot⟩ :=
    lemma_3_1 hd2 (mixtureInequality_printed hd2 hd10) (mixtureStrictness_printed hd2 hd10)
  exact ⟨hdens, hpot⟩

#print axioms mixture_strict_entropy_gap
#print axioms mixtureInequality_printed
#print axioms mixtureStrictness_printed
#print axioms prop_equality_printed

end BecknerOnofri.V2.Reaudit.Mixtures
