module

public import BecknerOnofri.V2.Reaudit.ElevenBounds.GapParam
public import BecknerOnofri.V2.Eleven.UniformUnique

@[expose] public section

/-! # S024, step 2: the latent law `L` and the dimension-eleven quantitative mixture gap
(`d11:eq:mixture-gap`)

For a countable mixture `ρ = ∑_a w_a h_{N_a}` (`eq:mixture`) the latent vector `L` of
`subsec:mixture-transfer` is formed by drawing `N` and `M` independently from the weights `w` and, conditionally
on `(N, M)`, drawing the coordinates `L_i` independently with the hypergeometric laws
`P(L_i = l | N_i = n, M_i = m) = C(n,l) C(m,l) / C(n+m,n)` (`eq:hypergeometric-law`).  `latentLaw w N` is the
law of `L`, a probability measure on `ℕ^d`; `latentProb w N i = P(L_i ≥ 1)`.

Main result (`mixture_gap_eleven`, `d11:eq:mixture-gap`): for `d = 11`, `β_0 = 3543/200`, every finite-entropy
countable mixture satisfies

  `(1/44000) ∑_{i=1}^{11} P(L_i ≥ 1) ≤ E_{β_0}(ρ)`, where `E_{β_0}(ρ) = Ent(ρ) - (β_0/(2β_s)) (2π)^{11} ‖ρ‖²`.

The scalar input is `d11:prop:scalar` (`V2.Eleven.scalar_gap`, margin `1/2000`), the mechanism is the
parametrized `mixture_energy_gap_param` of `GapParam.lean`; `1/44000 = (1/2000)/(2 · 11)`.
Coexistence is not used anywhere in this file. -/

noncomputable section
open Finset Filter MeasureTheory
open scoped BigOperators ENNReal Topology

namespace BecknerOnofri.V2.Reaudit.ElevenBounds
open BecknerOnofri.HighDim BecknerOnofri.V2.Section3
open Legacy.D10 (latentBox latentWeight latentWeight_nonneg sum_latentWeight)
open Legacy.TorusEndpoint (densityFourier)
open Legacy.BecknerOnofri

variable {d : ℕ}

/-! ## The law of the latent vector -/

/-- The latent index vector `T(L) = ∑_i 1_{L_i ≥ 1}`. -/
def posCount (L : Fin d → ℕ) : ℝ := ∑ i, (if 1 ≤ L i then (1 : ℝ) else 0)

theorem posCount_nonneg (L : Fin d → ℕ) : 0 ≤ posCount L :=
  sum_nonneg fun i _ => by split_ifs <;> norm_num

theorem posCount_le (L : Fin d → ℕ) : posCount L ≤ d := by
  unfold posCount
  calc _ ≤ ∑ _i : Fin d, (1 : ℝ) := sum_le_sum fun i _ => by split_ifs <;> norm_num
    _ = d := by simp

/-- The conditional law of `L` given `(N, M) = (n, m)`: `∑_{ℓ ∈ box(n)} ∏_i h(n_i, m_i, ℓ_i) δ_ℓ`
(`eq:hypergeometric-law`, coordinatewise independent). -/
def condLatent (n m : Fin d → ℕ) : Measure (Fin d → ℕ) :=
  ∑ L ∈ latentBox n, ENNReal.ofReal (latentWeight n m L) • Measure.dirac L

/-- **The law of the latent vector `L`**: `N, M` independent with the weights `w` (the component `a`
having the index vector `N a`), and `L | (N, M)` as in `condLatent`. -/
def latentLaw (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ) : Measure (Fin d → ℕ) :=
  Measure.sum fun p : ℕ × ℕ => ENNReal.ofReal (w p.1 * w p.2) • condLatent (N p.1) (N p.2)

/-- `P(L_i ≥ 1)`. -/
def latentProb (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ) (i : Fin d) : ℝ :=
  (latentLaw w N).real {L | 1 ≤ L i}

theorem condLatent_apply (n m : Fin d → ℕ) (S : Set (Fin d → ℕ)) :
    condLatent n m S = ∑ L ∈ latentBox n, ENNReal.ofReal (latentWeight n m L) * S.indicator 1 L := by
  have hS : MeasurableSet S := S.to_countable.measurableSet
  unfold condLatent
  rw [Measure.coe_finsetSum, Finset.sum_apply]
  refine sum_congr rfl fun L _ => ?_
  rw [Measure.smul_apply, Measure.dirac_apply' _ hS, smul_eq_mul]

theorem indicator_one_ne_top (S : Set (Fin d → ℕ)) (L : Fin d → ℕ) : S.indicator (1 : (Fin d → ℕ) → ℝ≥0∞) L ≠ ⊤ := by
  by_cases h : L ∈ S <;> simp [Set.indicator, h]

theorem condLatent_ne_top (n m : Fin d → ℕ) (S : Set (Fin d → ℕ)) : condLatent n m S ≠ ⊤ := by
  rw [condLatent_apply]
  exact ENNReal.sum_ne_top.2 fun L _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (indicator_one_ne_top _ _)

theorem condLatent_univ (n m : Fin d → ℕ) : condLatent n m Set.univ = 1 := by
  rw [condLatent_apply]
  simp only [Set.indicator_univ, Pi.one_apply, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun L _ => latentWeight_nonneg _ _ _), sum_latentWeight]
  simp

theorem latentLaw_apply (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ) (S : Set (Fin d → ℕ)) :
    latentLaw w N S = ∑' p : ℕ × ℕ, ENNReal.ofReal (w p.1 * w p.2) * condLatent (N p.1) (N p.2) S := by
  have hS : MeasurableSet S := S.to_countable.measurableSet
  unfold latentLaw
  rw [Measure.sum_apply _ hS]
  refine tsum_congr fun p => ?_
  rw [Measure.smul_apply, smul_eq_mul]

/-- The latent law is a probability measure when the weights are a probability vector. -/
theorem latentLaw_univ (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ) (hw : ∀ n, 0 ≤ w n) (hm : HasSum w 1) :
    latentLaw w N Set.univ = 1 := by
  rw [latentLaw_apply]
  simp only [condLatent_univ, mul_one]
  have hs : Summable fun p : ℕ × ℕ => w p.1 * w p.2 :=
    Summable.mul_of_nonneg hm.summable hm.summable hw hw
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun p => mul_nonneg (hw _) (hw _)) hs]
  have : (∑' p : ℕ × ℕ, w p.1 * w p.2) = 1 := by
    simpa using (hm.mul hm hs).tsum_eq
  simp [this]

theorem isProbabilityMeasure_latentLaw (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ) (hw : ∀ n, 0 ≤ w n)
    (hm : HasSum w 1) : IsProbabilityMeasure (latentLaw w N) :=
  ⟨latentLaw_univ w N hw hm⟩

/-! ## The mass of the positive latent indices -/

/-- The summand of `E ∑_i 1_{L_i ≥ 1}` for the pair `p = (a,b)` of components. -/
def posTerm (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ) (p : ℕ × ℕ) : ℝ :=
  w p.1 * w p.2 * ∑ L ∈ latentBox (N p.1), latentWeight (N p.1) (N p.2) L * posCount L

theorem posTerm_nonneg (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ) (hw : ∀ n, 0 ≤ w n) (p : ℕ × ℕ) :
    0 ≤ posTerm w N p :=
  mul_nonneg (mul_nonneg (hw _) (hw _))
    (sum_nonneg fun L _ => mul_nonneg (latentWeight_nonneg _ _ _) (posCount_nonneg L))

theorem posTerm_le (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ) (hw : ∀ n, 0 ≤ w n) (p : ℕ × ℕ) :
    posTerm w N p ≤ w p.1 * w p.2 * d := by
  unfold posTerm
  refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (hw _) (hw _))
  calc _ ≤ ∑ L ∈ latentBox (N p.1), latentWeight (N p.1) (N p.2) L * d :=
        sum_le_sum fun L _ => mul_le_mul_of_nonneg_left (posCount_le L) (latentWeight_nonneg _ _ _)
    _ = d := by rw [← sum_mul, sum_latentWeight, one_mul]

theorem summable_posTerm (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ) (hw : ∀ n, 0 ≤ w n) (hm : HasSum w 1) :
    Summable (posTerm w N) := by
  have hs : Summable fun p : ℕ × ℕ => w p.1 * w p.2 * (d : ℝ) :=
    (Summable.mul_of_nonneg hm.summable hm.summable hw hw).mul_right _
  exact Summable.of_nonneg_of_le (posTerm_nonneg w N hw) (posTerm_le w N hw) hs

/-- `∑_i P(L_i ≥ 1) = E ∑_i 1_{L_i ≥ 1}`, in the form of the full sum over pairs of components. -/
def latentMass (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ) : ℝ := ∑' p : ℕ × ℕ, posTerm w N p

/-- `P(L_i ≥ 1)` as the full series over pairs of components. -/
theorem latentProb_eq_tsum (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ) (hw : ∀ n, 0 ≤ w n) (hm : HasSum w 1)
    (i : Fin d) :
    latentProb w N i = ∑' p : ℕ × ℕ, w p.1 * w p.2 *
      ∑ L ∈ latentBox (N p.1), latentWeight (N p.1) (N p.2) L * (if 1 ≤ L i then (1 : ℝ) else 0) := by
  have := isProbabilityMeasure_latentLaw w N hw hm
  unfold latentProb
  rw [Measure.real, latentLaw_apply, ENNReal.tsum_toReal_eq]
  · refine tsum_congr fun p => ?_
    rw [condLatent_apply, ENNReal.toReal_mul, ENNReal.toReal_ofReal
      (mul_nonneg (hw _) (hw _)), ENNReal.toReal_sum]
    · congr 1
      refine sum_congr rfl fun L _ => ?_
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (latentWeight_nonneg _ _ _)]
      congr 1
      by_cases h : 1 ≤ L i <;> simp [Set.indicator, h]
    · intro L _
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (indicator_one_ne_top _ _)
  · intro p
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (condLatent_ne_top _ _ _)

/-- `∑_i P(L_i ≥ 1)` is the latent mass `E ∑_i 1_{L_i ≥ 1}`. -/
theorem sum_latentProb_eq (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ) (hw : ∀ n, 0 ≤ w n) (hm : HasSum w 1) :
    ∑ i, latentProb w N i = latentMass w N := by
  have hterm (i : Fin d) : Summable fun p : ℕ × ℕ => w p.1 * w p.2 *
      ∑ L ∈ latentBox (N p.1), latentWeight (N p.1) (N p.2) L * (if 1 ≤ L i then (1 : ℝ) else 0) := by
    refine Summable.of_nonneg_of_le (fun p => mul_nonneg (mul_nonneg (hw _) (hw _))
      (sum_nonneg fun L _ => mul_nonneg (latentWeight_nonneg _ _ _) (by split_ifs <;> norm_num)))
      (fun p => ?_) ((Summable.mul_of_nonneg hm.summable hm.summable hw hw).mul_right (1 : ℝ))
    have h1 : ∑ L ∈ latentBox (N p.1), latentWeight (N p.1) (N p.2) L *
        (if 1 ≤ L i then (1 : ℝ) else 0) ≤ 1 := by
      calc _ ≤ ∑ L ∈ latentBox (N p.1), latentWeight (N p.1) (N p.2) L * 1 :=
            sum_le_sum fun L _ => mul_le_mul_of_nonneg_left (by split_ifs <;> norm_num)
              (latentWeight_nonneg _ _ _)
        _ = 1 := by simp [sum_latentWeight]
    calc _ ≤ w p.1 * w p.2 * 1 := mul_le_mul_of_nonneg_left h1 (mul_nonneg (hw _) (hw _))
      _ = _ := by ring
  simp_rw [latentProb_eq_tsum w N hw hm]
  rw [← Summable.tsum_finsetSum fun i _ => hterm i]
  unfold latentMass
  refine tsum_congr fun p => ?_
  unfold posTerm posCount
  rw [← mul_sum]
  congr 1
  simp only [mul_sum]
  rw [Finset.sum_comm]

/-- `posMass` of the first `m` components is the partial sum over `range m × range m`. -/
theorem posMass_eq_sum (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ) (m : ℕ) :
    posMass (range m) w N = ∑ p ∈ range m ×ˢ range m, posTerm w N p := by
  unfold posMass latAvg posTerm
  rw [Finset.sum_product]
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun L _ => ?_
  unfold posCount
  ring

theorem tendsto_posMass (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ) (hw : ∀ n, 0 ≤ w n) (hm : HasSum w 1) :
    Tendsto (fun m => posMass (range m) w N) atTop (𝓝 (latentMass w N)) := by
  simp_rw [posMass_eq_sum]
  have hS := (summable_posTerm w N hw hm).hasSum
  refine hS.comp ?_
  refine Filter.tendsto_atTop_finset_of_monotone (f := fun m => range m ×ˢ range m)
    (fun m n hmn => product_subset_product (range_mono hmn) (range_mono hmn)) ?_
  intro p
  exact ⟨max p.1 p.2 + 1, mem_product.2 ⟨mem_range.2 (by omega), mem_range.2 (by omega)⟩⟩

theorem posMass_mono (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ) (hw : ∀ n, 0 ≤ w n) {m n : ℕ} (h : m ≤ n) :
    posMass (range m) w N ≤ posMass (range n) w N := by
  rw [posMass_eq_sum, posMass_eq_sum]
  exact sum_le_sum_of_subset_of_nonneg (product_subset_product (range_mono h) (range_mono h))
    (fun p _ _ => posTerm_nonneg w N hw p)

/-! ## The dimension-eleven scalar input -/

theorem binomialEnergy_zero (d : ℕ) : GaussianLattice.binomialEnergy d 0 = 0 := by
  rw [← HighDim.LowScalar.energy_eq_legacy]
  exact energy_zero d

/-- `d11:prop:scalar` (`d11:eq:gap`) in the form `ScalarGap 11 (β_0/β_s) (1/2000)`. -/
theorem scalarGap_eleven : ScalarGap 11 (Eleven.beta0 / spectralThreshold 11) (1 / 2000) := by
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [binomialEnergy_zero]
  · have h := Eleven.scalar_gap hn
    rw [HighDim.Eleven.ScalarFinite.scalarEnergy_eq_legacy] at h
    have h1 : (if 1 ≤ n then (1 : ℝ) else 0) = 1 := by simp; omega
    rw [h1, mul_one]
    have : ((11 : ℕ) : ℝ) = 11 := by norm_num
    rw [this]
    have e : Eleven.beta0 / spectralThreshold 11 * GaussianLattice.binomialEnergy 11 n =
        Eleven.beta0 / spectralThreshold 11 * GaussianLattice.binomialEnergy 11 n := rfl
    linarith

/-! ## `d11:eq:mixture-gap` -/

/-- **`d11:eq:mixture-gap`** (the quantitative latent-mass gap, dimension eleven).
For every finite-entropy countable cosine-power mixture `ρ = ∑_a w_a h_{N_a}` (`ρ` a.e. equal to
`rho w N`; the weights `w` are a probability vector),
`E_{β_0}(ρ) = Ent(ρ) - (β_0/(2β_s))(2π)^{11}‖ρ‖²_{Ḣ^{-11/2}} ≥ (1/44000) ∑_{i=1}^{11} P(L_i ≥ 1)`,
where `L` is the latent vector of `subsec:mixture-transfer` (law `latentLaw w N`). The proof needs neither
smoothness nor strict positivity of `ρ`, and does not use coexistence. -/
theorem mixture_gap_eleven (ρ : ProbabilityDensity 11) (hρ : ρ.FiniteEntropy)
    (w : ℕ → ℝ) (N : ℕ → Fin 11 → ℕ) (hw : ∀ n, 0 ≤ w n) (hm : HasSum w 1)
    (he : ρ.value =ᵐ[torusMeasure 11] CosineMixtureApproximation.rho w N) :
    (1 / 44000 : ℝ) * ∑ i : Fin 11, latentProb w N i ≤ Eleven.Efree Eleven.beta0 ρ := by
  have hd0 : 0 < 11 := by norm_num
  have hσ := Vocab.spectralThreshold_pos' (d := 11) hd0
  have hc : 0 < Eleven.beta0 / spectralThreshold 11 := by
    unfold Eleven.beta0; positivity
  have hmain (m0 : ℕ) : spectralEnergy ρ ≠ ⊤ ∧
      Eleven.beta0 / spectralThreshold 11 * (spectralEnergy ρ).toReal +
        ((1 / 2000 : ℝ) / ((11 : ℕ) : ℝ)) * posMass (range m0) w N ≤ 2 * entropy ρ :=
    mixture_energy_gap_param hd0 hc (by norm_num) scalarGap_eleven ρ hρ w N hw hm he _
      (Filter.eventually_atTop.2 ⟨m0, fun m hm' => posMass_mono w N hw hm'⟩)
  have hlim : Eleven.beta0 / spectralThreshold 11 * (spectralEnergy ρ).toReal +
        ((1 / 2000 : ℝ) / ((11 : ℕ) : ℝ)) * latentMass w N ≤ 2 * entropy ρ :=
    le_of_tendsto (((tendsto_posMass w N hw hm).const_mul _).const_add _)
      (Filter.Eventually.of_forall fun m => (hmain m).2)
  rw [← sum_latentProb_eq w N hw hm] at hlim
  have hkey := Vocab.kernelConstant_mul_negSobolevEnergy_toReal (d := 11) hd0 ρ
  have hent := (Vocab.entropy_eq_toReal_torusEntropy ρ hρ)
  unfold Eleven.Efree
  have e1 : Eleven.beta0 * Vocab.kernelConstant 11 / 2 * (Vocab.negSobolevEnergy ρ.value).toReal =
      Eleven.beta0 / 2 * ((spectralEnergy ρ).toReal / spectralThreshold 11) := by
    rw [← hkey]; ring
  rw [e1, ← hent]
  have e2 : Eleven.beta0 / 2 * ((spectralEnergy ρ).toReal / spectralThreshold 11) =
      (Eleven.beta0 / spectralThreshold 11 * (spectralEnergy ρ).toReal) / 2 := by ring
  rw [e2]
  have e3 : ((1 / 2000 : ℝ) / ((11 : ℕ) : ℝ)) = 2 / 44000 := by norm_num
  rw [e3] at hlim
  linarith

end BecknerOnofri.V2.Reaudit.ElevenBounds
