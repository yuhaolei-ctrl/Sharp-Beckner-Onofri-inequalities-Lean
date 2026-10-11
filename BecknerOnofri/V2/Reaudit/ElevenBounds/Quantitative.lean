module

public import BecknerOnofri.V2.Reaudit.ElevenBounds.LatentGap
public import BecknerOnofri.V2.Eleven.Estimates

@[expose] public section

/-! # S024, steps 1-3: the quantitative gap and the non-strict lower bound `3543/200 ≤ β_gm(11)`

This module holds the part of `d11:thm:interval` that precedes coexistence in the printed proof
(`d11:eq:mixture-gap`, strictness for nonuniform mixtures, uniqueness of the uniform minimizer for
`0 ≤ β ≤ 3543/200`, the **non-strict** bound `3543/200 ≤ β_gm`).  It does not import
`ElevenCoexistence`, the upper bound or any module downstream of `ElevenTransitionZeroSet`, so that
`HighDim.Eleven.transition_lower` (the non-strict bound consumed by coexistence) can be proved from it.
The remaining steps (4: upper bound, 5: strict bound after coexistence) are in `Interval.lean`. -/

noncomputable section
open Finset Filter MeasureTheory
open scoped BigOperators ENNReal Topology

namespace BecknerOnofri.V2.Reaudit.ElevenBounds
open BecknerOnofri.HighDim BecknerOnofri.V2.Section3
open Legacy.D10 (latentBox latentWeight latentWeight_nonneg sum_latentWeight)
open Legacy.BecknerOnofri

variable {d : ℕ}

/-! ## Positivity of the latent mass of a nonuniform mixture -/

theorem posMass_le_latentMass (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ) (hw : ∀ n, 0 ≤ w n) (hm : HasSum w 1)
    (m : ℕ) : posMass (range m) w N ≤ latentMass w N :=
  Monotone.ge_of_tendsto (f := fun m => posMass (range m) w N)
    (fun _ _ h => posMass_mono w N hw h) (tendsto_posMass w N hw hm) m

/-- A component with positive weight and nonzero index gives the latent mass the lower bound
`w_a² P(L = N_a | N = M = N_a)`. -/
theorem latentMass_lower (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ) (hw : ∀ n, 0 ≤ w n) (hm : HasSum w 1)
    {a : ℕ} (hNa : N a ≠ 0) :
    w a * w a * latentWeight (N a) (N a) (N a) ≤ latentMass w N :=
  (posMass_lower (range (a + 1)) w N (fun a _ => hw a) (mem_range.2 (Nat.lt_succ_self a)) hNa).trans
    (posMass_le_latentMass w N hw hm (a + 1))

theorem latentProb_nonneg (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ) (i : Fin d) : 0 ≤ latentProb w N i :=
  ENNReal.toReal_nonneg

/-- The printed step "some `i` satisfies `P(N_i ≥ 1) > 0`; independence of `N` and `M` and the
hypergeometric law give `P(L_i ≥ 1) > 0`": for a nonuniform mixture (a component of positive weight
and nonzero index) some `P(L_i ≥ 1)` is positive. -/
theorem exists_pos_latentProb (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ) (hw : ∀ n, 0 ≤ w n) (hm : HasSum w 1)
    {a : ℕ} (ha : 0 < w a) (hNa : N a ≠ 0) : ∃ i, 0 < latentProb w N i := by
  by_contra hno
  push Not at hno
  have hle : ∑ i, latentProb w N i ≤ 0 := sum_nonpos fun i _ => hno i
  rw [sum_latentProb_eq w N hw hm] at hle
  have := latentMass_lower w N hw hm hNa
  have hpos : 0 < w a * w a * latentWeight (N a) (N a) (N a) :=
    mul_pos (mul_pos ha ha) (latentWeight_self_pos' _)
  linarith

/-! ## Strictness for nonuniform mixtures, from the quantitative gap -/

/-- A countable cosine-power mixture all of whose positive-weight components have index `0` is
uniform; hence a nonuniform one has a component of positive weight and nonzero index. -/
theorem exists_component_of_nonuniform (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ) (hw : ∀ n, 0 ≤ w n)
    (hm : HasSum w 1) (hnon : ¬ (fun x => CosineMixtureApproximation.rho w N x) =ᵐ[torusMeasure d]
      fun _ => (1 : ℝ)) : ∃ a, 0 < w a ∧ N a ≠ 0 := by
  by_contra hno
  push Not at hno
  apply hnon
  have hall : ∀ n, 0 < w n → N n = 0 := fun n hn => by
    by_contra hne; exact absurd (hno n hn) (by simpa using hne)
  exact Filter.Eventually.of_forall fun x => rho_uniform_of_no_component w N hw hm hall x

/-- **`d11:eq:mixture-gap`, strict for nonuniform mixtures.**  Every nonuniform finite-entropy
countable cosine-power mixture has `E_{β_0}(ρ) > 0`; here no smoothness or positivity of `ρ` is used. -/
theorem efree_pos_of_nonuniform_mixture (ρ : ProbabilityDensity 11) (hρ : ρ.FiniteEntropy)
    (hmix : IsCountableCosineMixture ρ) (hnon : ¬ ρ.value =ᵐ[torusMeasure 11] fun _ => 1) :
    0 < Eleven.Efree Eleven.beta0 ρ := by
  obtain ⟨w, N, hw, hm, he⟩ := hmix
  have he' : ρ.value =ᵐ[torusMeasure 11] CosineMixtureApproximation.rho w N := he
  have hnon' : ¬ (fun x => CosineMixtureApproximation.rho w N x) =ᵐ[torusMeasure 11]
      fun _ => (1 : ℝ) := fun h => hnon (he'.trans h)
  obtain ⟨a, ha, hNa⟩ := exists_component_of_nonuniform w N hw hm hnon'
  obtain ⟨i, hi⟩ := exists_pos_latentProb w N hw hm ha hNa
  have hgap := mixture_gap_eleven ρ hρ w N hw hm he'
  have : 0 < ∑ i, latentProb w N i :=
    lt_of_lt_of_le hi (single_le_sum (f := fun i => latentProb w N i)
      (fun i _ => latentProb_nonneg w N i) (mem_univ i))
  linarith

/-- The hypothesis of `V2.Eleven.uniform_unique_of_gap`, proved through the quantitative gap. -/
theorem smoothMixtureGap11_quantitative : Eleven.SmoothMixtureGap11 :=
  fun ρ hρ _ _ hmix hnon => efree_pos_of_nonuniform_mixture ρ hρ hmix hnon

/-! ## Uniqueness through `17.715` and the non-strict lower bound (no coexistence) -/

/-- **Uniqueness of the uniform minimizer for `0 ≤ β ≤ 3543/200`** (`d11:thm:interval`, second
sentence), through the quantitative gap. -/
theorem uniform_unique_quantitative (β : ℝ) (hβ : 0 ≤ β) (hβ0 : β ≤ Eleven.beta0)
    (ρ : ProbabilityDensity 11) (hρ : ρ.FiniteEntropy) :
    IsGlobalMinimizer β ρ ↔ ρ.value =ᵐ[torusMeasure 11] (fun _ => 1) :=
  Eleven.uniform_unique_of_gap smoothMixtureGap11_quantitative β hβ hβ0 ρ hρ

/-- **The non-strict lower bound** `3543/200 ≤ β_gm(11)` through the quantitative gap.  It does not use
coexistence (nor the upper bound). -/
theorem beta0_le_globalTransition_quantitative : Eleven.beta0 ≤ VariationalCurves.globalTransition 11 :=
  Eleven.beta0_le_globalTransition smoothMixtureGap11_quantitative

/-- `P_11(β) = 0` for `0 ≤ β ≤ 3543/200`, through the quantitative gap (no coexistence, no legacy
endpoint theorem). -/
theorem pressure_zero_quantitative (β : ℝ) (hβ : 0 ≤ β) (hβ0 : β ≤ Eleven.beta0) :
    pressure 11 β = 0 :=
  Eleven.pressure_zero_of_gap smoothMixtureGap11_quantitative β hβ hβ0

end BecknerOnofri.V2.Reaudit.ElevenBounds
