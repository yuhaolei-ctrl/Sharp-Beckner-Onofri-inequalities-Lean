module

public import BecknerOnofri.V2.FiniteState.FamilyIdentities
public import BecknerOnofri.V2.FiniteState.JetCalculus

@[expose] public section

/-!
# Explicit family: second-order jets of `a`, `λ`, `ω` and of the ratios `p_j(t)/b_j`

Source: Appendix A.3, "Behavior at zero": `a = t + O(t^10)`, `λ = O(t^10)`,
`ω = t²/31 + O(t⁴)` and `p_j/b_j = 1 + 12 x_j t + 66 (32/31) A_{2,j} t² + O(t³)`
(`d12-spin-eq:pexpansion`).  The printed expansions of `a`, `λ`, `ω` are proved as
`famBias_sub_isBigO_ten`, `famLam_isBigO_ten`, `famOmega_sub_isBigO_four`; the jets below
(remainder `O(t³)`, which is all that is used) are derived from them.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter Topology Asymptotics
open scoped BigOperators
namespace BecknerOnofri.V2.FiniteState
open BecknerOnofri.HighDim.Spin

/-- Printed (Appendix A.3, "Behavior at zero"): `a(t) = t + O(t¹⁰)` (exact:
`a(t) - t = -(9/2) t¹⁰ (1 - t)`). -/
theorem famBias_sub_isBigO_ten : (fun t => famBias t - t) =O[𝓝 0] fun t : ℝ => t ^ 10 := by
  have h : (fun t : ℝ => famBias t - t) = fun t : ℝ => -(9 / 2) * (t ^ 10 * (1 - t)) := by
    funext t; unfold famBias famL; ring
  rw [h]
  have h1 : (fun t : ℝ => t ^ 10 * (1 - t)) =O[𝓝 0] fun t : ℝ => t ^ 10 := by
    have hb : (fun t : ℝ => 1 - t) =O[𝓝 0] fun _ : ℝ => (1 : ℝ) :=
      Filter.Tendsto.isBigO_one ℝ (c := 1 - 0) ((by fun_prop : Continuous fun t : ℝ => 1 - t).tendsto 0)
    simpa using (isBigO_refl (fun t : ℝ => t ^ 10) (𝓝 0)).mul hb
  exact h1.const_mul_left _

/-- Printed: `λ(t) = O(t¹⁰)`. -/
theorem famLam_isBigO_ten : famLam =O[𝓝 0] fun t : ℝ => t ^ 10 := by
  have hc : ContinuousAt (fun t : ℝ => (1 + famL t)⁻¹) 0 := by
    apply ContinuousAt.inv₀
    · unfold famL; fun_prop
    · simp [famL]
  have hb : (fun t : ℝ => (1 + famL t)⁻¹) =O[𝓝 0] fun _ : ℝ => (1 : ℝ) :=
    Filter.Tendsto.isBigO_one ℝ (c := (1 + famL 0)⁻¹) hc.tendsto
  have h1 : famL =O[𝓝 0] fun t : ℝ => t ^ 10 := by
    have : famL = fun t : ℝ => (9 / 2) * t ^ 10 := by funext t; rfl
    rw [this]
    exact (isBigO_refl (fun t : ℝ => t ^ 10) (𝓝 0)).const_mul_left _
  have := h1.mul hb
  refine this.congr' ?_ ?_
  · exact Filter.Eventually.of_forall fun t => by simp [famLam, div_eq_mul_inv]
  · exact Filter.Eventually.of_forall fun t => by simp

/-- The second-order jet of `a` is the printed expansion `a = t + O(t¹⁰)` truncated to `O(t³)`. -/
theorem famBias_jet : Jet2 famBias 0 1 0 := by
  unfold Jet2
  refine (famBias_sub_isBigO_ten.trans (isBigO_pow_pow (by norm_num : 3 ≤ 10))).congr_left ?_
  intro t; ring

/-- `λ = O(t³)`, from the printed `λ = O(t¹⁰)`. -/
theorem famLam_isBigO : famLam =O[𝓝 0] fun t : ℝ => t ^ 3 :=
  famLam_isBigO_ten.trans (isBigO_pow_pow (by norm_num : 3 ≤ 10))

theorem famLam_jet : Jet2 famLam 0 0 0 := Jet2.of_isBigO famLam_isBigO

/-- The denominator of `ω` is positive near zero (it equals `31` at `t = 0`). -/
def famOmegaDen (t : ℝ) : ℝ := famP (t ^ 2) * (1 - t) + t ^ 4 / 10

theorem famOmegaDen_zero : famOmegaDen 0 = 31 := by simp [famOmegaDen, famP]

/-- Printed: `ω(t) = t²/31 + O(t⁴)`; the exact identity `ω(t) - t²/31 = t⁴ Q(t)` with `Q`
continuous at `0` underlies it. -/
theorem famOmega_sub_isBigO_four :
    (fun t => famOmega t - t ^ 2 / 31) =O[𝓝 0] fun t : ℝ => t ^ 4 := by
  have hcont : Continuous famOmegaDen := by unfold famOmegaDen famP; fun_prop
  set Q : ℝ → ℝ := fun t => ((1 - t) * (32 - 12 * t ^ 4) - t ^ 2 / 10) / (31 * famOmegaDen t)
    with hQ
  have hQc : ContinuousAt Q 0 := by
    apply ContinuousAt.div
    · fun_prop
    · exact (continuous_const.mul hcont).continuousAt
    · rw [famOmegaDen_zero]; norm_num
  have hQb : Q =O[𝓝 0] fun _ : ℝ => (1 : ℝ) := Filter.Tendsto.isBigO_one ℝ (c := Q 0) hQc.tendsto
  have hne : ∀ᶠ t in 𝓝 (0 : ℝ), famOmegaDen t ≠ 0 := by
    have : Tendsto famOmegaDen (𝓝 0) (𝓝 31) := by
      simpa [famOmegaDen_zero] using hcont.tendsto 0
    exact this.eventually_ne (by norm_num)
  have h4 : (fun t : ℝ => t ^ 4 * Q t) =O[𝓝 0] fun t : ℝ => t ^ 4 := by
    simpa using (isBigO_refl (fun t : ℝ => t ^ 4) (𝓝 0)).mul hQb
  refine h4.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [hne] with t ht
  have e : famOmega t = t ^ 2 * (1 - t) / famOmegaDen t := rfl
  simp only [hQ, e]
  field_simp
  simp only [famOmegaDen, famP]
  ring

/-- The second-order jet of `ω` is the printed expansion `ω = t²/31 + O(t⁴)` truncated to `O(t³)`. -/
theorem famOmega_jet : Jet2 famOmega 0 0 (1 / 31) := by
  unfold Jet2
  refine (famOmega_sub_isBigO_four.trans (isBigO_pow_pow (by norm_num : 3 ≤ 4))).congr_left ?_
  intro t; ring

theorem famNu_div_reference (t : ℝ) (j : Count) :
    famNu t j / reference j =
      (∏ k ∈ Finset.range j.val, (1 + famBias t + 2 * (k : ℝ) * famOmega t)) *
      (∏ k ∈ Finset.range (12 - j.val), (1 - famBias t + 2 * (k : ℝ) * famOmega t)) *
      (∏ k ∈ Finset.range 12, (1 + (k : ℝ) * famOmega t))⁻¹ := by
  have hj : j.val ≤ 12 := Nat.lt_succ_iff.mp j.isLt
  have e1 : ∏ k ∈ Finset.range j.val, ((1 + famBias t) / 2 + (k : ℝ) * famOmega t) =
      (1 / 2) ^ j.val * ∏ k ∈ Finset.range j.val, (1 + famBias t + 2 * (k : ℝ) * famOmega t) := by
    rw [← prod_range_const_mul]
    exact Finset.prod_congr rfl (fun k _ => by ring)
  have e2 : ∏ k ∈ Finset.range (12 - j.val), ((1 - famBias t) / 2 + (k : ℝ) * famOmega t) =
      (1 / 2) ^ (12 - j.val) *
        ∏ k ∈ Finset.range (12 - j.val), (1 - famBias t + 2 * (k : ℝ) * famOmega t) := by
    rw [← prod_range_const_mul]
    exact Finset.prod_congr rfl (fun k _ => by ring)
  have hC : ((12).choose j.val : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hj).ne'
  have hpow : ((1 : ℝ) / 2) ^ j.val * (1 / 2) ^ (12 - j.val) = 1 / 4096 := by
    rw [← pow_add, show j.val + (12 - j.val) = 12 by omega]; norm_num
  have key : ∀ (C A B Dn h1 h2 : ℝ), C ≠ 0 → h1 * h2 = 1 / 4096 →
      C * (h1 * A) * (h2 * B) / Dn / (C / 4096) = A * B * Dn⁻¹ := by
    intro C A B Dn h1 h2 hC hh
    have : C * (h1 * A) * (h2 * B) = C * A * B * (h1 * h2) := by ring
    rw [this, hh]
    simp only [div_eq_mul_inv, mul_inv]
    have : (C⁻¹ : ℝ) * C = 1 := inv_mul_cancel₀ hC
    calc C * A * B * (1 / 4096) * Dn⁻¹ * (C⁻¹ * 4096⁻¹⁻¹)
        = (C * C⁻¹) * A * B * Dn⁻¹ * (1 / 4096 * 4096⁻¹⁻¹) := by ring
      _ = A * B * Dn⁻¹ := by rw [mul_inv_cancel₀ hC]; norm_num
  unfold famNu
  rw [e1, e2, reference_eq]
  exact key _ _ _ _ _ _ hC hpow

theorem sum_range_cast (n : ℕ) : ∑ k ∈ Finset.range n, (k : ℝ) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- `12 x_j = 2j - 12`. -/
def famEll (j : Count) : ℝ := 2 * (j.val : ℝ) - 12
/-- `66 (32/31) A_{2,j} = (32/31)(2 (j-6)² - 6)`. -/
def famD2 (j : Count) : ℝ := (32 / 31) * (2 * ((j.val : ℝ) - 6) ^ 2 - 6)

theorem famNu_ratio_jet (j : Count) :
    Jet2 (fun t => famNu t j / reference j) 1 (famEll j) (famD2 j) := by
  have hj : j.val ≤ 12 := Nat.lt_succ_iff.mp j.isLt
  have hA : ∀ k : ℕ, Jet2 (fun t => 1 + famBias t + 2 * (k : ℝ) * famOmega t) 1 1
      (2 * (k : ℝ) / 31) := by
    intro k
    have := ((Jet2.const 1).add famBias_jet).add (famOmega_jet.const_mul (2 * (k : ℝ)))
    refine this.coeff (by ring) (by ring) (by ring)
  have hB : ∀ k : ℕ, Jet2 (fun t => 1 - famBias t + 2 * (k : ℝ) * famOmega t) 1 (-1)
      (2 * (k : ℝ) / 31) := by
    intro k
    have := ((Jet2.const 1).sub famBias_jet).add (famOmega_jet.const_mul (2 * (k : ℝ)))
    refine this.coeff (by ring) (by ring) (by ring)
  have hD : ∀ k : ℕ, Jet2 (fun t => 1 + (k : ℝ) * famOmega t) 1 0 ((k : ℝ) / 31) := by
    intro k
    have := (Jet2.const 1).add (famOmega_jet.const_mul (k : ℝ))
    refine this.coeff (by ring) (by ring) (by ring)
  have PA := Jet2.prod_range j.val (φ := fun k t => 1 + famBias t + 2 * (k : ℝ) * famOmega t)
    (u := 1) (v := fun k => 2 * (k : ℝ) / 31) (fun k _ => hA k)
  have PB := Jet2.prod_range (12 - j.val) (φ := fun k t => 1 - famBias t + 2 * (k : ℝ) * famOmega t)
    (u := -1) (v := fun k => 2 * (k : ℝ) / 31) (fun k _ => hB k)
  have PD := Jet2.prod_range 12 (φ := fun k t => 1 + (k : ℝ) * famOmega t)
    (u := 0) (v := fun k => (k : ℝ) / 31) (fun k _ => hD k)
  have PDi := PD.inv_one
  have H := (PA.mul PB).mul PDi
  have hs1 : ∑ k ∈ Finset.range j.val, 2 * (k : ℝ) / 31 = (j.val : ℝ) * ((j.val : ℝ) - 1) / 31 := by
    rw [← Finset.sum_div, ← Finset.mul_sum, sum_range_cast]; ring
  have hs2 : ∑ k ∈ Finset.range (12 - j.val), 2 * (k : ℝ) / 31 =
      ((12 : ℝ) - j.val) * ((11 : ℝ) - j.val) / 31 := by
    rw [← Finset.sum_div, ← Finset.mul_sum, sum_range_cast, Nat.cast_sub hj]; push_cast; ring
  have hs3 : ∑ k ∈ Finset.range 12, (k : ℝ) / 31 = 66 / 31 := by
    rw [← Finset.sum_div, sum_range_cast]; norm_num
  have hc : ((12 - j.val : ℕ) : ℝ) = 12 - (j.val : ℝ) := by rw [Nat.cast_sub hj]; push_cast; ring
  rw [hs1] at H
  rw [hs2, hc] at H
  rw [hs3] at H
  refine (H.congr (fun t => ?_)).coeff (by ring) ?_ ?_
  · rw [famNu_div_reference]
  · unfold famEll; push_cast; ring
  · unfold famD2; push_cast; ring

/-- `p_j(t)/b_j = 1 + 12 x_j t + 66 (32/31) A_{2,j} t² + O(t³)` (`d12-spin-eq:pexpansion`). -/
theorem famLaw_ratio_jet (j : Count) :
    Jet2 (fun t => famLaw t j / reference j) 1 (famEll j) (famD2 j) := by
  have h1 : Jet2 (fun t => 1 - famLam t) 1 0 0 :=
    ((Jet2.const 1).sub famLam_jet).coeff (by ring) (by ring) (by ring)
  have h2 := h1.mul (famNu_ratio_jet j)
  have h3 : Jet2 (fun t => ((if j.val = 12 then (1 : ℝ) else 0) / reference j) * famLam t) 0 0 0 :=
    (famLam_jet.const_mul ((if j.val = 12 then (1 : ℝ) else 0) / reference j)).coeff
      (by ring) (by ring) (by ring)
  have h4 := h2.add h3
  refine (h4.congr (fun t => ?_)).coeff (by ring) (by ring) (by ring)
  unfold famLaw
  ring

end BecknerOnofri.V2.FiniteState
