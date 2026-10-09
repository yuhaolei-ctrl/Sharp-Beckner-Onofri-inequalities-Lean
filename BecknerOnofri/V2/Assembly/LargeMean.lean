module

public import BecknerOnofri.V2.FiniteState.ExpBound
public import BecknerOnofri.V2.FiniteState.FamilyIdentities
public import BecknerOnofri.V2.FiniteState.FamilyDefs
public import BecknerOnofri.SpinAlgebra
public import BecknerOnofri.SpinProductDefinitions
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section

/-!
# The large-mean coarse estimate (`d12-spin-sec:large`, `eq:d12-spin-eq:largecoarse`, `largefinal`)

Source: the paragraph "Large means and completion of the proof" of the subsection
"The finite-state entropy inequality" (Proposition 5.12(ii)).  For `99/100 ≤ t ≤ 1` and every
`q ∈ 𝒫_t` (including the point mass at twelve when `t = 1`):
`F(q) + 12 ψ(t) ≥ 24 I_B(a) - Σ_s w_s + 12 ψ(a) > 3/100` with `a = 99/100`.

ROUTE DIFFERENCES (elementary, flagged in the report).
* The manuscript writes `Hr(q | b) = Hr(q | π(t)) + 12 I_B(t) ≥ 12 I_B(t)` for `t < 1` (treating
  `t = 1` by direct evaluation) and then uses monotonicity of `I_B`.  Here the same coarse bound is
  proved as `Hr(q | b) ≥ 12 I_B(a)` for every `0 ≤ a < 1` with `a ≤ t` directly from the finite Gibbs
  variational inequality with `H_j = log(π_a(j)/b_j)`; with `a = 99/100` this covers all
  `t ∈ [99/100, 1]` at once (no separate treatment of `t = 1`, no monotonicity of `I_B`).
* The numerical inputs `I_B(99/100) > 33/50` and `ψ(99/100) > 9/40` are proved from Mathlib's
  `log 2` bounds instead of the series `log((1+z)/(1-z)) > 2(z + z³/3 + z⁵/5)` and the exponential
  sum `Σ_{k≤8} (47/10)^k/k! > 100`; the bounds `33/50`, `9/40` are exactly the manuscript's.
* `Σ_s w_s < 1851/100` is the exact rational sum evaluated by the kernel (the manuscript uses the
  rounded list `(2063, 1208, …)/1000`).
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
open scoped BigOperators
namespace BecknerOnofri.V2.Assembly
open BecknerOnofri.HighDim.Spin BecknerOnofri.V2.FiniteState

/-- `|A_{s,j}| ≤ 1` (each `A_{s,j}` is an average of products of spins). -/
theorem moment_abs_le_one (s : Order) (j : Count) : |moment s j| ≤ 1 := by
  have h : ∀ s : Order, ∀ j : Count, |momentQ s j| ≤ 1 := by decide +kernel
  have hc := (Rat.cast_le (K := ℝ)).mpr (h s j)
  simpa [moment] using hc

theorem probability_moment_abs_le_one {q : Count → ℝ} (hq : ∀ j, 0 ≤ q j)
    (hmass : (∑ j : Count, q j) = 1) (s : Order) : |∑ j : Count, moment s j * q j| ≤ 1 := by
  calc |∑ j : Count, moment s j * q j| ≤ ∑ j : Count, |moment s j * q j| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Count, q j := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul, abs_of_nonneg (hq j)]
        simpa using mul_le_mul_of_nonneg_right (moment_abs_le_one s j) (hq j)
    _ = 1 := hmass

/-- `p^T W p ≤ Σ_s w_s` for every probability vector. -/
theorem quadratic_le_sum_weight {q : Count → ℝ} (hq : ∀ j, 0 ≤ q j)
    (hmass : (∑ j : Count, q j) = 1) : quadratic q ≤ ∑ s : Order, weight s := by
  rw [quadratic_eq_sum]
  apply Finset.sum_le_sum
  intro s _
  have h := probability_moment_abs_le_one hq hmass s
  have hs : (∑ j : Count, moment s j * q j) ^ 2 ≤ 1 := by
    have := abs_le.mp h
    nlinarith
  simpa using mul_le_mul_of_nonneg_left hs (weight_nonneg s)

/-- `w_1 + … + w_12 < 1851/100`. -/
theorem sum_weight_lt : (∑ s : Order, weight s) < 1851 / 100 := by
  have h : (∑ s : Order, weightQ s) < 1851 / 100 := by decide +kernel
  have hc := (Rat.cast_lt (K := ℝ)).mpr h
  simpa [weight] using hc

/-! ### The entropy bound `Hr(q | b) ≥ 12 I_B(a)` -/

theorem sum_reference_exp (a : ℝ) (ha0 : -1 < a) (ha1 : a < 1) :
    (∑ j : Count, reference j * Real.exp ((j.val : ℝ) * Real.log (1 + a) +
      (12 - (j.val : ℝ)) * Real.log (1 - a))) = 1 := by
  have hp : 0 < 1 + a := by linarith
  have hm : 0 < 1 - a := by linarith
  have hterm (j : Count) : reference j * Real.exp ((j.val : ℝ) * Real.log (1 + a) +
      (12 - (j.val : ℝ)) * Real.log (1 - a)) =
      ((12).choose j.val : ℝ) * ((1 + a) ^ j.val * (1 - a) ^ (12 - j.val)) / 4096 := by
    rw [reference_eq, Real.exp_add]
    have h1 : Real.exp ((j.val : ℝ) * Real.log (1 + a)) = (1 + a) ^ j.val := by
      rw [Real.exp_nat_mul, Real.exp_log hp]
    have h2 : Real.exp ((12 - (j.val : ℝ)) * Real.log (1 - a)) = (1 - a) ^ (12 - j.val) := by
      have hc : ((12 - j.val : ℕ) : ℝ) = 12 - (j.val : ℝ) := by
        rw [Nat.cast_sub (by omega : j.val ≤ 12)]; norm_num
      rw [← hc, Real.exp_nat_mul, Real.exp_log hm]
    rw [h1, h2]
    ring
  simp_rw [hterm]
  rw [← Finset.sum_div]
  have hb : (∑ j : Count, ((12).choose j.val : ℝ) * ((1 + a) ^ j.val * (1 - a) ^ (12 - j.val))) =
      4096 := by
    have h := (add_pow (1 + a) (1 - a) 12)
    have h2 : ((1 + a) + (1 - a)) ^ 12 = 4096 := by norm_num
    calc (∑ j : Count, ((12).choose j.val : ℝ) * ((1 + a) ^ j.val * (1 - a) ^ (12 - j.val)))
        = ∑ m ∈ Finset.range 13, (1 + a) ^ m * (1 - a) ^ (12 - m) * ((12).choose m : ℝ) := by
          rw [← Fin.sum_univ_eq_sum_range (fun m : ℕ => (1 + a) ^ m * (1 - a) ^ (12 - m) *
            (Nat.choose 12 m : ℝ)) 13]
          apply Finset.sum_congr rfl
          intro j _
          ring
      _ = 4096 := h.symm.trans h2
  rw [hb]
  norm_num


/-- `Σ_j j q_j = 6 (1 + t)` for a probability vector of mean `t`. -/
theorem sum_index_mul {t : ℝ} {q : Count → ℝ} (hmass : (∑ j : Count, q j) = 1)
    (hmean : mean q = t) : (∑ j : Count, (j.val : ℝ) * q j) = 6 * (1 + t) := by
  have h1 : mean q = ∑ j : Count, ((j.val : ℝ) / 6 - 1) * q j := by
    unfold mean
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    simp only [meanCoordinate, meanCoordinateQ]
    push_cast
    ring
  have h2 : (∑ j : Count, ((j.val : ℝ) / 6 - 1) * q j) =
      (∑ j : Count, (j.val : ℝ) * q j) / 6 - ∑ j : Count, q j := by
    rw [Finset.sum_div, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [h1, h2, hmass] at hmean
  linarith

/-- **Coarse entropy bound.**  For `0 ≤ a < 1`, `a ≤ t` and `q ∈ 𝒫_t` (zero coordinates allowed),
`Hr(q | b) ≥ 12 I_B(a)`. -/
theorem relativeEntropy_ge_binaryCost {a t : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hat : a ≤ t)
    {q : Count → ℝ} (hq : FeasibleAt t q) : 12 * binaryCost a ≤ relativeEntropy q reference := by
  obtain ⟨⟨hq0, hmass, -⟩, hmean⟩ := hq
  have hp : 0 < 1 + a := by linarith
  have hm : 0 < 1 - a := by linarith
  have hg := gibbs_variational reference q
    (fun j : Count => (j.val : ℝ) * Real.log (1 + a) + (12 - (j.val : ℝ)) * Real.log (1 - a))
    reference_pos hq0 hmass
  rw [sum_reference_exp a (by linarith) ha1, Real.log_one] at hg
  have hsum : (∑ j : Count, q j * ((j.val : ℝ) * Real.log (1 + a) +
      (12 - (j.val : ℝ)) * Real.log (1 - a))) =
      6 * (1 + t) * Real.log (1 + a) + 6 * (1 - t) * Real.log (1 - a) := by
    have hI := sum_index_mul hmass hmean
    calc (∑ j : Count, q j * ((j.val : ℝ) * Real.log (1 + a) +
          (12 - (j.val : ℝ)) * Real.log (1 - a)))
        = (∑ j : Count, (j.val : ℝ) * q j) * Real.log (1 + a) +
          (12 * (∑ j : Count, q j) - ∑ j : Count, (j.val : ℝ) * q j) * Real.log (1 - a) := by
          rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_mul,
            ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro j _
          ring
      _ = _ := by rw [hI, hmass]; ring
  have hlog : Real.log (1 - a) ≤ Real.log (1 + a) :=
    Real.log_le_log hm (by linarith)
  have hB : 12 * binaryCost a = 6 * (1 + a) * Real.log (1 + a) + 6 * (1 - a) * Real.log (1 - a) := by
    unfold binaryCost
    ring
  have hre : relativeEntropy q reference = ∑ j : Count, q j * Real.log (q j / reference j) := rfl
  rw [hsum] at hg
  rw [hB, hre]
  nlinarith [mul_nonneg (sub_nonneg.mpr hat) (sub_nonneg.mpr hlog)]

/-! ### Numerical inputs -/

theorem log_hundred_lt : Real.log 100 < 47 / 10 := by
  have h2 := Real.log_two_lt_d9
  have h54 : Real.log (5 / 4) ≤ 5 / 4 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  have : Real.log 100 = 6 * Real.log 2 + 2 * Real.log (5 / 4) := by
    have e : (100 : ℝ) = 2 ^ 6 * (5 / 4) ^ 2 := by norm_num
    rw [e, Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
    push_cast
    ring
  rw [this]
  norm_num at h2 ⊢
  linarith

theorem log_199_100_gt : 688 / 1000 < Real.log (199 / 100) := by
  have h2 := Real.log_two_gt_d9
  have h : 1 - ((199 / 200 : ℝ))⁻¹ ≤ Real.log (199 / 200) :=
    Real.one_sub_inv_le_log_of_pos (by norm_num)
  have : Real.log (199 / 100) = Real.log 2 + Real.log (199 / 200) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  rw [this]
  norm_num at h2 h ⊢
  linarith

/-- `I_B(99/100) > 33/50`. -/
theorem binaryCost_ninety_nine_gt : 33 / 50 < binaryCost (99 / 100) := by
  have h1 := log_199_100_gt
  have h2 := log_hundred_lt
  have hl : Real.log (1 - 99 / 100 : ℝ) = - Real.log 100 := by
    rw [show (1 - 99 / 100 : ℝ) = (100 : ℝ)⁻¹ by norm_num, Real.log_inv]
  have hp : Real.log (1 + 99 / 100 : ℝ) = Real.log (199 / 100) := by norm_num
  unfold binaryCost
  rw [hl, hp]
  nlinarith

theorem psiV2_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) : psiV2 a ≤ psiV2 b := by
  unfold psiV2
  have h1 : a ^ 2 ≤ b ^ 2 := by nlinarith
  have hb2 : b ^ 2 ≤ 1 := by nlinarith
  have hbpos : 0 < 14 - 10 * b ^ 2 := by linarith
  have hapos : 0 < 14 - 10 * a ^ 2 := by linarith
  have h4 : a ^ 4 ≤ b ^ 4 := by
    have : a ^ 4 = (a ^ 2) ^ 2 := by ring
    have h' : b ^ 4 = (b ^ 2) ^ 2 := by ring
    rw [this, h']
    exact pow_le_pow_left₀ (sq_nonneg a) h1 2
  rw [div_le_div_iff₀ hapos hbpos]
  have h4a : 0 ≤ a ^ 4 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h1 h4a, h4]

theorem psiV2_ninety_nine_gt : 9 / 40 < psiV2 (99 / 100) := by
  unfold psiV2
  rw [lt_div_iff₀ (by norm_num)]
  norm_num

/-- **Large means** (`eq:d12-spin-eq:largefinal`): for `99/100 ≤ t ≤ 1` and every `q ∈ 𝒫_t`,
`F(q) + 12 ψ(t) > 3/100`. -/
theorem large_mean_bound {t : ℝ} (h99 : 99 / 100 ≤ t) (ht1 : t ≤ 1) {q : Count → ℝ}
    (hq : FeasibleAt t q) : 3 / 100 < functional q + 12 * psiV2 t := by
  have hent := relativeEntropy_ge_binaryCost (a := 99 / 100) (t := t) (by norm_num) (by norm_num)
    h99 hq
  have hquad := quadratic_le_sum_weight hq.1.1 hq.1.2.1
  have hw := sum_weight_lt
  have hIB := binaryCost_ninety_nine_gt
  have hpsi := psiV2_mono (a := 99 / 100) (b := t) (by norm_num) h99 ht1
  have hpsi' := psiV2_ninety_nine_gt
  unfold functional
  linarith

end BecknerOnofri.V2.Assembly
