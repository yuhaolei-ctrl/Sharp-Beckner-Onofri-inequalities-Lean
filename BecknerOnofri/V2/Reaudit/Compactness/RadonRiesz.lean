module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Analysis.Normed.Group.InfiniteSum

@[expose] public section

/-! # Weak convergence plus convergence of Hilbert norms gives strong convergence (weighted `ℓ²`)

Manuscript (Section 4, proof of `prop:section4-first-order-coexistence`, the passage from
`eq:section4-energy-norm-convergence` to `eq:section4-strong-critical-Sobolev`): "weak convergence
together with `‖u_n‖² → ‖u_0‖²` gives `u_n → u_0` strongly in `H^{11/2}`".

The Hilbert space is a weighted `ℓ²(ι)`: coefficients `a : ι → ℂ` with norm `Σ_i w_i |a_i|²`
(`w_i ≥ 0`).  Weak convergence of a bounded sequence is coefficientwise convergence, which is what
the `L²` convergence supplies; no weak-topology API is used.  The argument is the classical
tail estimate: if `F` is a finite set capturing all but `δ` of the mass of the limit, then the
mass of `a_n` off `F` tends to the mass of the limit off `F`, hence is `≲ δ`. -/

noncomputable section
open Filter
open scoped Topology

namespace BecknerOnofri.V2.Reaudit.Compactness

/-- **Radon--Riesz in a weighted `ℓ²`.**  Coefficientwise convergence together with convergence of
the weighted square norms implies convergence in the weighted `ℓ²` norm. -/
theorem radon_riesz {ι : Type*} (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (a : ℕ → ι → ℂ) (a₀ : ι → ℂ)
    (ha : ∀ n, Summable fun i => w i * ‖a n i‖ ^ 2)
    (ha₀ : Summable fun i => w i * ‖a₀ i‖ ^ 2)
    (hpt : ∀ i, Tendsto (fun n => a n i) atTop (𝓝 (a₀ i)))
    (hnorm : Tendsto (fun n => ∑' i, w i * ‖a n i‖ ^ 2) atTop (𝓝 (∑' i, w i * ‖a₀ i‖ ^ 2))) :
    Tendsto (fun n => ∑' i, w i * ‖a n i - a₀ i‖ ^ 2) atTop (𝓝 0) := by
  classical
  -- pointwise bound `|x - y|² ≤ 2|x|² + 2|y|²`
  have hpair : ∀ n i, w i * ‖a n i - a₀ i‖ ^ 2 ≤
      2 * (w i * ‖a n i‖ ^ 2) + 2 * (w i * ‖a₀ i‖ ^ 2) := by
    intro n i
    have h1 : ‖a n i - a₀ i‖ ≤ ‖a n i‖ + ‖a₀ i‖ := norm_sub_le _ _
    have h2 : ‖a n i - a₀ i‖ ^ 2 ≤ 2 * ‖a n i‖ ^ 2 + 2 * ‖a₀ i‖ ^ 2 := by
      have h0 : 0 ≤ ‖a n i - a₀ i‖ := norm_nonneg _
      nlinarith [norm_nonneg (a n i), norm_nonneg (a₀ i), sq_nonneg (‖a n i‖ - ‖a₀ i‖)]
    calc w i * ‖a n i - a₀ i‖ ^ 2 ≤ w i * (2 * ‖a n i‖ ^ 2 + 2 * ‖a₀ i‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h2 (hw i)
      _ = _ := by ring
  have hsum_diff : ∀ n, Summable fun i => w i * ‖a n i - a₀ i‖ ^ 2 := fun n =>
    Summable.of_nonneg_of_le (fun i => mul_nonneg (hw i) (sq_nonneg _)) (hpair n)
      (((ha n).mul_left 2).add (ha₀.mul_left 2))
  rw [tendsto_order]
  refine ⟨fun c hc => ?_, fun c hc => ?_⟩
  · exact Eventually.of_forall fun n =>
      lt_of_lt_of_le hc (tsum_nonneg fun i => mul_nonneg (hw i) (sq_nonneg _))
  -- upper bound: choose a finite set carrying all but `c/8` of the limit's mass
  have hc8 : 0 < c / 8 := by positivity
  have htail := tendsto_tsum_compl_atTop_zero (fun i => w i * ‖a₀ i‖ ^ 2)
  obtain ⟨F, hF⟩ := (tendsto_order.1 htail).2 (c / 8) hc8 |>.exists
  -- `hF : ∑' i : {x // x ∉ F}, w i * ‖a₀ i‖^2 < c/8`
  set S : ℕ → ℝ := fun n => ∑' i, w i * ‖a n i‖ ^ 2 with hS
  set S₀ : ℝ := ∑' i, w i * ‖a₀ i‖ ^ 2 with hS₀
  -- the mass of `a n` off `F`
  have hsplit : ∀ n, ∑ i ∈ F, w i * ‖a n i‖ ^ 2 + ∑' i : {x // x ∉ F}, w i * ‖a n i‖ ^ 2 = S n := by
    intro n
    exact (ha n).sum_add_tsum_subtype_compl F
  have hsplit₀ : ∑ i ∈ F, w i * ‖a₀ i‖ ^ 2 + ∑' i : {x // x ∉ F}, w i * ‖a₀ i‖ ^ 2 = S₀ :=
    ha₀.sum_add_tsum_subtype_compl F
  have hFin : Tendsto (fun n => ∑ i ∈ F, w i * ‖a n i‖ ^ 2) atTop
      (𝓝 (∑ i ∈ F, w i * ‖a₀ i‖ ^ 2)) :=
    tendsto_finsetSum _ fun i _ =>
      (((hpt i).norm.pow 2).const_mul (w i))
  have hTail : Tendsto (fun n => ∑' i : {x // x ∉ F}, w i * ‖a n i‖ ^ 2) atTop
      (𝓝 (∑' i : {x // x ∉ F}, w i * ‖a₀ i‖ ^ 2)) := by
    have h := hnorm.sub hFin
    have e : ∀ n, ∑' i : {x // x ∉ F}, w i * ‖a n i‖ ^ 2 = S n - ∑ i ∈ F, w i * ‖a n i‖ ^ 2 :=
      fun n => by linarith [hsplit n]
    have e₀ : ∑' i : {x // x ∉ F}, w i * ‖a₀ i‖ ^ 2 = S₀ - ∑ i ∈ F, w i * ‖a₀ i‖ ^ 2 := by
      linarith [hsplit₀]
    simp only [e, e₀]
    exact h
  have hFinDiff : Tendsto (fun n => ∑ i ∈ F, w i * ‖a n i - a₀ i‖ ^ 2) atTop (𝓝 0) := by
    have : Tendsto (fun n => ∑ i ∈ F, w i * ‖a n i - a₀ i‖ ^ 2) atTop
        (𝓝 (∑ i ∈ F, w i * ‖a₀ i - a₀ i‖ ^ 2)) :=
      tendsto_finsetSum _ fun i _ =>
        (((hpt i).sub_const (a₀ i)).norm.pow 2).const_mul (w i)
    simpa using this
  have e1 := (tendsto_order.1 hFinDiff).2 (c / 4) (by positivity)
  have e2 := (tendsto_order.1 hTail).2 (c / 4) (by linarith)
  filter_upwards [e1, e2] with n h1 h2
  -- split the difference sum
  have hd := (hsum_diff n).sum_add_tsum_subtype_compl F
  have htailDiff : ∑' i : {x // x ∉ F}, w i * ‖a n i - a₀ i‖ ^ 2 ≤
      2 * (∑' i : {x // x ∉ F}, w i * ‖a n i‖ ^ 2) +
        2 * (∑' i : {x // x ∉ F}, w i * ‖a₀ i‖ ^ 2) := by
    have hs1 : Summable fun i : {x // x ∉ F} => w i * ‖a n i‖ ^ 2 := (ha n).subtype _
    have hs2 : Summable fun i : {x // x ∉ F} => w i * ‖a₀ i‖ ^ 2 := ha₀.subtype _
    have hs3 : Summable fun i : {x // x ∉ F} => w i * ‖a n i - a₀ i‖ ^ 2 :=
      (hsum_diff n).subtype _
    calc ∑' i : {x // x ∉ F}, w i * ‖a n i - a₀ i‖ ^ 2
        ≤ ∑' i : {x // x ∉ F}, (2 * (w i * ‖a n i‖ ^ 2) + 2 * (w i * ‖a₀ i‖ ^ 2)) :=
          hs3.tsum_le_tsum (fun i => hpair n i) ((hs1.mul_left 2).add (hs2.mul_left 2))
      _ = _ := by rw [Summable.tsum_add (hs1.mul_left 2) (hs2.mul_left 2), tsum_mul_left,
            tsum_mul_left]
  linarith

end BecknerOnofri.V2.Reaudit.Compactness
