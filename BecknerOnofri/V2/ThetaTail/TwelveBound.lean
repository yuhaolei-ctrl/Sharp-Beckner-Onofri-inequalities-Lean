module

public import BecknerOnofri.V2.ThetaTail.LambertIntegral
public import BecknerOnofri.V2.ThetaTail.ElementaryBounds
public import BecknerOnofri.V2.ThetaTail.RationalCertificates

@[expose] public section

/-! # The eta-product term and the bound on `G(η)` assuming the twelve-square identity

HONESTLY CONDITIONAL: every theorem whose name ends in `_of_twelveSquare` takes
`TwelveSquareIdentity` as a hypothesis.  Unconditional lemmas: Euler product bounds,
the identity `(1+2q)^12 − 1 − 16(q − 12q³ + 66q⁵) = ∑ s⁶ d_s q^s`.

Appendix A.1: "q∏(1-q^{2m})^12 ≤ q(1-q²)^12 ≤ q − 12q³ + 66q⁵", the integration of the
Lambert series and the displayed bound `(d12-tail-eq:Glog)` in Lambert (pre-logarithm) form. -/
noncomputable section
open Finset Filter Topology MeasureTheory Set
namespace BecknerOnofri.V2.ThetaTail

/-- `0 ≤ ∏(1-q^{2m})^{12} ≤ (1-q²)^{12}` for `0 ≤ q < 1`. -/
theorem eulerProd_bounds {q : ℝ} (h0 : 0 ≤ q) (h1 : q < 1) :
    0 ≤ ∏' m : ℕ+, (1 - q ^ (2 * (m : ℕ))) ^ 12 ∧
      ∏' m : ℕ+, (1 - q ^ (2 * (m : ℕ))) ^ 12 ≤ (1 - q ^ 2) ^ 12 := by
  set g : ℕ → ℝ := fun n => 1 - q ^ (2 * (n + 1)) with hg
  have hq2 : q ^ 2 < 1 := by nlinarith
  have hgle : ∀ n, g n ≤ 1 := fun n => by simp only [hg]; have := pow_nonneg h0 (2 * (n + 1)); linarith
  have hgnn : ∀ n, 0 ≤ g n := fun n => by
    simp only [hg]
    have : q ^ (2 * (n + 1)) ≤ 1 := pow_le_one₀ h0 h1.le
    linarith
  have hsum : Summable (fun n : ℕ => -q ^ (2 * (n + 1))) := by
    have : Summable (fun n : ℕ => (q ^ 2) ^ (n + 1)) :=
      (summable_nat_add_iff 1).2 (summable_geometric_of_lt_one (sq_nonneg q) hq2)
    simpa [pow_mul] using this.neg
  have hmul : Multipliable g := by
    have := Real.multipliable_one_add_of_summable hsum
    simpa [hg, sub_eq_add_neg] using this
  have hP : HasProd g (∏' n, g n) := hmul.hasProd
  have hT := hP.tendsto_prod_nat
  have hg0 : g 0 = 1 - q ^ 2 := by simp [hg]
  have hpart_nn : ∀ N, 0 ≤ ∏ n ∈ range N, g n := fun N => prod_nonneg fun n _ => hgnn n
  have hpart_le : ∀ N, 1 ≤ N → ∏ n ∈ range N, g n ≤ g 0 := by
    intro N hN
    obtain ⟨M, rfl⟩ := Nat.exists_eq_add_of_le' hN
    rw [Finset.prod_range_succ']
    have : ∏ i ∈ range M, g (i + 1) ≤ 1 :=
      Finset.prod_le_one₀ (fun i _ => hgnn _) (fun i _ => hgle _)
    calc (∏ i ∈ range M, g (i + 1)) * g 0 ≤ 1 * g 0 :=
          mul_le_mul_of_nonneg_right this (hgnn 0)
      _ = g 0 := one_mul _
  have hR0 : 0 ≤ ∏' n, g n := ge_of_tendsto' hT hpart_nn
  have hR1 : ∏' n, g n ≤ g 0 :=
    le_of_tendsto hT (Filter.eventually_atTop.2 ⟨1, fun N hN => hpart_le N hN⟩)
  have heq : ∏' m : ℕ+, (1 - q ^ (2 * (m : ℕ))) ^ 12 = (∏' n, g n) ^ 12 := by
    rw [tprod_pnat_eq_tprod_succ (f := fun m : ℕ => (1 - q ^ (2 * m)) ^ 12)]
    rw [← hmul.tprod_pow]
  rw [heq, ← hg0]
  exact ⟨pow_nonneg hR0 _, pow_le_pow_left₀ hR0 hR1 12⟩

theorem sigma5_summable {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) :
    Summable (fun m : ℕ+ => sigma5 m * x ^ (m : ℕ)) := by
  have hs : Summable (fun n : ℕ => (n : ℝ) ^ 6 * x ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one 6 (by simpa [abs_of_nonneg h0] using h1)
  have hs' : Summable (fun m : ℕ+ => ((m : ℕ) : ℝ) ^ 6 * x ^ (m : ℕ)) := hs.subtype _
  exact Summable.of_nonneg_of_le (fun m => mul_nonneg (sigma5_nonneg _) (pow_nonneg h0 _))
    (fun m => mul_le_mul_of_nonneg_right (sigma5_le _) (pow_nonneg h0 _)) hs'

/-- `d_s` as a real number. -/
def dCoeffR (s : ℕ) : ℝ := ((dCoeff s : ℚ) : ℝ)

theorem poly_eq_dsum (q : ℝ) :
    (1 + 2 * q) ^ 12 - 1 - 16 * (q - 12 * q ^ 3 + 66 * q ^ 5)
      = ∑ s ∈ Icc 1 12, dCoeffR s * (s : ℝ) ^ 6 * q ^ s := by
  rw [polynomial_part]
  simp only [dCoeffR, dCoeff]
  simp [Finset.sum_Icc_succ_top]
  norm_num [Nat.choose]

end BecknerOnofri.V2.ThetaTail
