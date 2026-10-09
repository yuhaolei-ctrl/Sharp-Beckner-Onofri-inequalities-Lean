module

public import Mathlib.Tactic
public import BecknerOnofri.CircleBesselInverse

@[expose] public section

/-! # Truncations of the Bessel series with explicit remainders

`bessel n h = sum_j h^(2j+n)/(j!(j+n)!)` (repository definition, `I_n(2h)`).  For `0 <= h < 1`:
* `Dtr_le_bessel`: `D_4(h) = sum_{k<=4} h^(2k)/k!^2 <= I_0(2h)`;
* `bessel_zero_le`, `bessel_one_le`: `I_0(2h) <= D_4 + h^10/(5!^2 (1-h^2))`,
  `I_1(2h) <= N_4 + h^11/(5!6!(1-h^2))`, `N_4 = sum_{k<=4} h^(2k+1)/(k!(k+1)!)`.
These are the "actual remainder estimates" for the finite jet of the inverse of `R = I_1/I_0`
(Appendix A.2.1, Lemma 5.15). -/
noncomputable section
open Set
open BecknerOnofri.HighDim.CircleScalar
namespace BecknerOnofri.V2.Circle

/-- Truncations `D₄(h) = ∑_{k≤4} h^{2k}/k!²` and `N₄(h) = ∑_{k≤4} h^{2k+1}/(k!(k+1)!)`. -/
def Dtr (h : ℝ) : ℝ := ∑ k ∈ Finset.range 5, h ^ (2 * k) / ((k.factorial : ℝ) * (k.factorial : ℝ))
def Ntr (h : ℝ) : ℝ := ∑ k ∈ Finset.range 5, h ^ (2 * k + 1) / ((k.factorial : ℝ) * ((k + 1).factorial : ℝ))

/-- The `j`-th term of `bessel n h`. -/
def bterm (n : ℕ) (h : ℝ) (j : ℕ) : ℝ := h ^ (2 * j + n) / ((j.factorial : ℝ) * ((j + n).factorial : ℝ))

theorem bterm_nonneg (n : ℕ) {h : ℝ} (hh : 0 ≤ h) (j : ℕ) : 0 ≤ bterm n h j := by
  unfold bterm; positivity

theorem bterm_le_geom (n : ℕ) {h : ℝ} (hh : 0 ≤ h) (h1 : h < 1) (j : ℕ) :
    bterm n h j ≤ (h ^ 2) ^ j := by
  unfold bterm
  have hf1 : (1 : ℝ) ≤ (j.factorial : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero j)
  have hf2 : (1 : ℝ) ≤ ((j + n).factorial : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hn : h ^ n ≤ 1 := pow_le_one₀ hh h1.le
  rw [pow_add, pow_mul]
  apply div_le_of_le_mul₀ (by positivity) (by positivity)
  calc (h ^ 2) ^ j * h ^ n ≤ (h ^ 2) ^ j * 1 := by gcongr
    _ = (h ^ 2) ^ j := mul_one _
    _ ≤ (h ^ 2) ^ j * ((j.factorial : ℝ) * ((j + n).factorial : ℝ)) := by
      have : (1 : ℝ) ≤ (j.factorial : ℝ) * ((j + n).factorial : ℝ) := by nlinarith
      have h0 : 0 ≤ (h ^ 2) ^ j := by positivity
      nlinarith

theorem bterm_summable (n : ℕ) {h : ℝ} (hh : 0 ≤ h) (h1 : h < 1) : Summable (bterm n h) := by
  refine Summable.of_nonneg_of_le (bterm_nonneg n hh) (bterm_le_geom n hh h1)
    (summable_geometric_of_lt_one (by positivity) (by nlinarith))

theorem bessel_eq_tsum (n : ℕ) (h : ℝ) : bessel n h = ∑' j, bterm n h j := rfl

theorem Dtr_le_bessel {h : ℝ} (hh : 0 ≤ h) (h1 : h < 1) : Dtr h ≤ bessel 0 h := by
  have := (bterm_summable 0 hh h1).sum_add_tsum_nat_add 5
  rw [bessel_eq_tsum, ← this]
  have h2 : 0 ≤ ∑' i, bterm 0 h (i + 5) := tsum_nonneg (fun i => bterm_nonneg 0 hh _)
  have : Dtr h = ∑ i ∈ Finset.range 5, bterm 0 h i := by
    simp only [Dtr, bterm, add_zero]
  linarith

/-- Tail estimate for the Bessel series: for `0 ≤ h < 1`,
`bessel n h ≤ ∑_{k<5} h^{2k+n}/(k!(k+n)!) + h^{10+n}/(5!(5+n)! (1-h²))`. -/
theorem bessel_tail_le (n : ℕ) {h : ℝ} (hh : 0 ≤ h) (h1 : h < 1) :
    bessel n h ≤ (∑ i ∈ Finset.range 5, bterm n h i) +
      h ^ (10 + n) / (((5 : ℕ).factorial : ℝ) * ((5 + n).factorial : ℝ) * (1 - h ^ 2)) := by
  have hs := (bterm_summable n hh h1).sum_add_tsum_nat_add 5
  rw [bessel_eq_tsum, ← hs]
  have hq : h ^ 2 < 1 := by nlinarith
  set c : ℝ := ((5 : ℕ).factorial : ℝ) * ((5 + n).factorial : ℝ) with hc
  have hcpos : 0 < c := by positivity
  have hgeo : Summable (fun j : ℕ => h ^ (10 + n) / c * (h ^ 2) ^ j) :=
    (summable_geometric_of_lt_one (by positivity) hq).mul_left _
  have hle : ∀ j : ℕ, bterm n h (j + 5) ≤ h ^ (10 + n) / c * (h ^ 2) ^ j := by
    intro j
    unfold bterm
    have e : h ^ (2 * (j + 5) + n) = h ^ (10 + n) * (h ^ 2) ^ j := by
      rw [← pow_mul, ← pow_add]; congr 1; ring
    rw [e]
    have f1 : (((5 : ℕ).factorial : ℕ) : ℝ) ≤ ((j + 5).factorial : ℝ) := by
      have : (5 : ℕ).factorial ≤ (j + 5).factorial := Nat.factorial_le (by omega)
      exact_mod_cast this
    have f2 : (((5 + n : ℕ).factorial : ℕ) : ℝ) ≤ ((j + 5 + n).factorial : ℝ) := by
      have : (5 + n).factorial ≤ (j + 5 + n).factorial := Nat.factorial_le (by omega)
      exact_mod_cast this
    rw [div_le_iff₀ (by positivity)]
    have hcle : c ≤ ((j + 5).factorial : ℝ) * ((j + 5 + n).factorial : ℝ) := by
      rw [hc]
      exact mul_le_mul f1 f2 (by positivity) (by positivity)
    calc h ^ (10 + n) * (h ^ 2) ^ j = h ^ (10 + n) / c * (h ^ 2) ^ j * c := by field_simp
      _ ≤ h ^ (10 + n) / c * (h ^ 2) ^ j * (((j + 5).factorial : ℝ) * ((j + 5 + n).factorial : ℝ)) := by
        gcongr
  have htail : ∑' j, bterm n h (j + 5) ≤ h ^ (10 + n) / (c * (1 - h ^ 2)) := by
    calc ∑' j, bterm n h (j + 5) ≤ ∑' j : ℕ, h ^ (10 + n) / c * (h ^ 2) ^ j :=
          (Summable.tsum_le_tsum hle ((bterm_summable n hh h1).comp_injective (add_left_injective 5)) hgeo)
      _ = h ^ (10 + n) / (c * (1 - h ^ 2)) := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one (by positivity) hq]
        field_simp
  linarith

theorem bessel_one_le {h : ℝ} (hh : 0 ≤ h) (h1 : h < 1) :
    bessel 1 h ≤ Ntr h + h ^ 11 / (86400 * (1 - h ^ 2)) := by
  have := bessel_tail_le 1 hh h1
  have hN : Ntr h = ∑ i ∈ Finset.range 5, bterm 1 h i := by simp only [Ntr, bterm]
  rw [hN]
  norm_num [Nat.factorial] at this ⊢
  exact this

theorem bessel_zero_le {h : ℝ} (hh : 0 ≤ h) (h1 : h < 1) :
    bessel 0 h ≤ Dtr h + h ^ 10 / (14400 * (1 - h ^ 2)) := by
  have := bessel_tail_le 0 hh h1
  have hD : Dtr h = ∑ i ∈ Finset.range 5, bterm 0 h i := by simp only [Dtr, bterm, add_zero]
  rw [hD]
  norm_num [Nat.factorial] at this ⊢
  exact this

theorem bessel_zero_pos {h : ℝ} (hh : 0 ≤ h) (h1 : h < 1) : 1 ≤ bessel 0 h := by
  have := Dtr_le_bessel hh h1
  have hD : 1 ≤ Dtr h := by
    simp only [Dtr, Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num [Nat.factorial]
    have : 0 ≤ h ^ 2 / 1 + h ^ 4 / 4 + h ^ 6 / 36 + h ^ 8 / 576 := by positivity
    linarith
  linarith

end BecknerOnofri.V2.Circle
