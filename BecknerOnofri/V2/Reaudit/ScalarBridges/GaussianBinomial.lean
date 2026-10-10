module

public import BecknerOnofri.EntropyTailDefinitions
public import Mathlib.Analysis.SpecialFunctions.Artanh
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Data.Nat.Choose.Basic

@[expose] public section

/-! # Lemma 3.5 (`lem:gaussian-binomial`, row S021) by the printed artanh route

Manuscript (V2 TeX 1863-1878): for `n ≥ 1`, `j ∈ ℤ`, `a := log(1 + 1/n)`,
`a_n(j) ≤ e^{-a j²}` where `a_n(j) = C(2n, n+j) / C(2n, n)` (zero outside the support).

Printed proof: for `1 ≤ j ≤ n` the factorial formula gives
`-log a_n(j) = 2 ∑_{r=1}^j artanh((2r-1)/(2n+1)) ≥ a ∑_{r=1}^j (2r-1) = a j²`, using that
`v ↦ artanh(v)/v` is increasing on `(0,1)` (positive power series `∑ v^{2k}/(2k+1)`) and
`2 artanh(1/(2n+1)) = a`.  Symmetry in `j`, `a_n(0) = 1` and vanishing outside the support
finish the proof for `j ∈ ℤ`.

Each step of that proof is a declaration below; no rational subadditivity induction is used. -/

noncomputable section

namespace BecknerOnofri.V2.Reaudit.ScalarBridges

open Real Finset

/-- The printed coefficient `a_n(j) = C(2n, n+j) / C(2n, n)` for `j ∈ ℤ`, with binomial coefficients
taken to be zero outside their integer support (`n + j < 0`, or `n + j > 2n` where `Nat.choose` is
already zero). -/
def binomA (n : ℕ) (j : ℤ) : ℝ :=
  if 0 ≤ (n : ℤ) + j then
    ((2 * n).choose ((n : ℤ) + j).toNat : ℝ) / ((2 * n).choose n : ℝ)
  else 0

lemma binomA_natCast (n j : ℕ) :
    binomA n (j : ℤ) = ((2 * n).choose (n + j) : ℝ) / ((2 * n).choose n : ℝ) := by
  unfold binomA
  have e : (((n : ℤ) + (j : ℤ)).toNat) = n + j := by omega
  simp only [show (0 : ℤ) ≤ (n : ℤ) + (j : ℤ) from by omega, ↓reduceIte, e]

lemma choose_pos' (n : ℕ) : (0 : ℝ) < ((2 * n).choose n : ℝ) :=
  by exact_mod_cast Nat.choose_pos (by omega)

/-- `a_n(0) = 1`. -/
lemma binomA_zero (n : ℕ) : binomA n 0 = 1 := by
  have := binomA_natCast n 0
  simp only [Nat.cast_zero, add_zero] at this
  rw [this, div_self (choose_pos' n).ne']

/-- Vanishing outside the support: `a_n(j) = 0` for `|j| > n`. -/
lemma binomA_eq_zero_of_gt (n : ℕ) (j : ℤ) (h : (n : ℤ) < |j|) : binomA n j = 0 := by
  unfold binomA
  split_ifs with h0
  · have : (2 * n) < ((n : ℤ) + j).toNat := by
      rcases le_or_gt 0 j with hj | hj
      · rw [abs_of_nonneg hj] at h; omega
      · rw [abs_of_neg hj] at h; omega
    rw [Nat.choose_eq_zero_of_lt this]; simp
  · rfl

/-- Symmetry in `j`: `a_n(-j) = a_n(j)`. -/
lemma binomA_neg (n : ℕ) (j : ℤ) : binomA n (-j) = binomA n j := by
  suffices H : ∀ m : ℕ, binomA n (-(m : ℤ)) = binomA n (m : ℤ) by
    rcases Int.eq_nat_or_neg j with ⟨m, rfl | rfl⟩
    · exact H m
    · rw [neg_neg, H]
  intro m
  rw [binomA_natCast]
  by_cases hm : m ≤ n
  · unfold binomA
    have e : (((n : ℤ) + -(m : ℤ)).toNat) = n - m := by omega
    simp only [show (0 : ℤ) ≤ (n : ℤ) + -(m : ℤ) from by omega, ↓reduceIte, e]
    congr 2
    have := Nat.choose_symm_of_eq_add (n := 2 * n) (a := n - m) (b := n + m) (by omega)
    exact_mod_cast this
  · rw [binomA_eq_zero_of_gt n _ (by rw [abs_neg, Nat.abs_cast]; omega)]
    rw [Nat.choose_eq_zero_of_lt (by omega)]; simp

/-- Link with the repository's `scalarCoefficient`: `a_n(j) = scalarCoefficient n |j|`. -/
lemma binomA_eq_scalarCoefficient (n : ℕ) (j : ℤ) :
    binomA n j = BecknerOnofri.HighDim.EntropyTail.scalarCoefficient n j.natAbs := by
  unfold BecknerOnofri.HighDim.EntropyTail.scalarCoefficient
  rcases Int.eq_nat_or_neg j with ⟨m, rfl | rfl⟩
  · rw [binomA_natCast]; simp
  · rw [binomA_neg, binomA_natCast]; simp

/-! ### The positive artanh series -/

/-- `artanh v = ∑_{k≥0} v^{2k+1}/(2k+1)` for `|v| < 1`; in the form used here, the series of
`artanh(v)/v` has the positive coefficients `1/(2k+1)` on `v^{2k}`. -/
theorem hasSum_artanh_div {v : ℝ} (hv0 : 0 < v) (hv1 : v < 1) :
    HasSum (fun k : ℕ => v ^ (2 * k) / (2 * k + 1)) (artanh v / v) := by
  have habs : |v| < 1 := by rw [abs_of_pos hv0]; exact hv1
  have h := (hasSum_log_sub_log_of_abs_lt_one habs).div_const (2 * v)
  have hart : artanh v = (log (1 + v) - log (1 - v)) / 2 := by
    rw [artanh_eq_half_log ⟨by linarith, by linarith⟩, ← Real.log_div (by linarith) (by linarith)]
    · rw [Real.log_div (by linarith) (by linarith)]; ring
  have hv : v ≠ 0 := hv0.ne'
  convert h using 1
  · ext k
    field_simp
    ring
  · rw [hart]; field_simp

/-- `v ↦ artanh(v)/v` is increasing on `(0,1)` (positive coefficients of the series). -/
theorem artanh_div_mono {v w : ℝ} (hv : 0 < v) (hvw : v ≤ w) (hw : w < 1) :
    artanh v / v ≤ artanh w / w := by
  refine hasSum_le (fun k => ?_) (hasSum_artanh_div hv (by linarith))
    (hasSum_artanh_div (by linarith) hw)
  have : (0 : ℝ) < 2 * k + 1 := by positivity
  exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hv.le hvw _) this.le

/-- `2 artanh(1/(2n+1)) = a = log(1 + 1/n)`. -/
theorem two_artanh_eq (n : ℕ) (hn : 0 < n) :
    2 * artanh (1 / (2 * (n : ℝ) + 1)) = log (1 + 1 / (n : ℝ)) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hv : 1 / (2 * (n : ℝ) + 1) ∈ Set.Icc (-1 : ℝ) 1 := by
    constructor
    · have : (0 : ℝ) < 1 / (2 * (n : ℝ) + 1) := by positivity
      linarith
    · rw [div_le_one (by positivity)]; linarith
  rw [artanh_eq_half_log hv]
  have : (1 + 1 / (2 * (n : ℝ) + 1)) / (1 - 1 / (2 * (n : ℝ) + 1)) = 1 + 1 / (n : ℝ) := by
    field_simp; ring
  rw [this]; ring

/-! ### The factorial formula and the comparison -/

lemma binomA_succ (n j : ℕ) (hj : j < n) :
    binomA n ((j + 1 : ℕ) : ℤ) * ((n : ℝ) + j + 1) = binomA n (j : ℤ) * ((n : ℝ) - j) := by
  rw [binomA_natCast, binomA_natCast]
  have h := Nat.choose_succ_right_eq (2 * n) (n + j)
  have h2 : ((2 * n).choose (n + j + 1) : ℝ) * ((n + j + 1 : ℕ) : ℝ)
      = ((2 * n).choose (n + j) : ℝ) * ((2 * n - (n + j) : ℕ) : ℝ) := by exact_mod_cast h
  rw [Nat.cast_sub (by omega)] at h2
  push_cast at h2
  have hc := (choose_pos' n).ne'
  have e : n + (j + 1) = n + j + 1 := by ring
  rw [e]
  field_simp
  nlinarith [h2]

lemma binomA_pos (n j : ℕ) (hj : j ≤ n) : 0 < binomA n (j : ℤ) := by
  rw [binomA_natCast]
  have : 0 < (2 * n).choose (n + j) := Nat.choose_pos (by omega)
  have := choose_pos' n
  positivity

/-- The factorial-formula step of the printed proof (eq:binomial-log-comparison, first equality):
for `0 ≤ j ≤ n`, `-log a_n(j) = 2 ∑_{r=1}^j artanh((2r-1)/(2n+1))`. -/
theorem neg_log_binomA (n j : ℕ) (hj : j ≤ n) :
    -log (binomA n (j : ℤ)) =
      2 * ∑ r ∈ Icc 1 j, artanh ((2 * (r : ℝ) - 1) / (2 * (n : ℝ) + 1)) := by
  induction j with
  | zero => simp [binomA_zero]
  | succ j ih =>
    have hjn : j < n := by omega
    have ih := ih (by omega)
    have hjn' : (j : ℝ) + 1 ≤ n := by exact_mod_cast hjn
    rw [Finset.sum_Icc_succ_top (by omega)]
    set v : ℝ := (2 * ((j + 1 : ℕ) : ℝ) - 1) / (2 * (n : ℝ) + 1) with hvdef
    have hv0 : 0 < v := by
      rw [hvdef]; push_cast; apply div_pos <;> [linarith [(Nat.cast_nonneg j : (0:ℝ) ≤ j)]; positivity]
    have hv1 : v < 1 := by
      rw [hvdef, div_lt_one (by positivity)]; push_cast; linarith
    have hs := binomA_succ n j hjn
    have hpos := binomA_pos n j hjn.le
    have hden : (0 : ℝ) < (n : ℝ) + j + 1 := by positivity
    have hnj : (0 : ℝ) < (n : ℝ) - j := by linarith
    have hratio : binomA n ((j + 1 : ℕ) : ℤ) = binomA n (j : ℤ) * (((n : ℝ) - j) / ((n : ℝ) + j + 1)) := by
      field_simp; linarith
    have hpos' : 0 < binomA n ((j + 1 : ℕ) : ℤ) := binomA_pos n (j + 1) hjn
    have hq : ((n : ℝ) - j) / ((n : ℝ) + j + 1) = (1 - v) / (1 + v) := by
      have h2 : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
      have e1 : 1 - v = 2 * ((n : ℝ) - j) / (2 * n + 1) := by rw [hvdef]; push_cast; field_simp; ring
      have e2 : 1 + v = 2 * ((n : ℝ) + j + 1) / (2 * n + 1) := by rw [hvdef]; push_cast; field_simp; ring
      rw [e1, e2]; field_simp
    have hart : artanh v = 1 / 2 * log ((1 + v) / (1 - v)) :=
      artanh_eq_half_log ⟨by linarith, by linarith⟩
    have hlq : log (((n : ℝ) - j) / ((n : ℝ) + j + 1)) = -(2 * artanh v) := by
      have hinv : log ((1 - v) / (1 + v)) = -log ((1 + v) / (1 - v)) := by
        rw [← log_inv, inv_div]
      rw [hq, hart, hinv]; ring
    have hlog : log (binomA n ((j + 1 : ℕ) : ℤ)) =
        log (binomA n (j : ℤ)) + log (((n : ℝ) - j) / ((n : ℝ) + j + 1)) := by
      rw [hratio, log_mul hpos.ne' (by positivity)]
    rw [hlog, hlq]
    linarith

/-- The term comparison of the printed proof: for `1 ≤ r ≤ n`,
`2 artanh((2r-1)/(2n+1)) ≥ a (2r-1)`, from monotonicity of `artanh(v)/v` and `2 artanh(1/(2n+1)) = a`. -/
theorem term_ge (n r : ℕ) (hn : 0 < n) (hr1 : 1 ≤ r) (hrn : r ≤ n) :
    log (1 + 1 / (n : ℝ)) * (2 * (r : ℝ) - 1) ≤
      2 * artanh ((2 * (r : ℝ) - 1) / (2 * (n : ℝ) + 1)) := by
  have hr1' : (1 : ℝ) ≤ r := by exact_mod_cast hr1
  have hrn' : (r : ℝ) ≤ n := by exact_mod_cast hrn
  have hD : (0 : ℝ) < 2 * (n : ℝ) + 1 := by positivity
  set v1 : ℝ := 1 / (2 * (n : ℝ) + 1) with hv1def
  set v : ℝ := (2 * (r : ℝ) - 1) / (2 * (n : ℝ) + 1) with hvdef
  have hv1pos : 0 < v1 := by positivity
  have hv1v : v1 ≤ v := by
    rw [hv1def, hvdef]; exact div_le_div_of_nonneg_right (by linarith) hD.le
  have hv1 : v < 1 := by rw [hvdef, div_lt_one hD]; linarith
  have hmono := artanh_div_mono hv1pos hv1v hv1
  have hv0 : 0 < v := lt_of_lt_of_le hv1pos hv1v
  rw [div_le_div_iff₀ hv1pos hv0] at hmono
  -- artanh v1 * v ≤ artanh v * v1;  v = (2r-1) v1
  have hvv : v = (2 * (r : ℝ) - 1) * v1 := by rw [hvdef, hv1def]; ring
  have ha := two_artanh_eq n hn
  rw [← hv1def] at ha
  rw [← ha]
  have h3 : artanh v1 * ((2 * (r : ℝ) - 1) * v1) ≤ artanh v * v1 := by rw [← hvv]; exact hmono
  have h4 : artanh v1 * (2 * (r : ℝ) - 1) ≤ artanh v := by
    refine le_of_mul_le_mul_right ?_ hv1pos
    calc artanh v1 * (2 * (r : ℝ) - 1) * v1 = artanh v1 * ((2 * (r : ℝ) - 1) * v1) := by ring
      _ ≤ _ := h3
  linarith

lemma sum_odd (j : ℕ) : ∑ r ∈ Icc 1 j, (2 * (r : ℝ) - 1) = (j : ℝ) ^ 2 := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]; push_cast; ring

/-- The printed inequality (eq:binomial-log-comparison) for `1 ≤ j ≤ n`, in the form
`a j² ≤ -log a_n(j)`. -/
theorem neg_log_binomA_ge (n j : ℕ) (hn : 0 < n) (hj : j ≤ n) :
    log (1 + 1 / (n : ℝ)) * (j : ℝ) ^ 2 ≤ -log (binomA n (j : ℤ)) := by
  rw [neg_log_binomA n j hj, ← sum_odd j, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum (fun r hr => ?_)
  rw [Finset.mem_Icc] at hr
  exact term_ge n r hn hr.1 (le_trans hr.2 hj)

/-- **Lemma 3.5 (`lem:gaussian-binomial`), printed form.**  For `n ≥ 1` and `j ∈ ℤ`,
`a_n(j) ≤ exp(-a j²)` with `a = log(1 + 1/n)`. -/
theorem gaussian_binomial_printed (n : ℕ) (hn : 0 < n) (j : ℤ) :
    binomA n j ≤ Real.exp (-log (1 + 1 / (n : ℝ)) * (j : ℝ) ^ 2) := by
  have hlogpos : 0 < log (1 + 1 / (n : ℝ)) := by
    apply Real.log_pos
    have : (0 : ℝ) < 1 / n := by have : (0 : ℝ) < n := Nat.cast_pos.mpr hn; positivity
    linarith
  suffices H : ∀ m : ℕ, binomA n (m : ℤ) ≤ Real.exp (-log (1 + 1 / (n : ℝ)) * (m : ℝ) ^ 2) by
    rcases Int.eq_nat_or_neg j with ⟨m, rfl | rfl⟩
    · exact H m
    · rw [binomA_neg]; simpa using H m
  intro m
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [binomA_zero]
  by_cases hmn : m ≤ n
  · have h := neg_log_binomA_ge n m hn hmn
    have hp := binomA_pos n m hmn
    calc binomA n (m : ℤ) = Real.exp (log (binomA n (m : ℤ))) := (Real.exp_log hp).symm
      _ ≤ _ := Real.exp_le_exp.2 (by linarith)
  · rw [binomA_eq_zero_of_gt n _ (by rw [Nat.abs_cast]; omega)]
    exact (Real.exp_pos _).le

/-- The same statement for the repository's `scalarCoefficient` (the form of the existing
`BecknerOnofri.V2.Section3.lemma_3_5`), now proved along the printed artanh route. -/
theorem lemma_3_5_artanh (n : ℕ) (hn : 0 < n) (j : ℤ) :
    BecknerOnofri.HighDim.EntropyTail.scalarCoefficient n j.natAbs ≤
      Real.exp (-Real.log (1 + 1 / (n : ℝ)) * (j : ℝ) ^ 2) := by
  rw [← binomA_eq_scalarCoefficient]
  exact gaussian_binomial_printed n hn j


end BecknerOnofri.V2.Reaudit.ScalarBridges
