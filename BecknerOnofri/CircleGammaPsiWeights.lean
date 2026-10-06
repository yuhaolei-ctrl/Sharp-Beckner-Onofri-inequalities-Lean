module

public import BecknerOnofri.CircleGammaPsiPoly
public import BecknerOnofri.CircleWeightSeries

@[expose] public section

/-! Step 2 of the proof of Lemma 5.17 (`lem:section5-global-small-gamma`):
the rational lower bounds `B(x) ≤ c w₁(t)` and `C(x) ≤ c w₂(t)`, `x = t²`.

Instead of the manuscript's closed-form coefficients of the full power series,
we compare `B` and `C` with the partial sums of `w₁` (15 terms) and `w₂`
(18 terms); after clearing the quadratic denominators the difference is `x⁴`
times a polynomial whose Bernstein coefficients on `[0,1]` are positive. -/
noncomputable section
open scoped BigOperators
namespace BecknerOnofri.HighDim.CircleScalar
open GammaPoly

theorem eval_append (p q : List ℚ) (x : ℝ) :
    eval (p ++ q) x = eval p x + x ^ p.length * eval q x := by
  induction p with
  | nil => simp
  | cons a p ih => simp [ih]; ring

theorem eval_map_range (f : ℕ → ℚ) (N : ℕ) (x : ℝ) :
    eval ((List.range N).map f) x = ∑ j ∈ Finset.range N, (f j : ℝ) * x ^ j := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.map_append, eval_append, ih, Finset.sum_range_succ]
    simp; ring

def weightNumOne : List ℚ := [15, -8]
def weightDenOne : List ℚ := [10, -12, 3]
def weightNumTwo : List ℚ := [12, -7]
def weightDenTwo : List ℚ := [15, -20, 6]
def weightPartialOne : List ℚ := (List.range 15).map (fun j : ℕ => 1 / ((j : ℚ) + 2))
def weightPartialTwo : List ℚ := (List.range 18).map (fun j : ℕ => 1 / ((j : ℚ) + 3))
def weightGapOne : List ℚ := sub (smul 3 (mul weightDenOne weightPartialOne)) weightNumOne
def weightGapTwo : List ℚ :=
  sub (smul 12 (mul weightDenTwo weightPartialTwo)) (smul 5 weightNumTwo)

/-- The lower bound `B(x)` for `c w₁`. -/
def weightBoundOne (x : ℝ) : ℝ := (67/100) * eval weightNumOne x / (3 * eval weightDenOne x)
/-- The lower bound `C(x)` for `c w₂`. -/
def weightBoundTwo (x : ℝ) : ℝ :=
  5 * (67/100) * eval weightNumTwo x / (12 * eval weightDenTwo x)

theorem weight_partial_eq (n N : ℕ) (t : ℝ) :
    (∑ j ∈ Finset.range N, t^(2*j)/(n+j+1:ℝ)) =
      eval ((List.range N).map (fun j : ℕ => 1 / ((j : ℚ) + (n + 1)))) (t^2) := by
  rw [eval_map_range]
  apply Finset.sum_congr rfl
  intro j _
  rw [pow_mul]
  push_cast
  field_simp
  ring

theorem weightDenOne_pos {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : 0 < eval weightDenOne x :=
  pos_of_posCheck (lo := 0) (hi := 1) (by decide +kernel) (by simpa using h0) (by simpa using h1)

theorem weightDenTwo_pos {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : 0 < eval weightDenTwo x :=
  pos_of_posCheck (lo := 0) (hi := 1) (by decide +kernel) (by simpa using h0) (by simpa using h1)

theorem weightNumOne_pos {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : 0 < eval weightNumOne x :=
  pos_of_posCheck (lo := 0) (hi := 1) (by decide +kernel) (by simpa using h0) (by simpa using h1)

theorem weightNumTwo_pos {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : 0 < eval weightNumTwo x :=
  pos_of_posCheck (lo := 0) (hi := 1) (by decide +kernel) (by simpa using h0) (by simpa using h1)

theorem weightGapOne_nonneg {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : 0 ≤ eval weightGapOne x := by
  rw [eval_drop 4 weightGapOne (by decide +kernel)]
  exact mul_nonneg (pow_nonneg h0 4) (pos_of_posCheck (lo := 0) (hi := 1)
    (by decide +kernel) (by simpa using h0) (by simpa using h1)).le

theorem weightGapTwo_nonneg {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : 0 ≤ eval weightGapTwo x := by
  rw [eval_drop 4 weightGapTwo (by decide +kernel)]
  exact mul_nonneg (pow_nonneg h0 4) (pos_of_posCheck (lo := 0) (hi := 1)
    (by decide +kernel) (by simpa using h0) (by simpa using h1)).le

theorem weightBoundOne_nonneg {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : 0 ≤ weightBoundOne x := by
  have := weightNumOne_pos h0 h1
  have := weightDenOne_pos h0 h1
  unfold weightBoundOne; positivity

theorem weightBoundTwo_nonneg {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : 0 ≤ weightBoundTwo x := by
  have := weightNumTwo_pos h0 h1
  have := weightDenTwo_pos h0 h1
  unfold weightBoundTwo; positivity

/-- Step 2, first weight: `B(t²) ≤ c w₁(t)`. -/
theorem weightBoundOne_le {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) :
    weightBoundOne (t^2) ≤ (67/100) * weight 1 t := by
  have hx0 : 0 ≤ t^2 := sq_nonneg t
  have hx1 : t^2 ≤ 1 := by nlinarith
  have hS := (weight_finite_enclosure 1 15 ht ht1).1
  rw [weight_partial_eq] at hS
  have hg := weightGapOne_nonneg hx0 hx1
  have hd := weightDenOne_pos hx0 hx1
  simp only [weightGapOne, eval_sub, eval_smul, eval_mul] at hg
  have hS' : eval weightPartialOne (t^2) ≤ weight 1 t := by
    convert hS using 3; norm_num [weightPartialOne]
  unfold weightBoundOne
  rw [div_le_iff₀ (by positivity)]
  push_cast at hg
  nlinarith

/-- Step 2, second weight: `C(t²) ≤ c w₂(t)`. -/
theorem weightBoundTwo_le {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) :
    weightBoundTwo (t^2) ≤ (67/100) * weight 2 t := by
  have hx0 : 0 ≤ t^2 := sq_nonneg t
  have hx1 : t^2 ≤ 1 := by nlinarith
  have hS := (weight_finite_enclosure 2 18 ht ht1).1
  rw [weight_partial_eq] at hS
  have hg := weightGapTwo_nonneg hx0 hx1
  have hd := weightDenTwo_pos hx0 hx1
  simp only [weightGapTwo, eval_sub, eval_smul, eval_mul] at hg
  have hS' : eval weightPartialTwo (t^2) ≤ weight 2 t := by
    convert hS using 3; norm_num [weightPartialTwo]
  unfold weightBoundTwo
  rw [div_le_iff₀ (by positivity)]
  push_cast at hg
  nlinarith

end BecknerOnofri.HighDim.CircleScalar
