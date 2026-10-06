module

public import BecknerOnofri.CircleGammaPsiBarrier
public import BecknerOnofri.SpinBinaryCost

@[expose] public section

/-! Step 3 of the proof of Lemma 5.17 (`lem:section5-global-small-gamma`):
`(1-c)J + cx - 2I_B - ψ ≥ x² E(x)` with the explicit rational function `E`
of the computational supplement.

Deviation from the manuscript: instead of bounding the full entropy tail by
the rational function in `eq:simple-entropy-tail`, we first bound the two
logarithms below by the partial sum of their combined series through `x⁴³`
(all omitted coefficients are positive; this is proved by showing that the
second derivative of the remainder is nonnegative), and then compare this
polynomial with `x² E(x)` by one Bernstein certificate on `[0,1]`. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
namespace BecknerOnofri.HighDim.CircleScalar
open GammaPoly Spin

/-- Coefficients `α'_k = (33/200)/k - 1/(k(2k-1))`, `1 ≤ k ≤ 43`, of the combined
series of `-(33/200) log(1-x) - 2 I_B(t)` in `x = t²`. -/
def entropySeries : List ℚ :=
  0 :: (List.range 43).map (fun k : ℕ => (33/200) / ((k : ℚ) + 1) -
    1 / (((k : ℚ) + 1) * (2 * ((k : ℚ) + 1) - 1)))
def entropySeriesSecond : List ℚ := derivL (derivL (subsq entropySeries))
/-- `(1-u²)²` times the second derivative of the series remainder. -/
def entropyRemainderSecond : List ℚ :=
  add [-167/100, 0, 233/100] (smul (-1) (mul [1, 0, -2, 0, 1] entropySeriesSecond))
def entropyNum : List ℚ :=
  [6882876000, -8276268000, 1454760450, 7405775520, -10154519635, 2826860324]
def entropyDen : List ℚ := [30, -40, 11]
/-- The polynomial part of `(1-c)J + cx - ψ` plus the series lower bound. -/
def entropyPolynomial : List ℚ :=
  add entropySeries (add (smul (33/100) [0, 1/2, 0, -1/36, -5/192, -49/1200])
    [0, 67/100, -3/40, 0, 0, -33/200])
def entropyGap : List ℚ :=
  add (smul 1441440000 (mul entropyDen entropyPolynomial)) (mul [0, 0, 1] entropyNum)

/-- The rational function `E(x)` (equation (8) of the supplement). -/
def entropyBound (x : ℝ) : ℝ := -eval entropyNum x / (1441440000 * eval entropyDen x)

theorem eval_derivL_subsq_zero (p : List ℚ) : eval (derivL (subsq p)) 0 = 0 := by
  cases p with
  | nil => simp [subsq, derivL]
  | cons a p => simp [subsq, derivL]

theorem entropyDen_pos {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : 0 < eval entropyDen x :=
  pos_of_posCheck (lo := 0) (hi := 1) (by decide +kernel) (by simpa using h0) (by simpa using h1)

theorem entropyRemainderSecond_nonneg {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) :
    0 ≤ eval entropyRemainderSecond u := by
  rw [eval_drop 86 entropyRemainderSecond (by decide +kernel)]
  exact mul_nonneg (pow_nonneg h0 86) (pos_of_posCheck (lo := 0) (hi := 1)
    (by decide +kernel) (by simpa using h0) (by simpa using h1)).le

theorem entropyGap_nonneg {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : 0 ≤ eval entropyGap x := by
  rw [eval_drop 8 entropyGap (by decide +kernel)]
  exact mul_nonneg (pow_nonneg h0 8) (pos_of_posCheck (lo := 0) (hi := 1)
    (by decide +kernel) (by simpa using h0) (by simpa using h1)).le

/-- The logarithmic part dominates the partial sum of its series. -/
theorem entropySeries_le {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) :
    eval entropySeries (a^2) ≤ (33/100) * (-(1/2) * Real.log (1 - a^2)) - 2 * binaryCost a := by
  let F : ℝ → ℝ := fun u => (33/100) * (-(1/2) * Real.log (1 - u^2)) - 2 * binaryCost u -
    eval (subsq entropySeries) u
  let F' : ℝ → ℝ := fun u => (33/100) * (u / (1 - u^2)) - 2 * binaryCostSlope u -
    eval (derivL (subsq entropySeries)) u
  let F'' : ℝ → ℝ := fun u => (33/100) * ((1 + u^2) / (1 - u^2)^2) -
    2 * binaryCostHessian u - eval entropySeriesSecond u
  have hF (u : ℝ) (hu : -1 < u) (hu1 : u < 1) : HasDerivAt F (F' u) u := by
    have hd : 1 - u^2 ≠ 0 := by nlinarith
    have hlog := ((hasDerivAt_pow 2 u).const_sub 1).log hd
    have h := ((hlog.const_mul (-(1/2:ℝ))).const_mul (33/100)).sub
      ((binaryCost_derivative u hu hu1).const_mul 2) |>.sub
      (hasDerivAt_eval (subsq entropySeries) u)
    convert h using 1
    simp only [F']
    field_simp
    ring
  have hF' (u : ℝ) (hu : -1 < u) (hu1 : u < 1) : HasDerivAt F' (F'' u) u := by
    have hd : 1 - u^2 ≠ 0 := by nlinarith
    have h := ((((hasDerivAt_id u).div ((hasDerivAt_pow 2 u).const_sub 1) hd)).const_mul
      (33/100)).sub ((binaryCost_second_derivative u hu hu1).const_mul 2) |>.sub
      (hasDerivAt_eval (derivL (subsq entropySeries)) u)
    convert h using 1
    · funext v; simp [F']
    · simp only [F'', entropySeriesSecond, id]
      field_simp
      ring
  have hF''_nonneg (u : ℝ) (hu : 0 ≤ u) (hu1 : u < 1) : 0 ≤ F'' u := by
    have hd : 0 < 1 - u^2 := by nlinarith
    have hg := entropyRemainderSecond_nonneg hu hu1.le
    have he : F'' u = eval entropyRemainderSecond u / (1 - u^2)^2 := by
      simp only [F'', entropyRemainderSecond, eval_add, eval_smul, eval_mul, eval_cons,
        eval_nil, binaryCostHessian]
      field_simp
      push_cast
      ring
    rw [he]
    positivity
  let f : ℝ → ℝ := fun s => F (a * s)
  let f' : ℝ → ℝ := fun s => a * F' (a * s)
  let f'' : ℝ → ℝ := fun s => a^2 * F'' (a * s)
  have hi (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) : 0 ≤ a * s ∧ a * s < 1 := by
    refine ⟨mul_nonneg ha hs.1, ?_⟩
    have : a * s ≤ a := by nlinarith [hs.2]
    linarith
  have hd (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) : HasDerivAt f (f' s) s := by
    have h := (hF (a * s) (by linarith [(hi s hs).1]) (hi s hs).2).comp s
      ((hasDerivAt_id s).const_mul a)
    convert h using 1
    · exact rfl
    · show a * F' (a * s) = F' (a * s) * (a * 1)
      ring
  have hdd (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) : HasDerivAt f' (f'' s) s := by
    have h := ((hF' (a * s) (by linarith [(hi s hs).1]) (hi s hs).2).comp s
      ((hasDerivAt_id s).const_mul a)).const_mul a
    convert h using 1
    · exact rfl
    · show a^2 * F'' (a * s) = a * (F'' (a * s) * (a * 1))
      ring
  have hcont : ContinuousOn f (Icc 0 1) := fun s hs =>
    (hd s hs).continuousAt.continuousWithinAt
  have h := Spin.second_order_support (c := 0) hcont (hd 0 (by simp))
    (fun s hs => hd s (Ioo_subset_Icc_self hs)) (fun s hs => hdd s (Ioo_subset_Icc_self hs))
    (fun s hs => mul_nonneg (sq_nonneg a) (hF''_nonneg (a * s) (hi s
      (Ioo_subset_Icc_self hs)).1 (hi s (Ioo_subset_Icc_self hs)).2))
  have hz : F 0 = 0 := by simp [F, binaryCost, subsq, entropySeries]
  have hz' : F' 0 = 0 := by simp [F', binaryCostSlope, eval_derivL_subsq_zero]
  simp only [f, f', mul_zero, mul_one, hz, hz', zero_div, add_zero] at h
  simp only [F, eval_subsq] at h
  linarith

/-- Step 3: `(1-c)J + cx - 2I_B - ψ ≥ x² E(x)` (`eq:simple-circle-E`). -/
theorem entropyBound_le {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) :
    t^4 * entropyBound (t^2) ≤ (33/100) * rateLower t + (67/100) * t^2 -
      2 * binaryCost t - ((3/40) * t^4 + (33/200) * t^10) := by
  have hx0 : 0 ≤ t^2 := sq_nonneg t
  have hx1 : t^2 ≤ 1 := by nlinarith
  have hs := entropySeries_le ht ht1
  have hg := entropyGap_nonneg hx0 hx1
  have hd := entropyDen_pos hx0 hx1
  simp only [entropyGap, entropyPolynomial, eval_add, eval_smul, eval_mul, eval_cons,
    eval_nil] at hg
  have hE : t^4 * entropyBound (t^2) = -(t^2)^2 * eval entropyNum (t^2) /
      (1441440000 * eval entropyDen (t^2)) := by
    unfold entropyBound; ring
  rw [hE, div_le_iff₀ (by positivity)]
  unfold rateLower
  push_cast at hg
  nlinarith

end BecknerOnofri.HighDim.CircleScalar
