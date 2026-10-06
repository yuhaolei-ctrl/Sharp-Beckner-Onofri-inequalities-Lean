module

public import BecknerOnofri.SpinNormEstimate

@[expose] public section

/-!
# Curvature on slices of fixed mean (Lemma 5.18, manuscript 2026-10-06)

This file proves `lem:section5-global-curvature` with the constants of the manuscript dated
2026-10-06: the vertex maximum is below `6/7`, the corrector `v = e₀ - (12/11)e₁ + (1/11)e₁₂`
satisfies `vᵀWv < (15/8)²`, `√(6/7) < 13/14`, `K = 15/8 + (13/14)(13/11)` and
`κ = 6/7 + K²/4096 < 43/50`.

The extreme-point reduction and the exact vertex evaluation are reused from
`SpinPolytopeBound`/`SpinExactArithmetic`; only the constants change.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace BecknerOnofri.HighDim.Spin

/-- The exact vertex maximum is below `6/7` (eq:section5-global-vertex-max). -/
theorem vertex_energy_lt_six_sevenths :
    (3187261891510618067287:ℚ)/3722907769367296702500 < 6/7 := by norm_num

/-- Every three-point vertex has energy at most `6/7`. -/
theorem quadratic_vertex_bound_sharp {i j k : Count} (hi : 1 ≤ i.val) (hij : i < j)
    (hjk : j < k) : quadratic (vertex i j k) ≤ 6/7 := by
  have h := (vertex_energy_bound i j k hi hij hjk).trans vertex_energy_lt_six_sevenths.le
  rw [← vertex_energy_eq hij hjk] at h
  change quadratic (fun r => (vertexQ i j k r : ℝ)) ≤ 6/7
  rw [quadratic_cast]
  have hc := Rat.cast_le (K := ℝ).mpr h
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hc
  exact hc

/-- The quadratic form is at most `6/7` on the whole tangent polytope. -/
theorem tangentPolytope_quadratic_bound_sharp :
    ∀ q ∈ tangentPolytope, quadratic q ≤ 6/7 := by
  apply quadratic_bound_of_extreme
  intro q hq
  obtain ⟨i, j, k, hi, hij, hjk, hs⟩ := extreme_support_three hq
  have hrep := sparse_eq_smul_vertex hij hjk hs hq.1.2.1 hq.1.2.2.1
  have hscale := sparse_scale_bound hij hjk hs hq.1.2.1 hq.1.2.2.2
  have hsq : (-2 * q j)^2 ≤ 1 := by nlinarith [sq_abs (-2 * q j), abs_nonneg (-2 * q j)]
  have hb := quadratic_vertex_bound_sharp hi hij hjk
  have hn := quadratic_nonneg (vertex i j k)
  rw [hrep, quadratic_smul]
  nlinarith [mul_nonneg (sub_nonneg.mpr hsq) hn]

/-- Seminorm bound `‖q‖_W ≤ √(6/7) ‖q‖₁` for `q₀ = 0` with mass and mean zero. -/
theorem zero_coordinate_seminorm_bound_sharp {q : Count → ℝ}
    (hq0 : q 0 = 0) (hmass : (∑ j : Count, q j) = 0) (hmean : mean q = 0) :
    ‖featureMap q‖ ≤ Real.sqrt (6/7) * l1 q := by
  by_cases hl : l1 q = 0
  · rw [(l1_eq_zero_iff q).mp hl]
    simp [l1]
  have hp : 0 < l1 q := lt_of_le_of_ne (l1_nonneg q) (Ne.symm hl)
  let r := (1 / l1 q) • q
  have hr : r ∈ tangentPolytope := by
    refine ⟨by simp [r, hq0], by simp [r, ← Finset.mul_sum, hmass], ?_, ?_⟩
    · have h := mean_linear_combination q q (1 / l1 q) 0
      simpa [r, hmean] using h
    · change l1 ((1 / l1 q) • q) ≤ 1
      rw [l1_smul, abs_of_pos (by positivity), one_div_mul_cancel hl]
  have hb := tangentPolytope_quadratic_bound_sharp r hr
  have hnorm : ‖featureMap r‖ ≤ Real.sqrt (6/7) := by
    rw [featureMap_norm]
    exact Real.sqrt_le_sqrt hb
  have he : q = l1 q • r := by
    dsimp [r]
    rw [smul_smul, mul_one_div_cancel hl, one_smul]
  calc
    ‖featureMap q‖ = l1 q * ‖featureMap r‖ := by
      conv_lhs => rw [he, map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hp]
    _ ≤ l1 q * Real.sqrt (6/7) := mul_le_mul_of_nonneg_left hnorm hp.le
    _ = _ := mul_comm _ _

/-- Exact evaluation: `vᵀWv < (15/8)²` for the corrector `v`. -/
theorem correctionVQ_quadratic_lt : quadraticQ correctionVQ < 225/64 := by
  decide +kernel

theorem correctionV_norm_le : ‖featureMap correctionV‖ ≤ 15/8 := by
  have hv : quadratic correctionV < 225/64 := by
    unfold correctionV
    rw [quadratic_cast]
    have hc := Rat.cast_lt (K := ℝ).mpr correctionVQ_quadratic_lt
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at hc
    exact hc
  nlinarith [featureMap_norm_sq correctionV, norm_nonneg (featureMap correctionV)]

theorem sqrt_six_sevenths_lt : Real.sqrt (6/7) < 13/14 := by
  rw [Real.sqrt_lt' (by norm_num)]
  norm_num

/-- The corrected seminorm estimate of Lemma 5.18:
`√(qᵀWq) ≤ √(6/7) y + K |q₀|` with `K = 15/8 + (13/14)(13/11) = 1831/616`. -/
theorem corrected_seminorm_bound_sharp (q : Count → ℝ) (hmass : (∑ j : Count, q j) = 0)
    (hmean : mean q = 0) :
    Real.sqrt (quadratic q) ≤
      Real.sqrt (6/7) * (∑ j ∈ Finset.univ.erase (0:Count), |q j|) + (1831/616) * |q 0| := by
  let r := q - q 0 • correctionV
  obtain ⟨hv0, -, hvm, hvx, -, -⟩ := correcting_real_constraints
  have hr0 : r 0 = 0 := by simp [r, hv0]
  have hrm : (∑ j : Count, r j) = 0 := by
    simp [r, Finset.sum_sub_distrib, ← Finset.mul_sum, hmass, hvm]
  have hrx : mean r = 0 := by
    dsimp [r]
    rw [mean_sub, mean_smul, hvx, hmean]
    ring
  have hnr := zero_coordinate_seminorm_bound_sharp hr0 hrm hrx
  have hl := corrected_l1_bound q
  rw [hmean, zero_smul, sub_zero, abs_zero, mul_zero, add_zero] at hl
  change l1 r ≤ _ at hl
  have hdecomp : q = r + q 0 • correctionV := by dsimp [r]; module
  have htri : ‖featureMap q‖ ≤ ‖featureMap r‖ + |q 0| * ‖featureMap correctionV‖ := by
    conv_lhs => rw [hdecomp, map_add, map_smul]
    have h := norm_add_le (featureMap r) (q 0 • featureMap correctionV)
    simp only [norm_smul, Real.norm_eq_abs] at h ⊢
    linarith
  have hv := mul_le_mul_of_nonneg_left correctionV_norm_le (abs_nonneg (q 0))
  have hs := sqrt_six_sevenths_lt
  have hs0 := Real.sqrt_nonneg (6/7)
  have hr := mul_le_mul_of_nonneg_left hl hs0
  rw [featureMap_norm] at htri
  nlinarith [mul_nonneg (sub_nonneg.mpr hs.le) (abs_nonneg (q 0))]

/-- The Cauchy–Schwarz step: `(√(6/7) y + K a)² ≤ κ (y² + 4096 a²)`, `κ < 43/50`. -/
theorem curvature_cauchy_sharp (y a S : ℝ) (hS : y^2 + 4096 * a^2 ≤ S) :
    (Real.sqrt (6/7) * y + (1831/616) * a)^2 ≤ (43/50) * S := by
  have hs : Real.sqrt (6/7)^2 = (6/7:ℝ) := Real.sq_sqrt (by norm_num)
  have he : (6/7 + (1831/616)^2/4096) * (y^2 + 4096 * a^2) -
      (Real.sqrt (6/7) * y + (1831/616) * a)^2 =
      (64 * Real.sqrt (6/7) * a - (1831/616)/64 * y)^2 := by
    ring_nf
    rw [hs]
    ring
  have hh := sq_nonneg (64 * Real.sqrt (6/7) * a - (1831/616)/64 * y)
  rw [← he] at hh
  have hk : (6/7 + (1831/616)^2/4096 : ℝ) ≤ 43/50 := by norm_num
  have hS0 : 0 ≤ y^2 + 4096 * a^2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hk hS0]

/-- Lemma 5.18 (lem:section5-global-curvature), eq:section5-global-fixed-curvature:
`qᵀWq ≤ (43/50) Σ q_j²/p_j` for mass-zero, mean-zero `q` and positive feasible `p`. -/
theorem fixed_mean_curvature_sharp {p q : Count → ℝ}
    (hp : Feasible p) (hpos : ∀ j, 0 < p j)
    (hmass : (∑ j : Count, q j) = 0) (hmean : mean q = 0) :
    quadratic q ≤ (43/50) * ∑ j : Count, q j^2 / p j := by
  let y := ∑ j ∈ Finset.univ.erase (0:Count), |q j|
  let S := ∑ j : Count, q j^2 / p j
  have hy : 0 ≤ y := Finset.sum_nonneg (fun j _ => abs_nonneg _)
  have hc := curvature_cauchy_sharp y |q 0| S (curvature_denominator_lower hp hpos)
  have hn := corrected_seminorm_bound_sharp q hmass hmean
  have hu : 0 ≤ Real.sqrt (6/7) * y + (1831/616) * |q 0| := by positivity
  have hsq := (sq_le_sq₀ (Real.sqrt_nonneg (quadratic q)) hu).mpr hn
  rw [Real.sq_sqrt (quadratic_nonneg q)] at hsq
  exact hsq.trans hc

end BecknerOnofri.HighDim.Spin
