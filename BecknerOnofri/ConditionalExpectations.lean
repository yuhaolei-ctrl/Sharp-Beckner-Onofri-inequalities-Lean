module

public import BecknerOnofri.ConditionalMoments

@[expose] public section

/-! Expressing conditional entropy and moments as expectations under the
original joint density, as in the manuscript's chain-and-Jensen formula. -/

noncomputable section
open MeasureTheory Function
open scoped BigOperators

namespace BecknerOnofri.HighDim.ConditionalEntropy
open EntropyShearer

theorem prefix_congr {d : ℕ} (f : Torus d → ℝ) (k : ℕ) {x y : Torus d}
    (hxy : ∀ j : Fin d, j.val < k → x j = y j) :
    prefixDensity f k x = prefixDensity f k y := by
  unfold prefixDensity
  apply integral_congr_ae
  filter_upwards [] with z
  congr 1
  funext j
  unfold updateFinset
  split_ifs with hj
  · rfl
  · exact hxy j (Nat.lt_of_not_ge (fun h => hj (mem_suffixCoordinates.mpr h)))

theorem conditional_density_prefix_congr {d : ℕ} (f : Torus d → ℝ) (i : Fin d)
    {x y : Torus d} (hxy : ∀ j : Fin d, j.val < i.val → x j = y j) :
    conditionalDensity f i x = conditionalDensity f i y := by
  funext z
  unfold conditionalDensity
  rw [prefix_congr f i.val hxy]
  congr 1
  apply prefix_congr
  intro j hj
  by_cases he : j = i
  · subst j; simp
  · rw [Function.update_of_ne he, Function.update_of_ne he]
    apply hxy j
    have hne : j.val ≠ i.val := fun h => he (Fin.ext h)
    omega

theorem conditional_entropy_bounded {d : ℕ} {f : Torus d → ℝ}
    (hf : PositiveBounded f) (i : Fin d) :
    BoundedMeasurable (conditionalEntropy f i) := by
  have ha := prefix_positive hf (i.val + 1)
  have hb := prefix_positive hf i.val
  have he : conditionalEntropy f i = fun x =>
      avg {i} (fun y => prefixDensity f (i.val + 1) y *
        (Real.log (prefixDensity f (i.val + 1) y) - Real.log (prefixDensity f i.val y))) x *
      (prefixDensity f i.val x)⁻¹ := by
    funext x
    rw [← conditional_entropy_weighted hf i x]
    field_simp [(hb.pos x).ne']
  rw [he]
  exact ((ha.bounded.mul (ha.logBounded.sub hb.logBounded)).avg {i}).mul hb.invBounded

theorem conditional_density_suffix_update {d : ℕ} (f : Torus d → ℝ) (i : Fin d)
    (x : Torus d) (y : suffixCoordinates d i.val → UnitAddCircle) :
    conditionalDensity f i (updateFinset x (suffixCoordinates d i.val) y) =
      conditionalDensity f i x := by
  apply conditional_density_prefix_congr
  intro j hj
  simp [updateFinset, Nat.not_le_of_lt hj]

theorem conditional_entropy_expectation {d : ℕ} {f : Torus d → ℝ}
    (hf : PositiveBounded f) (i : Fin d) :
    (∫ x, f x * conditionalEntropy f i x ∂torusMeasure d) =
      ∫ x, prefixDensity f i.val x * conditionalEntropy f i x ∂torusMeasure d := by
  apply integral_pairing (suffixCoordinates d i.val) hf.bounded
    (conditional_entropy_bounded hf i)
  intro x y
  simp only [conditionalEntropy, conditional_density_suffix_update]

theorem entropy_chain_rule_full {d : ℕ} {f : Torus d → ℝ}
    (hf : PositiveBounded f) (hmass : (∫ x, f x ∂torusMeasure d) = 1) :
    (∫ x, f x * Real.log (f x) ∂torusMeasure d) =
      ∑ i : Fin d, ∫ x, f x * conditionalEntropy f i x ∂torusMeasure d := by
  simp_rw [conditional_entropy_expectation hf]
  exact entropy_chain_rule hf hmass

theorem conditional_moment_full_tower {d : ℕ} {f : Torus d → ℝ}
    (hf : PositiveBounded f) (i : Fin d) (n : ℕ) :
    (∫ x, f x * conditionalCosineMoment f i n x ∂torusMeasure d) =
      ∫ x, f x * (fourier (n : ℤ) (x i)).re ∂torusMeasure d := by
  rw [integral_pairing (suffixCoordinates d i.val) hf.bounded
    (conditional_moment_bounded hf i n) (fun x y => by
      simp only [conditionalCosineMoment, conditional_density_suffix_update])]
  exact conditional_moment_tower hf i n

theorem conditional_moment_full_square {d : ℕ} {f : Torus d → ℝ}
    (hf : PositiveBounded f) (hm : (∫ x, f x ∂torusMeasure d) = 1)
    (i : Fin d) (n : ℕ) :
    (∫ x, f x * (fourier (n : ℤ) (x i)).re ∂torusMeasure d) ^ 2 ≤
      ∫ x, f x * (conditionalCosineMoment f i n x) ^ 2 ∂torusMeasure d := by
  rw [← conditional_moment_full_tower hf i n]
  exact weighted_square_jensen hf (conditional_moment_bounded hf i n) hm

#print axioms entropy_chain_rule_full
#print axioms conditional_moment_full_square

end BecknerOnofri.HighDim.ConditionalEntropy
