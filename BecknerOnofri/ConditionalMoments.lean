module

public import BecknerOnofri.ConditionalEntropyChain

@[expose] public section

/-! The tower identity and square Jensen inequality for actual conditional
cosine moments. All expectations use the actual prefix Haar density. -/

noncomputable section
open MeasureTheory Function
open scoped BigOperators

namespace BecknerOnofri.HighDim.ConditionalEntropy
open EntropyShearer

theorem cosine_bounded {d : ℕ} (i : Fin d) (n : ℕ) :
    BoundedMeasurable (fun x : Torus d => (fourier (n : ℤ) (x i)).re) := by
  refine ⟨(Complex.continuous_re.comp
    ((map_continuous (fourier (n : ℤ))).comp (continuous_apply i))).measurable,
    1, fun x => ?_⟩
  calc
    _ = |(fourier (n : ℤ) (x i)).re| := Real.norm_eq_abs _
    _ ≤ ‖fourier (n : ℤ) (x i)‖ := Complex.abs_re_le_norm _
    _ = 1 := by simp [fourier_apply]

theorem conditional_moment_formula {d : ℕ} (f : Torus d → ℝ)
    (i : Fin d) (n : ℕ) :
    conditionalCosineMoment f i n = fun x =>
      avg {i} (fun y => prefixDensity f (i.val + 1) y *
        (fourier (n : ℤ) (y i)).re) x / prefixDensity f i.val x := by
  funext x
  rw [avg_singleton]
  simp only [conditionalCosineMoment, conditionalDensity, Function.update_self]
  simp_rw [div_mul_eq_mul_div]
  rw [integral_div]

theorem conditional_moment_bounded {d : ℕ} {f : Torus d → ℝ}
    (hf : PositiveBounded f) (i : Fin d) (n : ℕ) :
    BoundedMeasurable (conditionalCosineMoment f i n) := by
  rw [conditional_moment_formula f]
  simpa only [div_eq_mul_inv] using
    (((prefix_positive hf (i.val + 1)).bounded.mul (cosine_bounded i n)).avg {i}).mul
      (prefix_positive hf i.val).invBounded

theorem prefix_mass {d : ℕ} {f : Torus d → ℝ}
    (hf : BoundedMeasurable f) (k : ℕ) :
    (∫ x, prefixDensity f k x ∂torusMeasure d) = ∫ x, f x ∂torusMeasure d :=
  integral_avg _ hf

theorem conditional_moment_tower {d : ℕ} {f : Torus d → ℝ}
    (hf : PositiveBounded f) (i : Fin d) (n : ℕ) :
    (∫ x, prefixDensity f i.val x * conditionalCosineMoment f i n x ∂torusMeasure d) =
      ∫ x, f x * (fourier (n : ℤ) (x i)).re ∂torusMeasure d := by
  rw [conditional_moment_formula f]
  have hc := cosine_bounded i n
  calc
    _ = ∫ x, avg {i} (fun y => prefixDensity f (i.val + 1) y *
          (fourier (n : ℤ) (y i)).re) x ∂torusMeasure d := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact mul_div_cancel₀ _ ((prefix_positive hf i.val).pos x).ne'
    _ = ∫ x, prefixDensity f (i.val + 1) x * (fourier (n : ℤ) (x i)).re
        ∂torusMeasure d := integral_avg _ ((prefix_positive hf _).bounded.mul hc)
    _ = _ := (integral_pairing (suffixCoordinates d (i.val + 1)) hf.bounded hc
      (fun x y => by
        have hi : i ∉ suffixCoordinates d (i.val + 1) := by simp
        simp [Function.updateFinset, hi])).symm

theorem weighted_square_jensen {d : ℕ} {b u : Torus d → ℝ}
    (hb : PositiveBounded b) (hu : BoundedMeasurable u)
    (hm : (∫ x, b x ∂torusMeasure d) = 1) :
    (∫ x, b x * u x ∂torusMeasure d) ^ 2 ≤
      ∫ x, b x * (u x) ^ 2 ∂torusMeasure d := by
  let m := ∫ x, b x * u x ∂torusMeasure d
  have hi : Integrable (fun x => b x * u x ^ 2) (torusMeasure d) := by
    simpa only [pow_two] using (hb.bounded.mul (hu.mul hu)).integrable
  have hlin : Integrable (fun x => b x * u x) (torusMeasure d) :=
    (hb.bounded.mul hu).integrable
  have hnonneg : 0 ≤ ∫ x, b x * (u x - m) ^ 2 ∂torusMeasure d :=
    integral_nonneg (fun x => mul_nonneg (hb.pos x).le (sq_nonneg _))
  have he (x : Torus d) : b x * (u x - m) ^ 2 =
      b x * u x ^ 2 - (b x * u x) * (2 * m) + b x * m ^ 2 := by ring
  simp_rw [he] at hnonneg
  rw [integral_add (f := fun x => b x * u x ^ 2 - (b x * u x) * (2 * m))
      (g := fun x => b x * m ^ 2) (hi.sub (hlin.mul_const (2 * m)))
      (hb.bounded.integrable.mul_const (m ^ 2)),
    integral_sub hi (hlin.mul_const (2 * m)), integral_mul_const, integral_mul_const, hm] at hnonneg
  change m ^ 2 ≤ _
  change 0 ≤ (∫ x, b x * u x ^ 2 ∂torusMeasure d) - m * (2 * m) + 1 * m ^ 2 at hnonneg
  nlinarith

theorem conditional_moment_square {d : ℕ} {f : Torus d → ℝ}
    (hf : PositiveBounded f) (hm : (∫ x, f x ∂torusMeasure d) = 1)
    (i : Fin d) (n : ℕ) :
    (∫ x, f x * (fourier (n : ℤ) (x i)).re ∂torusMeasure d) ^ 2 ≤
      ∫ x, prefixDensity f i.val x * (conditionalCosineMoment f i n x) ^ 2
        ∂torusMeasure d := by
  rw [← conditional_moment_tower hf i n]
  exact weighted_square_jensen (prefix_positive hf _) (conditional_moment_bounded hf i n)
    ((prefix_mass hf.bounded _).trans hm)

#print axioms conditional_moment_tower
#print axioms conditional_moment_square

end BecknerOnofri.HighDim.ConditionalEntropy
