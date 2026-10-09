module

public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.MeasureTheory.Measure.WithDensity

@[expose] public section

/-! # Sequence-level inequalities for the Sobolev algebra estimate

All statements are for `ℝ≥0∞`-valued series, so no summability hypotheses occur.

* `tsum_mul_sq_le` : weighted Cauchy-Schwarz `(∑ x g)² ≤ (∑ g)(∑ x² g)`;
* `tsum_mul_le_rpow` : Cauchy-Schwarz `∑ x y ≤ (∑ x²)^{1/2} (∑ y²)^{1/2}`;
* `tsum_sq_tsum_le` : Minkowski for a countable sum of sequences in `ℓ²`;
* `tsum_convE_sq_le` : Young's inequality `‖f * g‖₂ ≤ ‖f‖₂ ‖g‖₁` in squared form.

These are the analytic core of the Banach-algebra property of `H^s(𝕋^d)`, `s > d/2`
(Appendix-free; used for the Sobolev bootstrap in the proof of Proposition 5.24). -/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace BecknerOnofri.V2.Onset

/-- `(A^{1/2})² = A` in `ℝ≥0∞`. -/
theorem rpow_half_sq (A : ℝ≥0∞) : (A ^ (1 / 2 : ℝ)) ^ 2 = A := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num

/-- Weighted Cauchy-Schwarz for `ℝ≥0∞`-valued series. -/
theorem tsum_mul_sq_le {ι : Type*} (x g : ι → ℝ≥0∞) :
    (∑' i, x i * g i) ^ 2 ≤ (∑' i, g i) * (∑' i, x i ^ 2 * g i) := by
  classical
  let _ : MeasurableSpace ι := ⊤
  have _ : MeasurableSingletonClass ι := ⟨fun _ => trivial⟩
  set μ : Measure ι := Measure.count.withDensity g with hμ
  have hx : Measurable x := measurable_from_top
  have hg : Measurable g := measurable_from_top
  have h1 : ∫⁻ i, x i ∂μ = ∑' i, x i * g i := by
    rw [hμ, lintegral_withDensity_eq_lintegral_mul₀ hg.aemeasurable hx.aemeasurable,
      lintegral_count]
    simp [mul_comm]
  have h2 : ∫⁻ i, x i ^ (2:ℝ) ∂μ = ∑' i, x i ^ 2 * g i := by
    rw [hμ, lintegral_withDensity_eq_lintegral_mul₀ hg.aemeasurable (hx.pow_const _).aemeasurable,
      lintegral_count]
    simp [mul_comm]
  have h3 : ∫⁻ i, (1:ι → ℝ≥0∞) i ^ (2:ℝ) ∂μ = ∑' i, g i := by
    rw [hμ, lintegral_withDensity_eq_lintegral_mul₀ hg.aemeasurable (by fun_prop), lintegral_count]
    simp
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq μ (Real.HolderConjugate.two_two) (f := x)
    (g := 1) hx.aemeasurable (by fun_prop)
  rw [h2, h3] at hH
  simp only [Pi.mul_apply, Pi.one_apply, mul_one] at hH
  rw [h1] at hH
  have := pow_le_pow_left' hH 2
  rw [mul_pow, rpow_half_sq, rpow_half_sq] at this
  rwa [mul_comm] at this

/-- Cauchy-Schwarz for `ℝ≥0∞`-valued series. -/
theorem tsum_mul_le_rpow {ι : Type*} (x y : ι → ℝ≥0∞) :
    ∑' i, x i * y i ≤ (∑' i, x i ^ 2) ^ (1 / 2 : ℝ) * (∑' i, y i ^ 2) ^ (1 / 2 : ℝ) := by
  classical
  let _ : MeasurableSpace ι := ⊤
  have _ : MeasurableSingletonClass ι := ⟨fun _ => trivial⟩
  have hx : Measurable x := measurable_from_top
  have hy : Measurable y := measurable_from_top
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq (Measure.count : Measure ι)
    (Real.HolderConjugate.two_two) (f := x) (g := y) hx.aemeasurable hy.aemeasurable
  simp only [lintegral_count, Pi.mul_apply] at hH
  simpa using hH

variable {G : Type*} [AddCommGroup G]

/-- Convolution of `ℝ≥0∞`-valued sequences on a discrete abelian group. -/
def convE (f g : G → ℝ≥0∞) (k : G) : ℝ≥0∞ := ∑' l, f (k - l) * g l

theorem convE_comm (f g : G → ℝ≥0∞) : convE f g = convE g f := by
  funext k
  unfold convE
  rw [← (Equiv.subLeft k).tsum_eq]
  refine tsum_congr fun l => ?_
  simp [mul_comm]

/-- Young's inequality `ℓ² * ℓ¹ ⊂ ℓ²`, in squared form. -/
theorem tsum_convE_sq_le (f g : G → ℝ≥0∞) :
    ∑' k, (convE f g k) ^ 2 ≤ (∑' l, f l ^ 2) * (∑' l, g l) ^ 2 := by
  have h1 : ∀ k, (convE f g k) ^ 2 ≤ (∑' l, g l) * ∑' l, f (k - l) ^ 2 * g l := fun k =>
    tsum_mul_sq_le (fun l => f (k - l)) g
  calc ∑' k, (convE f g k) ^ 2 ≤ ∑' k, (∑' l, g l) * ∑' l, f (k - l) ^ 2 * g l :=
        ENNReal.tsum_le_tsum h1
    _ = (∑' l, g l) * ∑' l, g l * ∑' k, f (k - l) ^ 2 := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_comm]
        congr 1
        refine tsum_congr fun l => ?_
        rw [← ENNReal.tsum_mul_left]
        exact tsum_congr fun k => mul_comm _ _
    _ = (∑' l, f l ^ 2) * (∑' l, g l) ^ 2 := by
        have hs (l : G) : ∑' k, f (k - l) ^ 2 = ∑' k, f k ^ 2 :=
          (Equiv.subRight l).tsum_eq (fun k => f k ^ 2)
        simp only [hs, ENNReal.tsum_mul_right]
        ring

omit [AddCommGroup G] in
/-- Minkowski's inequality for a countable sum of sequences, in squared form. -/
theorem tsum_sq_tsum_le {N : Type*} (g : N → G → ℝ≥0∞) :
    ∑' k, (∑' n, g n k) ^ 2 ≤ (∑' n, (∑' k, g n k ^ 2) ^ (1 / 2 : ℝ)) ^ 2 := by
  have h1 : ∀ k, (∑' n, g n k) ^ 2 = ∑' n, ∑' m, g n k * g m k := fun k => by
    rw [sq, ← ENNReal.tsum_mul_right]
    exact tsum_congr fun n => by rw [← ENNReal.tsum_mul_left]
  calc ∑' k, (∑' n, g n k) ^ 2 = ∑' k, ∑' n, ∑' m, g n k * g m k := tsum_congr h1
    _ = ∑' n, ∑' m, ∑' k, g n k * g m k := by
        rw [ENNReal.tsum_comm]
        refine tsum_congr fun n => ?_
        rw [ENNReal.tsum_comm]
    _ ≤ ∑' n, ∑' m, (∑' k, g n k ^ 2) ^ (1 / 2 : ℝ) * (∑' k, g m k ^ 2) ^ (1 / 2 : ℝ) :=
        ENNReal.tsum_le_tsum fun n => ENNReal.tsum_le_tsum fun m =>
          tsum_mul_le_rpow (fun k => g n k) (fun k => g m k)
    _ = (∑' n, (∑' k, g n k ^ 2) ^ (1 / 2 : ℝ)) ^ 2 := by
        rw [sq, ← ENNReal.tsum_mul_right]
        exact tsum_congr fun n => by rw [← ENNReal.tsum_mul_left]

end BecknerOnofri.V2.Onset
