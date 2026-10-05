import Legacy.TorusEndpoint.TorusFourier
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-!
# Exact aliasing on the uniform torus grid

The grid is the actual image of `(ZMod N)^d` in the unit flat torus.
No quadrature or character-orthogonality hypothesis is assumed.
-/

open scoped BigOperators ComplexConjugate

namespace Legacy.TorusEndpoint

noncomputable def gridPoint {d N : ℕ} [NeZero N]
    (j : Fin d → ZMod N) : Torus d :=
  fun i => ZMod.toAddCircle (j i)

theorem fourier_grid_coordinate {N : ℕ} [NeZero N] (k : ℤ) (j : ZMod N) :
    fourier k (ZMod.toAddCircle j) = ZMod.stdAddChar ((k : ZMod N) * j) := by
  rw [fourier_apply, ← map_zsmul, zsmul_eq_mul]
  rfl

theorem grid_coordinate_orthogonality {N : ℕ} [NeZero N] (k : ℤ) :
    (∑ j : ZMod N, fourier k (ZMod.toAddCircle j)) =
      if (k : ZMod N) = 0 then (N : ℂ) else 0 := by
  simp_rw [fourier_grid_coordinate, mul_comm (k : ZMod N)]
  simpa only [ZMod.card, Nat.cast_ite, Nat.cast_zero] using
    AddChar.sum_mulShift (k : ZMod N) (ZMod.isPrimitive_stdAddChar N)

theorem grid_character_orthogonality {d N : ℕ} [NeZero N] (k : Frequency d) :
    (∑ j : Fin d → ZMod N, UnitAddTorus.mFourier k (gridPoint j)) =
      if (∀ i, (k i : ZMod N) = 0) then (N : ℂ) ^ d else 0 := by
  classical
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, gridPoint]
  rw [← Fintype.prod_sum (fun (i : Fin d) (j : ZMod N) =>
    fourier (k i) (ZMod.toAddCircle j))]
  simp_rw [grid_coordinate_orthogonality]
  split_ifs with h
  · simp [h]
  · push Not at h
    obtain ⟨i, hi⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

noncomputable def gridAverage {d N : ℕ} [NeZero N] (f : Torus d → ℂ) : ℂ :=
  ((N : ℂ) ^ d)⁻¹ * ∑ j : Fin d → ZMod N, f (gridPoint j)

theorem grid_average_character {d N : ℕ} [NeZero N] (k : Frequency d) :
    gridAverage (N := N) (UnitAddTorus.mFourier k) =
      if (∀ i, (k i : ZMod N) = 0) then 1 else 0 := by
  classical
  rw [gridAverage, grid_character_orthogonality]
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  split_ifs <;> simp [hN]

theorem grid_average_shifted_character {d N : ℕ} [NeZero N]
    (k r : Frequency d) :
    gridAverage (N := N) (fun x =>
      UnitAddTorus.mFourier k x * UnitAddTorus.mFourier (-r) x) =
      if (∀ i, (k i : ZMod N) = (r i : ZMod N)) then 1 else 0 := by
  classical
  simp_rw [← UnitAddTorus.mFourier_add]
  rw [grid_average_character]
  simp only [Pi.add_apply, Pi.neg_apply, ← sub_eq_add_neg, Int.cast_sub, sub_eq_zero]

theorem grid_average_sum {d N : ℕ} [NeZero N] {ι : Type*}
    (s : Finset ι) (f : ι → Torus d → ℂ) :
    gridAverage (N := N) (fun x => ∑ i ∈ s, f i x) =
      ∑ i ∈ s, gridAverage (N := N) (f i) := by
  simp only [gridAverage]
  rw [Finset.sum_comm, Finset.mul_sum]

theorem grid_average_mul_const {d N : ℕ} [NeZero N]
    (a : ℂ) (f : Torus d → ℂ) :
    gridAverage (N := N) (fun x => a * f x) = a * gridAverage (N := N) f := by
  simp only [gridAverage, ← Finset.mul_sum]
  ring

/-- Exact finite Fourier aliasing: only congruent frequencies survive. -/
theorem finite_grid_aliasing {d N : ℕ} [NeZero N]
    (s : Finset (Frequency d)) (c : Frequency d → ℂ) (r : Frequency d) :
    gridAverage (N := N) (fun x => fourierPolynomial s c x *
      UnitAddTorus.mFourier (-r) x) =
      ∑ k ∈ s, if (∀ i, (k i : ZMod N) = (r i : ZMod N)) then c k else 0 := by
  classical
  simp only [fourierPolynomial, ContinuousMap.sum_apply, ContinuousMap.smul_apply,
    smul_eq_mul, Finset.sum_mul, mul_assoc]
  rw [grid_average_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [grid_average_mul_const, grid_average_shifted_character]
  split_ifs <;> simp

theorem mFourier_norm_apply {d : ℕ} (k : Frequency d) (x : Torus d) :
    ‖UnitAddTorus.mFourier k x‖ = 1 := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, norm_prod,
    fourier_apply, Circle.norm_coe, Finset.prod_const_one]

noncomputable def absoluteFourierSeries {d : ℕ} (c : Frequency d → ℂ) : Torus d → ℂ :=
  fun x => ∑' k, c k * UnitAddTorus.mFourier k x

theorem summable_fourierSeries_apply {d : ℕ} (c : Frequency d → ℂ)
    (hc : Summable (fun k => ‖c k‖)) (x : Torus d) :
    Summable (fun k => c k * UnitAddTorus.mFourier k x) := by
  apply hc.of_norm_bounded
  intro k
  simp only [norm_mul, mFourier_norm_apply, mul_one, le_refl]

theorem grid_average_tsum {d N : ℕ} [NeZero N] {ι : Type*}
    (f : ι → Torus d → ℂ)
    (hf : ∀ j : Fin d → ZMod N, Summable (fun k => f k (gridPoint j))) :
    HasSum (fun k => gridAverage (N := N) (f k))
      (gridAverage (N := N) (fun x => ∑' k, f k x)) := by
  classical
  have h := hasSum_sum (s := Finset.univ) (fun j _ => (hf j).hasSum)
  exact h.mul_left (((N : ℂ) ^ d)⁻¹)

/-- Exact aliasing for an absolutely summable Fourier series on the actual
unit torus. The full congruence class, including all aliases, is summed. -/
theorem absolute_grid_aliasing {d N : ℕ} [NeZero N]
    (c : Frequency d → ℂ) (hc : Summable (fun k => ‖c k‖)) (r : Frequency d) :
    gridAverage (N := N) (fun x => absoluteFourierSeries c x *
      UnitAddTorus.mFourier (-r) x) =
      ∑' k, if (∀ i, (k i : ZMod N) = (r i : ZMod N)) then c k else 0 := by
  classical
  have h := grid_average_tsum (N := N)
    (fun k x => c k * UnitAddTorus.mFourier k x * UnitAddTorus.mFourier (-r) x)
    (fun j => (summable_fourierSeries_apply c hc (gridPoint j)).mul_right _)
  have heq (k : Frequency d) :
      gridAverage (N := N) (fun x => c k * UnitAddTorus.mFourier k x *
        UnitAddTorus.mFourier (-r) x) =
        if (∀ i, (k i : ZMod N) = (r i : ZMod N)) then c k else 0 := by
    simp_rw [mul_assoc]
    rw [grid_average_mul_const, grid_average_shifted_character]
    split_ifs <;> simp
  simp_rw [heq] at h
  rw [h.tsum_eq]
  congr 1
  funext x
  exact (summable_fourierSeries_apply c hc x).tsum_mul_right _ |>.symm

/-- Positive aliasing: a nonnegative Fourier coefficient is at most the
real part of its exact discrete Fourier average, without a grid-error term. -/
theorem nonnegative_coefficient_le_grid_average {d N : ℕ} [NeZero N]
    (c : Frequency d → ℝ) (hc : Summable c) (hpos : ∀ k, 0 ≤ c k)
    (r : Frequency d) :
    c r ≤ (gridAverage (N := N) (fun x =>
      absoluteFourierSeries (fun k => (c k : ℂ)) x *
        UnitAddTorus.mFourier (-r) x)).re := by
  classical
  have hnorm : Summable (fun k => ‖(c k : ℂ)‖) := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hpos _)] using hc
  rw [absolute_grid_aliasing _ hnorm]
  have hs : Summable (fun k =>
      if (∀ i, (k i : ZMod N) = (r i : ZMod N)) then (c k : ℂ) else 0) := by
    apply hc.of_norm_bounded
    intro k
    split_ifs <;> simp [hpos k, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
  rw [Complex.re_tsum hs]
  have hh := (Complex.hasSum_re hs.hasSum).summable
  have hle := hh.le_tsum r (fun k _ => by
    split_ifs <;> simp [hpos k])
  simpa using hle

/-- A continuous function with summable actual Fourier coefficients is
represented pointwise, including at every grid point, by this series. -/
theorem absoluteFourierSeries_actual_coefficients {d : ℕ}
    (f : C(Torus d, ℂ)) (hf : Summable (UnitAddTorus.mFourierCoeff f)) :
    absoluteFourierSeries (UnitAddTorus.mFourierCoeff f) = f := by
  funext x
  simpa only [absoluteFourierSeries, smul_eq_mul] using
    (UnitAddTorus.hasSum_mFourier_series_apply_of_summable hf x).tsum_eq

theorem continuous_grid_aliasing {d N : ℕ} [NeZero N]
    (f : C(Torus d, ℂ)) (hf : Summable (UnitAddTorus.mFourierCoeff f))
    (r : Frequency d) :
    gridAverage (N := N) (fun x => f x * UnitAddTorus.mFourier (-r) x) =
      ∑' k, if (∀ i, (k i : ZMod N) = (r i : ZMod N)) then
        UnitAddTorus.mFourierCoeff f k else 0 := by
  simpa only [absoluteFourierSeries_actual_coefficients f hf] using
    absolute_grid_aliasing (N := N) (UnitAddTorus.mFourierCoeff f) hf.norm r

theorem continuous_coefficient_le_grid_average {d N : ℕ} [NeZero N]
    (f : C(Torus d, ℂ)) (hf : Summable (UnitAddTorus.mFourierCoeff f))
    (hpos : ∀ k, 0 ≤ (UnitAddTorus.mFourierCoeff f k).re)
    (r : Frequency d) :
    (UnitAddTorus.mFourierCoeff f r).re ≤
      (gridAverage (N := N) (fun x => f x * UnitAddTorus.mFourier (-r) x)).re := by
  classical
  rw [continuous_grid_aliasing f hf r]
  have hs : Summable (fun k => if (∀ i, (k i : ZMod N) = (r i : ZMod N)) then
      UnitAddTorus.mFourierCoeff f k else 0) := by
    apply hf.norm.of_norm_bounded
    intro k
    split_ifs <;> simp
  rw [Complex.re_tsum hs]
  have hle := (Complex.hasSum_re hs.hasSum).summable.le_tsum r (fun k _ => by
    split_ifs <;> simp [hpos k])
  simpa using hle

/-- The exact zero-mode upper bound used by positive grid certificates. -/
theorem integral_le_grid_average {d N : ℕ} [NeZero N]
    (f : C(Torus d, ℂ)) (hf : Summable (UnitAddTorus.mFourierCoeff f))
    (hpos : ∀ k, 0 ≤ (UnitAddTorus.mFourierCoeff f k).re) :
    (∫ x, f x ∂torusMeasure d).re ≤ (gridAverage (N := N) f).re := by
  simpa only [UnitAddTorus.mFourierCoeff, neg_zero, UnitAddTorus.mFourier_zero,
    ContinuousMap.one_apply, one_smul, mul_one, torusMeasure] using
    continuous_coefficient_le_grid_average (N := N) f hf hpos 0

theorem gridAverage_re {d N : ℕ} [NeZero N] (f : Torus d → ℂ) :
    (gridAverage (N := N) f).re =
      ((N : ℝ) ^ d)⁻¹ * ∑ j : Fin d → ZMod N, (f (gridPoint j)).re := by
  unfold gridAverage
  have hcast : ((N : ℂ) ^ d)⁻¹ = (((N : ℝ) ^ d)⁻¹ : ℝ) := by
    push_cast
    rfl
  rw [hcast]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, Complex.re_sum]

/-- Only values on the actual grid are needed to compare discrete upper bounds. -/
theorem gridAverage_re_mono {d N : ℕ} [NeZero N] (f g : Torus d → ℂ)
    (h : ∀ j : Fin d → ZMod N, (f (gridPoint j)).re ≤ (g (gridPoint j)).re) :
    (gridAverage (N := N) f).re ≤ (gridAverage (N := N) g).re := by
  rw [gridAverage_re, gridAverage_re]
  apply mul_le_mul_of_nonneg_left
  · exact Finset.sum_le_sum (fun j _ => h j)
  · positivity

theorem integral_le_certified_grid_upper {d N : ℕ} [NeZero N]
    (f : C(Torus d, ℂ)) (hf : Summable (UnitAddTorus.mFourierCoeff f))
    (hpos : ∀ k, 0 ≤ (UnitAddTorus.mFourierCoeff f k).re)
    (u : (Fin d → ZMod N) → ℝ)
    (hu : ∀ j, (f (gridPoint j)).re ≤ u j) :
    (∫ x, f x ∂torusMeasure d).re ≤
      ((N : ℝ) ^ d)⁻¹ * ∑ j, u j := by
  apply (integral_le_grid_average (N := N) f hf hpos).trans
  rw [gridAverage_re]
  apply mul_le_mul_of_nonneg_left
  · exact Finset.sum_le_sum (fun j _ => hu j)
  · positivity

end Legacy.TorusEndpoint
