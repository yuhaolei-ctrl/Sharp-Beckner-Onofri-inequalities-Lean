module

public import BecknerOnofri.Definitions
public import BecknerOnofri.V2.Transfer.Characters
public import BecknerOnofri.Uniform
public import BecknerOnofri.CosineMixtureStatementDefinitions

@[expose] public section

/-! # Remark 5.6: the explicit arbitrary-density counterexample (character computations)

Source: `rem:spectral-energy-restriction`.  For `d ≥ 1` and `0 < |ε| < 1` the density is

  `ρ_ε(x) = 1 + ε cos(2π(x_1 + ⋯ + x_d))`  on `𝕋^d`.

The cosine is written through the Mathlib character `UnitAddTorus.mFourier`, namely
`sumCos d x = Re (mFourier (1,…,1) x)`; `sumCos_coe` proves that this is literally
`Real.cos (2π (t_1 + ⋯ + t_d))` on every real lift `t` of `x`.

This file proves the character integrals, the exact Fourier coefficients of `ρ_ε` and the fact
that every coordinate marginal over a strict subset of the coordinates is identically one.  The
density structure, positivity, smoothness, the value of the full interaction and the contradiction
with the claimed unrestricted inequalities are in `Remark56`. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace BecknerOnofri.V2.Transfer
open BecknerOnofri.HighDim

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

/-- The all-ones frequency `(1,…,1)`. -/
def onesFreq (d : ℕ) : Frequency d := fun _ => 1

/-- The indicator frequency of a set of coordinates. -/
def indFreq {d : ℕ} (S : Finset (Fin d)) : Frequency d := fun i => if i ∈ S then 1 else 0

/-- `x ↦ cos(2π(x_1+⋯+x_d))` on `𝕋^d`, as the real part of the character `e^{2πi(x_1+⋯+x_d)}`. -/
def sumCos (d : ℕ) (x : Torus d) : ℝ := (UnitAddTorus.mFourier (onesFreq d) x).re

/-- The source density `ρ_ε = 1 + ε cos(2π(x_1+⋯+x_d))` (as a bare function). -/
def remarkValue (d : ℕ) (ε : ℝ) (x : Torus d) : ℝ := 1 + ε * sumCos d x

/-- `sumCos` is literally `cos(2π(t_1+⋯+t_d))` for any real lift `t` of `x`. -/
theorem sumCos_coe (d : ℕ) (t : Fin d → ℝ) :
    sumCos d (fun j => (t j : UnitAddCircle)) = Real.cos (2 * Real.pi * ∑ j, t j) := by
  have h : UnitAddTorus.mFourier (onesFreq d) (fun j => (t j : UnitAddCircle)) =
      Complex.exp (((2 * Real.pi * ∑ j, t j : ℝ) : ℂ) * Complex.I) := by
    simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, onesFreq, fourier_coe_apply,
      Int.cast_one]
    rw [← Complex.exp_sum]
    congr 1
    push_cast
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  rw [sumCos, h, Complex.exp_ofReal_mul_I_re]

theorem abs_sumCos_le (d : ℕ) (x : Torus d) : |sumCos d x| ≤ 1 := by
  have h := Complex.abs_re_le_norm (UnitAddTorus.mFourier (onesFreq d) x)
  rw [norm_mFourier_apply] at h
  exact h

theorem continuous_sumCos (d : ℕ) : Continuous (sumCos d) :=
  Complex.continuous_re.comp (continuous_mFourier' _)

theorem continuous_remarkValue (d : ℕ) (ε : ℝ) : Continuous (remarkValue d ε) :=
  continuous_const.add (continuous_const.mul (continuous_sumCos d))

/-- The real part of the all-ones character, in terms of the characters `e_{±(1,…,1)}`. -/
theorem sumCos_eq_complex (d : ℕ) (x : Torus d) :
    (sumCos d x : ℂ) = (UnitAddTorus.mFourier (onesFreq d) x +
      UnitAddTorus.mFourier (-onesFreq d) x) / 2 := by
  rw [UnitAddTorus.mFourier_neg, sumCos, Complex.re_eq_add_conj]

theorem remarkValue_eq_complex (d : ℕ) (ε : ℝ) (x : Torus d) :
    (remarkValue d ε x : ℂ) = 1 + (ε / 2 : ℝ) * (UnitAddTorus.mFourier (onesFreq d) x +
      UnitAddTorus.mFourier (-onesFreq d) x) := by
  rw [remarkValue]
  push_cast
  rw [sumCos_eq_complex]
  ring

/-- Exact Fourier coefficients of `ρ_ε`. -/
theorem fourierCoeff_remarkValue {d : ℕ} (ε : ℝ) (k : Frequency d) :
    HighDim.fourierCoeff (remarkValue d ε) k =
      (if k = 0 then 1 else 0) +
        (ε / 2 : ℝ) * ((if k = onesFreq d then 1 else 0) + (if k = -onesFreq d then 1 else 0)) := by
  have hpt : ∀ x : Torus d, UnitAddTorus.mFourier (-k) x * (remarkValue d ε x : ℂ) =
      UnitAddTorus.mFourier (-k) x + (ε / 2 : ℝ) * UnitAddTorus.mFourier (onesFreq d + -k) x +
        (ε / 2 : ℝ) * UnitAddTorus.mFourier (-onesFreq d + -k) x := by
    intro x
    rw [remarkValue_eq_complex, UnitAddTorus.mFourier_add, UnitAddTorus.mFourier_add]
    ring
  unfold HighDim.fourierCoeff
  simp_rw [hpt]
  have h1 : Integrable (fun x : Torus d => UnitAddTorus.mFourier (-k) x) (torusMeasure d) :=
    integrable_of_continuous_torus (continuous_mFourier' _)
  have h2 : ∀ n : Frequency d, Integrable (fun x : Torus d =>
      ((ε / 2 : ℝ) : ℂ) * UnitAddTorus.mFourier n x) (torusMeasure d) := fun n =>
    (integrable_of_continuous_torus (continuous_mFourier' n)).const_mul _
  have i12 : Integrable (fun x : Torus d => UnitAddTorus.mFourier (-k) x +
      ((ε / 2 : ℝ) : ℂ) * UnitAddTorus.mFourier (onesFreq d + -k) x) (torusMeasure d) :=
    h1.add (h2 _)
  rw [integral_add i12 (h2 _), integral_add h1 (h2 _), integral_const_mul,
    integral_const_mul, integral_mFourier, integral_mFourier, integral_mFourier]
  have e1 : (-k = 0) ↔ (k = 0) := neg_eq_zero
  have e2 : (onesFreq d + -k = 0) ↔ (k = onesFreq d) := by
    rw [← sub_eq_add_neg, sub_eq_zero]; exact eq_comm
  have e3 : (-onesFreq d + -k = 0) ↔ (k = -onesFreq d) := by
    rw [add_eq_zero_iff_eq_neg, neg_neg]; exact eq_comm
  simp only [e1, e2, e3]
  ring

/-- `1_S + 1_{Sᶜ} = (1,…,1)`. -/
theorem indFreq_add_compl {d : ℕ} (S : Finset (Fin d)) : indFreq S + indFreq Sᶜ = onesFreq d := by
  funext i
  by_cases h : i ∈ S <;> simp [indFreq, onesFreq, h]

theorem indFreq_ne_zero {d : ℕ} {S : Finset (Fin d)} (h : S.Nonempty) : indFreq S ≠ 0 := by
  obtain ⟨i, hi⟩ := h
  intro h0
  have := congrFun h0 i
  simp [indFreq, hi] at this

/-- Every coordinate marginal over a strict subset of the coordinates of `ρ_ε` is identically one. -/
theorem coordinateMarginal_remark_eq_one {d : ℕ} (ε : ℝ) (ρ : ProbabilityDensity d)
    (hρ : ρ.value = remarkValue d ε) {I : Finset (Fin d)} (hI : I ≠ Finset.univ) (x : Torus d) :
    coordinateMarginal ρ I x = 1 := by
  have hne : Iᶜ.Nonempty := by
    by_contra hc
    rw [Finset.not_nonempty_iff_eq_empty, Finset.compl_eq_empty_iff] at hc
    exact hI hc
  let mix : Torus d → Torus d := fun y => fun i => if i ∈ I then x i else y i
  have hmixc : Continuous mix := by
    refine continuous_pi (fun i => ?_)
    by_cases hi : i ∈ I
    · simp only [mix, hi, ite_true]; exact continuous_const
    · simp only [mix, hi, ite_false]; exact continuous_apply i
  have hfac : ∀ y : Torus d,
      UnitAddTorus.mFourier (indFreq I + indFreq Iᶜ) (mix y) =
      UnitAddTorus.mFourier (indFreq I) x * UnitAddTorus.mFourier (indFreq Iᶜ) y := by
    intro y
    rw [UnitAddTorus.mFourier_add]
    congr 1
    · apply mFourier_congr_support
      intro i hi
      have : i ∈ I := by
        by_contra hni; exact hi (by simp [indFreq, hni])
      simp [mix, this]
    · apply mFourier_congr_support
      intro i hi
      have : i ∉ I := by
        intro hiI; exact hi (by simp [indFreq, hiI])
      simp [mix, this]
  -- the integral of the all-ones character composed with the mixing map vanishes
  have hint1 : ∫ y, UnitAddTorus.mFourier (onesFreq d) (mix y) ∂torusMeasure d = 0 := by
    have : ∀ y, UnitAddTorus.mFourier (onesFreq d) (mix y) =
        UnitAddTorus.mFourier (indFreq I) x * UnitAddTorus.mFourier (indFreq Iᶜ) y := by
      intro y; rw [← indFreq_add_compl I]; exact hfac y
    simp_rw [this]
    rw [integral_const_mul, integral_mFourier]
    simp [indFreq_ne_zero hne]
  have hint2 : ∫ y, UnitAddTorus.mFourier (-onesFreq d) (mix y) ∂torusMeasure d = 0 := by
    have : ∀ y, UnitAddTorus.mFourier (-onesFreq d) (mix y) =
        UnitAddTorus.mFourier (-indFreq I) x * UnitAddTorus.mFourier (-indFreq Iᶜ) y := by
      intro y
      rw [UnitAddTorus.mFourier_neg, UnitAddTorus.mFourier_neg, UnitAddTorus.mFourier_neg,
        ← indFreq_add_compl I, hfac y]
      simp [map_mul]
    simp_rw [this]
    rw [integral_const_mul, integral_mFourier]
    have : (-indFreq Iᶜ : Frequency d) ≠ 0 := by
      intro h; exact indFreq_ne_zero hne (neg_eq_zero.mp h)
    simp [this]
  have hcomp : ∀ n : Frequency d, Integrable (fun y : Torus d => UnitAddTorus.mFourier n (mix y))
      (torusMeasure d) := fun n =>
    integrable_of_continuous_torus ((continuous_mFourier' n).comp hmixc)
  have hre : ∫ y, sumCos d (mix y) ∂torusMeasure d = 0 := by
    have hc : (∫ y, (sumCos d (mix y) : ℂ) ∂torusMeasure d) = 0 := by
      simp_rw [sumCos_eq_complex]
      rw [integral_div, integral_add (hcomp _) (hcomp _), hint1, hint2]
      simp
    have h2 : ((∫ y, sumCos d (mix y) ∂torusMeasure d : ℝ) : ℂ) = 0 := by
      rw [← hc]; exact (integral_complex_ofReal).symm
    exact_mod_cast h2
  unfold coordinateMarginal
  change ∫ y, ρ.value (mix y) ∂torusMeasure d = 1
  simp_rw [hρ, remarkValue]
  have hsi : Integrable (fun y : Torus d => sumCos d (mix y)) (torusMeasure d) :=
    integrable_of_continuous_torus ((continuous_sumCos d).comp hmixc)
  rw [integral_add (integrable_const _) (hsi.const_mul ε), integral_const_mul, hre]
  simp

end BecknerOnofri.V2.Transfer
