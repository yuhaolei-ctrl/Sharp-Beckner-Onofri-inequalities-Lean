module

public import BecknerOnofri.V2.Transfer.Remark56Basic

@[expose] public section

/-! # Remark 5.6: the restriction on the density is essential

Source: `rem:spectral-energy-restriction` (S038).  For `d ≥ 1` and `0 < |ε| < 1` the smooth strictly
positive probability density `ρ_ε(x) = 1 + ε cos(2π(x_1+⋯+x_d))` has

* every coordinate marginal over a strict subset of the coordinates identically `1`
  (`remark56_marginal_eq_one`);
* full interaction (the Fourier energy `(2π)^d ‖ρ_ε‖²_{Ḣ^{-d/2}} = Σ_{k≠0} |k|^{-d} |ρ̂_ε(k)|²`)
  exactly `ε² d^{-d/2} / 2 > 0` (`remark56_spectralEnergy`).

Hence the claimed unrestricted deletion inequality (the right side of which is `0`, since every
`(d-1)`-coordinate marginal is the constant `1`) and its all-subsets version fail for every `d ≥ 2`
(in particular for every `d ≥ 12`): `not_unrestrictedDeletionEnergy`,
`not_unrestrictedSubsetEnergy`.  The proofs are direct computations; no negated proposition is
assumed. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace BecknerOnofri.V2.Transfer
open BecknerOnofri.HighDim

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

theorem remarkValue_pos {ε : ℝ} (hε : |ε| < 1) (d : ℕ) (x : Torus d) : 0 < remarkValue d ε x := by
  have h1 := abs_sumCos_le d x
  have h2 : |ε * sumCos d x| < 1 := by
    rw [abs_mul]
    calc |ε| * |sumCos d x| ≤ |ε| * 1 := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ < 1 := by rwa [mul_one]
  have := (abs_lt.mp h2).1
  unfold remarkValue
  linarith

theorem integral_sumCos {d : ℕ} (hd : 0 < d) : ∫ x, sumCos d x ∂torusMeasure d = 0 := by
  have hne : onesFreq d ≠ 0 := by
    intro h
    have := congrFun h ⟨0, hd⟩
    simp [onesFreq] at this
  have hne' : -onesFreq d ≠ 0 := fun h => hne (neg_eq_zero.mp h)
  have hc : (∫ x, (sumCos d x : ℂ) ∂torusMeasure d) = 0 := by
    simp_rw [sumCos_eq_complex]
    rw [integral_div, integral_add (integrable_of_continuous_torus (continuous_mFourier' _))
      (integrable_of_continuous_torus (continuous_mFourier' _)), integral_mFourier,
      integral_mFourier]
    simp [hne, hne']
  have h2 : ((∫ x, sumCos d x ∂torusMeasure d : ℝ) : ℂ) = 0 := by
    rw [← hc]; exact (integral_complex_ofReal).symm
  exact_mod_cast h2

/-- The density `ρ_ε` of Remark 5.6 as a `ProbabilityDensity`, for `d ≥ 1` and `|ε| < 1`. -/
def remarkDensity (d : ℕ) (hd : 0 < d) (ε : ℝ) (hε : |ε| < 1) : ProbabilityDensity d where
  value := remarkValue d ε
  nonneg := ae_of_all _ (fun x => (remarkValue_pos hε d x).le)
  integrable := integrable_of_continuous_torus (continuous_remarkValue d ε)
  mass := by
    unfold remarkValue
    rw [integral_add (integrable_const _)
      ((integrable_of_continuous_torus (continuous_sumCos d)).const_mul ε), integral_const_mul,
      integral_sumCos hd]
    simp

@[simp] theorem remarkDensity_value (d : ℕ) (hd : 0 < d) (ε : ℝ) (hε : |ε| < 1) :
    (remarkDensity d hd ε hε).value = remarkValue d ε := rfl

/-- Smoothness of `ρ_ε`, as a `ℤ^d`-periodic function on `ℝ^d`. -/
theorem remarkValue_smooth (d : ℕ) (ε : ℝ) : SmoothOnTorus (remarkValue d ε) := by
  unfold SmoothOnTorus
  have : (fun x : Fin d → ℝ => remarkValue d ε (fun j => (x j : UnitAddCircle))) =
      fun x => 1 + ε * Real.cos (2 * Real.pi * ∑ j, x j) := by
    funext x
    rw [remarkValue, sumCos_coe]
  rw [this]
  refine contDiff_const.add (contDiff_const.mul (Real.contDiff_cos.comp ?_))
  exact contDiff_const.mul (ContDiff.sum fun j _ => contDiff_apply ℝ ℝ j)

theorem remarkDensity_finiteEntropy (d : ℕ) (hd : 0 < d) (ε : ℝ) (hε : |ε| < 1) :
    (remarkDensity d hd ε hε).FiniteEntropy := by
  unfold ProbabilityDensity.FiniteEntropy
  apply integrable_of_continuous_torus
  exact (continuous_remarkValue d ε).mul
    (Continuous.log (continuous_remarkValue d ε) (fun x => (remarkValue_pos hε d x).ne'))

/-- Every coordinate marginal over a strict subset of the coordinates of `ρ_ε` is the constant `1`. -/
theorem remark56_marginal_eq_one (d : ℕ) (hd : 0 < d) (ε : ℝ) (hε : |ε| < 1)
    {I : Finset (Fin d)} (hI : I ≠ Finset.univ) :
    coordinateMarginal (remarkDensity d hd ε hε) I = fun _ => 1 :=
  funext (coordinateMarginal_remark_eq_one ε _ rfl hI)

lemma frequencyLength_ones (d : ℕ) : frequencyLength (onesFreq d) = Real.sqrt d := by
  simp [frequencyLength, onesFreq]

lemma frequencyLength_neg_ones (d : ℕ) : frequencyLength (-onesFreq d) = Real.sqrt d := by
  simp [frequencyLength, onesFreq]

lemma ones_ne_neg_ones {d : ℕ} (hd : 0 < d) : onesFreq d ≠ -onesFreq d := by
  intro h
  have := congrFun h ⟨0, hd⟩
  simp [onesFreq] at this

lemma inv_sqrt_pow (d : ℕ) : ((Real.sqrt d) ^ d)⁻¹ = (d : ℝ) ^ (-((d : ℝ) / 2)) := by
  rw [Real.rpow_neg (Nat.cast_nonneg d), Real.sqrt_eq_rpow, ← Real.rpow_natCast,
    ← Real.rpow_mul (Nat.cast_nonneg d)]
  congr 2
  ring

/-- The full interaction of `ρ_ε`: `(2π)^d ‖ρ_ε‖²_{Ḣ^{-d/2}} = ε² d^{-d/2} / 2`. -/
theorem remark56_spectralEnergy (d : ℕ) (hd : 0 < d) (ε : ℝ) (hε : |ε| < 1) :
    spectralEnergy (remarkDensity d hd ε hε) =
      ENNReal.ofReal (ε ^ 2 / 2 * (d : ℝ) ^ (-((d : ℝ) / 2))) := by
  have hcoef : ∀ k : Frequency d, fourierCoeff (remarkDensity d hd ε hε).value k =
      (if k = 0 then 1 else 0) +
        (ε / 2 : ℝ) * ((if k = onesFreq d then 1 else 0) + (if k = -onesFreq d then 1 else 0)) :=
    fun k => fourierCoeff_remarkValue ε k
  let f : Frequency d → ℝ≥0∞ := fun k => ENNReal.ofReal
    ((frequencyLength k ^ d)⁻¹ * ‖fourierCoeff (remarkDensity d hd ε hε).value k‖ ^ 2)
  have hf0 : f 0 = 0 := by
    have : frequencyLength (0 : Frequency d) = 0 := by simp [frequencyLength]
    simp [f, this, zero_pow hd.ne']
  have hs : Function.support f ⊆ {k : Frequency d | k ≠ 0} := by
    intro k hk hz
    exact hk (by rw [hz]; exact hf0)
  have h1 : spectralEnergy (remarkDensity d hd ε hε) = ∑' k : Frequency d, f k := by
    unfold spectralEnergy
    change (∑' k : NonzeroFrequency d, f k.1) = _
    exact tsum_subtype_eq_of_support_subset hs
  have hne : onesFreq d ≠ 0 := by
    intro h
    have := congrFun h ⟨0, hd⟩
    simp [onesFreq] at this
  have hne' : -onesFreq d ≠ 0 := fun h => hne (neg_eq_zero.mp h)
  have hzero : ∀ k ∉ ({onesFreq d, -onesFreq d} : Finset (Frequency d)), f k = 0 := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    by_cases h0 : k = 0
    · rw [h0]; exact hf0
    · have : HighDim.fourierCoeff (remarkValue d ε) k = 0 := by
        rw [fourierCoeff_remarkValue]; simp [h0, hk.1, hk.2]
      simp [f, this]
  have hc1 : fourierCoeff (remarkDensity d hd ε hε).value (onesFreq d) = ((ε / 2 : ℝ) : ℂ) := by
    rw [hcoef]
    simp [hne, ones_ne_neg_ones hd]
  have hc2 : fourierCoeff (remarkDensity d hd ε hε).value (-onesFreq d) = ((ε / 2 : ℝ) : ℂ) := by
    rw [hcoef]
    simp [hne', (ones_ne_neg_ones hd).symm]
  rw [h1, tsum_eq_sum hzero, Finset.sum_pair (ones_ne_neg_ones hd)]
  simp only [f, hc1, hc2, frequencyLength_ones, frequencyLength_neg_ones, inv_sqrt_pow]
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  ring

theorem remark56_spectralEnergy_pos (d : ℕ) (hd : 0 < d) {ε : ℝ} (hε0 : ε ≠ 0) (hε : |ε| < 1) :
    0 < spectralEnergy (remarkDensity d hd ε hε) := by
  rw [remark56_spectralEnergy]
  have : 0 < ε ^ 2 / 2 * (d : ℝ) ^ (-((d : ℝ) / 2)) := by
    have hd' : (0 : ℝ) < d := by exact_mod_cast hd
    positivity
  exact ENNReal.ofReal_pos.mpr this

/-- **Remark 5.6** (explicit counterexample), packaged: for every `d ≥ 1` and `0 < |ε| < 1` the
density `ρ_ε = 1 + ε cos(2π(x_1+⋯+x_d))` is a smooth strictly positive probability density of finite
entropy, with every strict-subset marginal equal to `1` and strictly positive full interaction
`ε² d^{-d/2} / 2`. -/
theorem remark56 (d : ℕ) (hd : 0 < d) (ε : ℝ) (hε0 : ε ≠ 0) (hε : |ε| < 1) :
    ∃ ρ : ProbabilityDensity d,
      (∀ t : Fin d → ℝ, ρ.value (fun j => (t j : UnitAddCircle)) =
        1 + ε * Real.cos (2 * Real.pi * ∑ j, t j)) ∧
      SmoothOnTorus ρ.value ∧ (∀ x, 0 < ρ.value x) ∧ ρ.FiniteEntropy ∧
      (∀ I : Finset (Fin d), I ≠ Finset.univ → coordinateMarginal ρ I = fun _ => 1) ∧
      spectralEnergy ρ = ENNReal.ofReal (ε ^ 2 / 2 * (d : ℝ) ^ (-((d : ℝ) / 2))) ∧
      0 < spectralEnergy ρ := by
  refine ⟨remarkDensity d hd ε hε, ?_, remarkValue_smooth d ε, remarkValue_pos hε d,
    remarkDensity_finiteEntropy d hd ε hε, fun I hI => remark56_marginal_eq_one d hd ε hε hI,
    remark56_spectralEnergy d hd ε hε, remark56_spectralEnergy_pos d hd hε0 hε⟩
  intro t
  change remarkValue d ε _ = _
  rw [remarkValue, sumCos_coe]

/-- The claimed unrestricted deletion inequality (the energy comparison of Proposition 5.5 with the
cosine-power-mixture hypothesis replaced by smoothness and strict positivity). -/
def UnrestrictedDeletionEnergy (d : ℕ) : Prop :=
  ∀ ρ : ProbabilityDensity d, SmoothOnTorus ρ.value → (∀ x, 0 < ρ.value x) →
    spectralEnergy ρ ≤ ENNReal.ofReal (1 / ((d : ℝ) - 1)) *
      ∑ i : Fin d, inversePowerEnergy (d - 1) (coordinateMarginal ρ (Finset.univ.erase i))

/-- The claimed unrestricted all-subsets energy comparison. -/
def UnrestrictedSubsetEnergy (d r : ℕ) : Prop :=
  ∀ ρ : ProbabilityDensity d, SmoothOnTorus ρ.value → (∀ x, 0 < ρ.value x) →
    spectralEnergy ρ ≤ ENNReal.ofReal ((d : ℝ) / ((r : ℝ) * (d.choose r : ℝ))) *
      ∑ I ∈ (Finset.univ : Finset (Fin d)).powersetCard r,
        inversePowerEnergy r (coordinateMarginal ρ I)

lemma erase_ne_univ' {d : ℕ} (i : Fin d) : (Finset.univ.erase i : Finset (Fin d)) ≠ Finset.univ := by
  intro h
  have : i ∈ (Finset.univ.erase i : Finset (Fin d)) := by rw [h]; exact Finset.mem_univ i
  simp at this

lemma inversePowerEnergy_one {d : ℕ} (r : ℕ) : inversePowerEnergy r (fun _ : Torus d => (1 : ℝ)) = 0 := by
  unfold inversePowerEnergy
  refine ENNReal.tsum_eq_zero.mpr (fun k => ?_)
  simp [fourierCoeff_one_nonzero k.1 k.2]

/-- Remark 5.6: the unrestricted deletion inequality is false in every dimension `d ≥ 2`, in
particular for all `d ≥ 12`. -/
theorem not_unrestrictedDeletionEnergy {d : ℕ} (hd : 2 ≤ d) : ¬ UnrestrictedDeletionEnergy d := by
  intro h
  have hd0 : 0 < d := by omega
  have hε : |(1 / 2 : ℝ)| < 1 := by rw [abs_of_pos (by norm_num)]; norm_num
  have key := h (remarkDensity d hd0 (1 / 2) hε) (remarkValue_smooth d _) (remarkValue_pos hε d)
  have hrhs : ∑ i : Fin d, inversePowerEnergy (d - 1)
      (coordinateMarginal (remarkDensity d hd0 (1 / 2) hε) (Finset.univ.erase i)) = 0 := by
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [remark56_marginal_eq_one d hd0 _ hε (erase_ne_univ' i), inversePowerEnergy_one]
  rw [hrhs, mul_zero] at key
  exact absurd key (not_le.mpr (remark56_spectralEnergy_pos d hd0 (by norm_num) hε))

/-- Remark 5.6, all-subsets form: for every `d ≥ 2` and `1 ≤ r < d` (in particular `12 ≤ r < d`) the
unrestricted all-subsets energy comparison is false. -/
theorem not_unrestrictedSubsetEnergy {d r : ℕ} (hr : 1 ≤ r) (hrd : r < d) :
    ¬ UnrestrictedSubsetEnergy d r := by
  intro h
  have hd0 : 0 < d := by omega
  have hε : |(1 / 2 : ℝ)| < 1 := by rw [abs_of_pos (by norm_num)]; norm_num
  have key := h (remarkDensity d hd0 (1 / 2) hε) (remarkValue_smooth d _) (remarkValue_pos hε d)
  have hrhs : ∑ I ∈ (Finset.univ : Finset (Fin d)).powersetCard r, inversePowerEnergy r
      (coordinateMarginal (remarkDensity d hd0 (1 / 2) hε) I) = 0 := by
    refine Finset.sum_eq_zero (fun I hI => ?_)
    have hcard : I.card = r := (Finset.mem_powersetCard.mp hI).2
    have hI' : I ≠ Finset.univ := by
      intro h'; rw [h', Finset.card_univ, Fintype.card_fin] at hcard; omega
    rw [remark56_marginal_eq_one d hd0 _ hε hI', inversePowerEnergy_one]
  rw [hrhs, mul_zero] at key
  exact absurd key (not_le.mpr (remark56_spectralEnergy_pos d hd0 (by norm_num) hε))

end BecknerOnofri.V2.Transfer
