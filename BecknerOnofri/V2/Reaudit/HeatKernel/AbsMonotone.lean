module

public import Mathlib.Analysis.Calculus.AbsolutelyMonotone
public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.Calculus.TangentCone.Real
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

@[expose] public section

/-! # S014, one variable: an absolutely monotone function equals its Taylor series

This file proves the one-variable theorem that the printed proof of
`lem:positive-bernstein` cites as \cite[Chapter IV, Theorem 3a]{Widder1941}: a function that is
absolutely monotone on `[0,R)` (Mathlib's `AbsolutelyMonotoneOn g (Set.Ico 0 R)`: `C^∞` with all
iterated derivatives within `[0,R)` nonnegative) agrees on `[0,R)` with its Taylor series at `0`.

The proof is the classical one (Taylor's formula with integral remainder on `[0,x]` and `[0,r]`,
`x < r < R`, and the scaling comparison `Rem_n(x) ≤ (x/r)^(n+1) Rem_n(r) ≤ (x/r)^(n+1) g(r)`).
Mathlib has the definition `AbsolutelyMonotoneOn` but not this representation theorem.
-/

noncomputable section
open Set Filter intervalIntegral Topology Finset
open scoped ContDiff Nat

namespace BecknerOnofri.V2.Reaudit.HeatKernel

variable {g : ℝ → ℝ} {R : ℝ}

/-- Smoothness and nonnegativity of derivatives, unpacked from `AbsolutelyMonotoneOn`. -/
theorem absMonotone_unpack (hg : AbsolutelyMonotoneOn g (Ico 0 R)) :
    ContDiffOn ℝ ∞ g (Ico 0 R) ∧ ∀ n : ℕ, ∀ t ∈ Ico (0 : ℝ) R,
      0 ≤ iteratedDerivWithin n g (Ico 0 R) t :=
  (AbsolutelyMonotoneOn.iff_iteratedDerivWithin_nonneg (uniqueDiffOn_Ico 0 R)).mp hg

/-- Iterated derivatives within the smaller interval `[0,x]` agree with those within `[0,R)`. -/
theorem iteratedDerivWithin_Icc_eq (hcd : ContDiffOn ℝ ∞ g (Ico 0 R)) {x : ℝ} (hx : 0 < x)
    (hxR : x < R) (k : ℕ) {t : ℝ} (ht : t ∈ Icc 0 x) :
    iteratedDerivWithin k g (Icc 0 x) t = iteratedDerivWithin k g (Ico 0 R) t := by
  rw [iteratedDerivWithin_eq_iteratedFDerivWithin, iteratedDerivWithin_eq_iteratedFDerivWithin]
  congr 1
  exact iteratedFDerivWithin_subset (fun u hu => ⟨hu.1, lt_of_le_of_lt hu.2 hxR⟩)
    (uniqueDiffOn_Icc hx) (uniqueDiffOn_Ico 0 R) (hcd.of_le (by exact_mod_cast le_top)) ht

/-- Each iterated derivative of an absolutely monotone function is nondecreasing on `[0,R)`. -/
theorem iteratedDerivWithin_monotoneOn (hg : AbsolutelyMonotoneOn g (Ico 0 R)) (m : ℕ) :
    MonotoneOn (iteratedDerivWithin m g (Ico 0 R)) (Ico 0 R) := by
  obtain ⟨hcd, hnn⟩ := absMonotone_unpack hg
  have hU := uniqueDiffOn_Ico (0 : ℝ) R
  apply monotoneOn_of_deriv_nonneg (convex_Ico 0 R)
  · exact hcd.continuousOn_iteratedDerivWithin (by exact_mod_cast le_top) hU
  · exact (hcd.differentiableOn_iteratedDerivWithin (by exact_mod_cast WithTop.coe_lt_top m) hU).mono
      interior_subset
  · intro t ht
    rw [interior_Ico] at ht
    have hmem : Ico (0 : ℝ) R ∈ 𝓝 t := Ico_mem_nhds ht.1 ht.2
    rw [← derivWithin_of_mem_nhds hmem, ← iteratedDerivWithin_succ]
    exact hnn (m + 1) t ⟨ht.1.le, ht.2⟩

/-- Taylor's formula with integral remainder on `[0,x]`, expressed through derivatives within
`[0,R)`. -/
theorem taylor_remainder_formula (hcd : ContDiffOn ℝ ∞ g (Ico 0 R)) {x : ℝ} (hx : 0 < x)
    (hxR : x < R) (n : ℕ) :
    g x - ∑ k ∈ range (n + 1), (iteratedDerivWithin k g (Ico 0 R) 0 / (k ! : ℝ)) * x ^ k =
      ∫ t in (0 : ℝ)..x, ((x - t) ^ n / (n ! : ℝ)) * iteratedDerivWithin (n + 1) g (Ico 0 R) t := by
  have hsub : Icc (0 : ℝ) x ⊆ Ico 0 R := fun u hu => ⟨hu.1, lt_of_le_of_lt hu.2 hxR⟩
  have hf : ContDiffOn ℝ (n + 1 : ℕ) g (uIcc 0 x) := by
    rw [uIcc_of_le hx.le]
    exact (hcd.mono hsub).of_le (by exact_mod_cast le_top)
  have h := taylor_integral_remainder (x := x) (x₀ := 0) (n := n) hf
  rw [taylor_within_apply, uIcc_of_le hx.le] at h
  have h0 : (0 : ℝ) ∈ Icc 0 x := ⟨le_rfl, hx.le⟩
  have e1 : ∀ k ∈ range (n + 1),
      ((k ! : ℝ)⁻¹ * (x - 0) ^ k) • iteratedDerivWithin k g (Icc 0 x) 0 =
        (iteratedDerivWithin k g (Ico 0 R) 0 / (k ! : ℝ)) * x ^ k := by
    intro k _
    rw [iteratedDerivWithin_Icc_eq hcd hx hxR k h0, smul_eq_mul, sub_zero]
    ring
  rw [Finset.sum_congr rfl e1] at h
  rw [h]
  refine intervalIntegral.integral_congr (fun t ht => ?_)
  rw [uIcc_of_le hx.le] at ht
  simp only [smul_eq_mul]
  rw [iteratedDerivWithin_Icc_eq hcd hx hxR (n + 1) ht]

/-- The scaling comparison `Rem_n(x) ≤ (x/r)^(n+1) Rem_n(r)`. -/
theorem remainder_scaling (hg : AbsolutelyMonotoneOn g (Ico 0 R)) {x r : ℝ} (hx : 0 < x)
    (hxr : x < r) (hrR : r < R) (n : ℕ) :
    (∫ t in (0 : ℝ)..x, ((x - t) ^ n / (n ! : ℝ)) * iteratedDerivWithin (n + 1) g (Ico 0 R) t) ≤
      (x / r) ^ (n + 1) *
        ∫ σ in (0 : ℝ)..r, ((r - σ) ^ n / (n ! : ℝ)) * iteratedDerivWithin (n + 1) g (Ico 0 R) σ := by
  obtain ⟨hcd, hnn⟩ := absMonotone_unpack hg
  have hr : 0 < r := hx.trans hxr
  set h := iteratedDerivWithin (n + 1) g (Ico 0 R) with hh
  set l : ℝ := x / r with hl
  have hl0 : 0 < l := div_pos hx hr
  have hl1 : l ≤ 1 := (div_le_one hr).mpr hxr.le
  have hlr : l * r = x := by rw [hl]; field_simp
  have hcont : ContinuousOn h (Ico 0 R) :=
    hcd.continuousOn_iteratedDerivWithin (by exact_mod_cast le_top) (uniqueDiffOn_Ico 0 R)
  have hmono : MonotoneOn h (Ico 0 R) := iteratedDerivWithin_monotoneOn hg (n + 1)
  have hsubr : Icc (0 : ℝ) r ⊆ Ico 0 R := fun u hu => ⟨hu.1, lt_of_le_of_lt hu.2 hrR⟩
  -- change of variables
  set F : ℝ → ℝ := fun t => ((x - t) ^ n / (n ! : ℝ)) * h t with hF
  have hsub1 : (∫ σ in (0 : ℝ)..r, F (l * σ)) = l⁻¹ • ∫ t in (0 : ℝ)..x, F t := by
    rw [intervalIntegral.integral_comp_mul_left (fun t => F t) hl0.ne', mul_zero, hlr]
  have hsub2 : (∫ t in (0 : ℝ)..x, F t) = l * ∫ σ in (0 : ℝ)..r, F (l * σ) := by
    rw [hsub1, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hl0.ne', one_mul]
  change (∫ t in (0 : ℝ)..x, F t) ≤ _
  rw [hsub2]
  have hint : (∫ σ in (0 : ℝ)..r, F (l * σ)) ≤
      l ^ n * ∫ σ in (0 : ℝ)..r, ((r - σ) ^ n / (n ! : ℝ)) * h σ := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hr.le
    · apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hr.le]
      have hc : ContinuousOn (fun σ => h (l * σ)) (Icc 0 r) := by
        refine hcont.comp (by fun_prop) (fun σ hσ => ?_)
        exact hsubr ⟨by nlinarith [hσ.1], by nlinarith [hσ.2]⟩
      simp only [hF]
      exact ((by fun_prop : Continuous fun σ : ℝ => (x - l * σ) ^ n / (n ! : ℝ)).continuousOn).mul hc
    · apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hr.le]
      have hc : ContinuousOn h (Icc 0 r) := hcont.mono hsubr
      exact continuousOn_const.mul
        (((by fun_prop : Continuous fun σ : ℝ => (r - σ) ^ n / (n ! : ℝ)).continuousOn).mul hc)
    · intro σ hσ
      have hσ0 : 0 ≤ σ := hσ.1
      have h1 : h (l * σ) ≤ h σ := hmono ⟨by positivity, by nlinarith [hσ.2]⟩ (hsubr hσ)
        (by nlinarith)
      have h2 : x - l * σ = l * (r - σ) := by rw [← hlr]; ring
      have h3 : 0 ≤ ((r - σ) ^ n / (n ! : ℝ)) := by
        apply div_nonneg (pow_nonneg (by linarith [hσ.2]) _) (by positivity)
      simp only [hF]
      rw [h2, mul_pow, show l ^ n * (r - σ) ^ n / (n ! : ℝ) = l ^ n * ((r - σ) ^ n / (n ! : ℝ)) by ring]
      have hpow : 0 ≤ l ^ n := by positivity
      calc l ^ n * ((r - σ) ^ n / (n ! : ℝ)) * h (l * σ)
          ≤ l ^ n * ((r - σ) ^ n / (n ! : ℝ)) * h σ := by
            apply mul_le_mul_of_nonneg_left h1 (mul_nonneg hpow h3)
        _ = l ^ n * (((r - σ) ^ n / (n ! : ℝ)) * h σ) := by ring
  calc l * ∫ σ in (0 : ℝ)..r, F (l * σ)
      ≤ l * (l ^ n * ∫ σ in (0 : ℝ)..r, ((r - σ) ^ n / (n ! : ℝ)) * h σ) :=
        mul_le_mul_of_nonneg_left hint hl0.le
    _ = l ^ (n + 1) * ∫ σ in (0 : ℝ)..r, ((r - σ) ^ n / (n ! : ℝ)) * h σ := by ring

/-- **One-variable absolute-monotonicity theorem** (the special case of Widder, Chapter IV, used
in the proof of `lem:positive-bernstein`): an absolutely monotone function on `[0,R)` equals its
Taylor series at `0` on `[0,R)`.  Here the derivatives are the iterated derivatives within
`[0,R)`. -/
theorem absMonotone_hasSum_taylor (hg : AbsolutelyMonotoneOn g (Ico 0 R)) {x : ℝ}
    (hx : x ∈ Ico (0 : ℝ) R) :
    HasSum (fun n : ℕ => (iteratedDerivWithin n g (Ico 0 R) 0 / (n ! : ℝ)) * x ^ n) (g x) := by
  obtain ⟨hcd, hnn⟩ := absMonotone_unpack hg
  have h0R : (0 : ℝ) ∈ Ico (0 : ℝ) R := ⟨le_rfl, hx.1.trans_lt hx.2⟩
  set a : ℕ → ℝ := fun n => iteratedDerivWithin n g (Ico 0 R) 0 / (n ! : ℝ) with ha
  have ha0 : ∀ n, 0 ≤ a n := fun n => div_nonneg (hnn n 0 h0R) (by positivity)
  rcases hx.1.eq_or_lt with h0 | hpos
  · -- x = 0
    subst h0
    have : (fun n : ℕ => a n * (0 : ℝ) ^ n) = fun n => if n = 0 then g 0 else 0 := by
      funext n
      rcases n with _ | n
      · simp [ha]
      · simp
    rw [this]
    simpa using hasSum_ite_eq 0 (g 0)
  · have hxR := hx.2
    set r : ℝ := (x + R) / 2 with hr
    have hxr : x < r := by rw [hr]; linarith
    have hrR : r < R := by rw [hr]; linarith
    have hr0 : 0 < r := hpos.trans hxr
    have hrmem : r ∈ Ico (0 : ℝ) R := ⟨hr0.le, hrR⟩
    have hterm : ∀ n, 0 ≤ a n * x ^ n := fun n => mul_nonneg (ha0 n) (pow_nonneg hpos.le n)
    rw [hasSum_iff_tendsto_nat_of_nonneg hterm]
    -- Bounds for the remainders
    have hrem_nonneg : ∀ n : ℕ, 0 ≤ g x - ∑ k ∈ range (n + 1), a k * x ^ k := by
      intro n
      rw [taylor_remainder_formula hcd hpos hxR n]
      apply intervalIntegral.integral_nonneg hpos.le
      intro t ht
      exact mul_nonneg (div_nonneg (pow_nonneg (by linarith [ht.2]) _) (by positivity))
        (hnn (n + 1) t ⟨ht.1, lt_of_le_of_lt ht.2 hxR⟩)
    have hrem_le : ∀ n : ℕ, g x - ∑ k ∈ range (n + 1), a k * x ^ k ≤ (x / r) ^ (n + 1) * g r := by
      intro n
      have h1 := remainder_scaling hg hpos hxr hrR n
      rw [← taylor_remainder_formula hcd hpos hxR n,
        ← taylor_remainder_formula hcd hr0 hrR n] at h1
      have h2 : 0 ≤ ∑ k ∈ range (n + 1), a k * r ^ k :=
        Finset.sum_nonneg (fun k _ => mul_nonneg (ha0 k) (pow_nonneg hr0.le k))
      have h3 : 0 ≤ (x / r) ^ (n + 1) := by positivity
      calc g x - ∑ k ∈ range (n + 1), a k * x ^ k
          ≤ (x / r) ^ (n + 1) * (g r - ∑ k ∈ range (n + 1), a k * r ^ k) := h1
        _ ≤ (x / r) ^ (n + 1) * g r := by
            apply mul_le_mul_of_nonneg_left _ h3
            linarith
    have hlim : Tendsto (fun n : ℕ => (x / r) ^ (n + 1) * g r) atTop (𝓝 0) := by
      have hq : Tendsto (fun n : ℕ => (x / r) ^ n) atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hpos.le hr0.le)
          ((div_lt_one hr0).mpr hxr)
      have := (hq.comp (tendsto_add_atTop_nat 1)).mul_const (g r)
      simpa [Function.comp] using this
    have hsq : Tendsto (fun n : ℕ => g x - ∑ k ∈ range (n + 1), a k * x ^ k) atTop (𝓝 0) :=
      squeeze_zero hrem_nonneg hrem_le hlim
    have hconv : Tendsto (fun n : ℕ => ∑ k ∈ range (n + 1), a k * x ^ k) atTop (𝓝 (g x)) := by
      have := (tendsto_const_nhds (x := g x)).sub hsq
      simpa using this
    exact (tendsto_add_atTop_iff_nat (f := fun n => ∑ k ∈ range n, a k * x ^ k) 1).mp hconv

#print axioms absMonotone_hasSum_taylor

end BecknerOnofri.V2.Reaudit.HeatKernel
