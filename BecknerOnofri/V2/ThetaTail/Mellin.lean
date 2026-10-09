module

public import BecknerOnofri.V2.ThetaTail.LatticeProd
public import Legacy.BecknerOnofri.GaussianMellinTerm
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

/-! # The Mellin identity of Appendix A.1 (`d12-tail-eq:Mellin`)

`m^{-6} e^{-ηm} = (1/120) ∫_η^∞ (s-η)^5 e^{-sm} ds` and, by Tonelli/Fubini after proving
absolute convergence,

  `G(η) = (1/120) ∫_η^∞ (s-η)^5 [θ(e^{-s})^{12} − (1+2e^{-s})^{12}] ds`.

No twelve-square identity is used here.  The generic one-term Mellin lemma comes from
`Legacy.BecknerOnofri.GaussianMellinTerm` (a Mathlib-only file). -/
noncomputable section
open Finset Filter Topology MeasureTheory Set
namespace BecknerOnofri.V2.ThetaTail

/-- `∫_η^∞ (s-η)^5 e^{-ms} ds = 120 e^{-ηm}/m^6` -/
theorem integral_pow_five_exp {m : ℝ} (hm : 0 < m) (η : ℝ) :
    ∫ s in Ioi η, (s - η) ^ 5 * Real.exp (-s * m) = 120 * Real.exp (-η * m) / m ^ 6 := by
  have h := Legacy.BecknerOnofri.GaussianMellinTerm.shifted_integral (s := 6) (by norm_num) hm η
  have hG : Real.Gamma 6 = 120 := by
    have h := Real.Gamma_nat_eq_factorial 5
    norm_num at h ⊢
  norm_num only [show (6 : ℝ) - 1 = 5 by norm_num, Real.rpow_ofNat, hG] at h
  rw [h]; ring

theorem integrableOn_pow_five_exp {m : ℝ} (hm : 0 < m) (η : ℝ) :
    IntegrableOn (fun s : ℝ => (s - η) ^ 5 * Real.exp (-s * m)) (Ioi η) := by
  have h := Legacy.BecknerOnofri.GaussianMellinTerm.shifted_integrable (s := 6) (by norm_num) hm η
  norm_num only [show (6 : ℝ) - 1 = 5 by norm_num, Real.rpow_ofNat] at h
  exact h

lemma mellinTerm_nonneg_aux {η s : ℝ} (hs : η ≤ s) (k : Fin 12 → ℤ) (c : ℝ) (hc : 0 ≤ c) :
    0 ≤ (s - η) ^ 5 * c := mul_nonneg (pow_nonneg (sub_nonneg.2 hs) 5) hc

/-- individual normalized Mellin terms -/
def mellinTerm (η : ℝ) (k : Fin 12 → ℤ) (s : ℝ) : ℝ :=
  (s - η) ^ 5 * (cube12ᶜ).indicator (fun k => Real.exp (-s * latticeNormSq k)) k / 120

lemma mellinTerm_eq_of_mem {η : ℝ} {k : Fin 12 → ℤ} (hk : k ∈ cube12ᶜ) (s : ℝ) :
    mellinTerm η k s = (s - η) ^ 5 * Real.exp (-s * latticeNormSq k) / 120 := by
  unfold mellinTerm; rw [Set.indicator_of_mem hk]

lemma mellinTerm_eq_zero {η : ℝ} {k : Fin 12 → ℤ} (hk : k ∉ cube12ᶜ) (s : ℝ) :
    mellinTerm η k s = 0 := by
  unfold mellinTerm; rw [Set.indicator_of_notMem hk]; simp

theorem mellinTerm_integrable (η : ℝ) (k : Fin 12 → ℤ) :
    Integrable (mellinTerm η k) (volume.restrict (Ioi η)) := by
  by_cases hk : k ∈ cube12ᶜ
  · have hpos : 0 < latticeNormSq k := by
      have := latticeNormSq_ge_four hk; linarith
    have h : Integrable (fun s : ℝ => (s - η) ^ 5 * Real.exp (-s * latticeNormSq k) / 120)
        (volume.restrict (Ioi η)) := (integrableOn_pow_five_exp hpos η).div_const 120
    refine h.congr ?_
    filter_upwards with s
    rw [mellinTerm_eq_of_mem hk]
  · have : mellinTerm η k = fun _ => 0 := funext (mellinTerm_eq_zero hk)
    rw [this]
    exact integrable_zero _ _ _

theorem mellinTerm_integral (η : ℝ) (k : Fin 12 → ℤ) :
    ∫ s in Ioi η, mellinTerm η k s = gaussSummand η k := by
  by_cases hk : k ∈ cube12ᶜ
  · have hpos : 0 < latticeNormSq k := by
      have := latticeNormSq_ge_four hk; linarith
    unfold gaussSummand
    rw [Set.indicator_of_mem hk]
    simp_rw [mellinTerm_eq_of_mem hk]
    rw [integral_div, integral_pow_five_exp hpos, latticeNorm_pow_twelve]
    field_simp
  · simp only [mellinTerm_eq_zero hk, integral_zero]
    unfold gaussSummand
    rw [Set.indicator_of_notMem hk]

lemma mellinTerm_nonneg {η s : ℝ} (hs : η ≤ s) (k : Fin 12 → ℤ) : 0 ≤ mellinTerm η k s := by
  unfold mellinTerm
  refine div_nonneg (mul_nonneg (pow_nonneg (sub_nonneg.2 hs) 5) ?_) (by norm_num)
  exact Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) k

theorem mellinTerm_sum {η s : ℝ} (hs : 0 < s) :
    ∑' k : Fin 12 → ℤ, mellinTerm η k s
      = (s - η) ^ 5 * (theta (Real.exp (-s)) ^ 12 - (1 + 2 * Real.exp (-s)) ^ 12) / 120 := by
  unfold mellinTerm
  simp only [div_eq_mul_inv, tsum_mul_right, tsum_mul_left]
  rw [(hasSum_heat_off_cube hs).tsum_eq]

/-- The Mellin identity `(d12-tail-eq:Mellin)`, with integrability of the integrand. -/
theorem G_eq_mellin {η : ℝ} (hη : 0 < η) :
    G η = (1 / 120) * ∫ s in Ioi η, (s - η) ^ 5 *
        (theta (Real.exp (-s)) ^ 12 - (1 + 2 * Real.exp (-s)) ^ 12) := by
  have hs : Summable (fun k : Fin 12 → ℤ => ∫ s in Ioi η, ‖mellinTerm η k s‖) := by
    have : ∀ k : Fin 12 → ℤ, ∫ s in Ioi η, ‖mellinTerm η k s‖ = gaussSummand η k := by
      intro k
      rw [← mellinTerm_integral η k]
      refine setIntegral_congr_fun measurableSet_Ioi (fun s hs' => ?_)
      exact Real.norm_of_nonneg (mellinTerm_nonneg (le_of_lt hs') k)
    simp_rw [this]
    exact summable_gaussSummand hη
  have h := integral_tsum_of_summable_integral_norm (μ := volume.restrict (Ioi η))
    (mellinTerm_integrable η) hs
  simp only [mellinTerm_integral] at h
  unfold G
  rw [h]
  have e : ∀ s ∈ Ioi η, ∑' k : Fin 12 → ℤ, mellinTerm η k s
      = (s - η) ^ 5 * (theta (Real.exp (-s)) ^ 12 - (1 + 2 * Real.exp (-s)) ^ 12) / 120 :=
    fun s hs' => mellinTerm_sum (hη.trans hs')
  rw [setIntegral_congr_fun measurableSet_Ioi e, integral_div]
  ring

end BecknerOnofri.V2.ThetaTail
