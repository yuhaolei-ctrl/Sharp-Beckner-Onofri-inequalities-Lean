module

public import BecknerOnofri.V2.ThetaTail.Mellin
public import BecknerOnofri.V2.ThetaTail.LambertLog
public import Legacy.TorusEndpoint.IntegrableSeries
public import Mathlib.Analysis.SpecialFunctions.Log.Summable

@[expose] public section

/-! # Termwise integration of Lambert series (Appendix A.1, "Termwise integration ...")

"Termwise integration of the Lambert series is justified by absolute convergence for η > 0":
for nonnegative `a` with `∑ a_m e^{-η b m}/(b m)^6 < ∞`,

 `∫_η^∞ (s-η)^5 ∑_m a_m e^{-s b m} ds = 120 ∑_m a_m e^{-η b m}/(b m)^6`,

together with integrability of the integrand.  Also the Euler-product bounds
`0 ≤ ∏(1 - q^{2m})^{12} ≤ (1-q²)^{12}` and `σ₅(m) ≤ m⁶`. -/
noncomputable section
open Finset Filter Topology MeasureTheory Set
namespace BecknerOnofri.V2.ThetaTail

theorem lambert_integral (η b : ℝ) (hb : 0 < b) (a : ℕ+ → ℝ) (ha : ∀ m, 0 ≤ a m)
    (hs : Summable (fun m : ℕ+ => a m * Real.exp (-η * (b * (m : ℕ))) / (b * (m : ℕ)) ^ 6)) :
    Integrable (fun s : ℝ => (s - η) ^ 5 * ∑' m : ℕ+, a m * Real.exp (-s * (b * (m : ℕ))))
        (volume.restrict (Ioi η)) ∧
      ∫ s in Ioi η, (s - η) ^ 5 * ∑' m : ℕ+, a m * Real.exp (-s * (b * (m : ℕ)))
        = 120 * ∑' m : ℕ+, a m * Real.exp (-η * (b * (m : ℕ))) / (b * (m : ℕ)) ^ 6 := by
  set F : ℕ+ → ℝ → ℝ := fun m s => a m * ((s - η) ^ 5 * Real.exp (-s * (b * (m : ℕ)))) with hF
  have hbm : ∀ m : ℕ+, 0 < b * (m : ℕ) := fun m => mul_pos hb (by exact_mod_cast m.pos)
  have hF_int : ∀ m, Integrable (F m) (volume.restrict (Ioi η)) :=
    fun m => (integrableOn_pow_five_exp (hbm m) η).const_mul (a m)
  have hF_nonneg : ∀ m, ∀ s ∈ Ioi η, 0 ≤ F m s := by
    intro m s hs'
    exact mul_nonneg (ha m) (mul_nonneg (pow_nonneg (sub_nonneg.2 (le_of_lt hs')) 5)
      (Real.exp_pos _).le)
  have hnorm : ∀ m, ∫ s, ‖F m s‖ ∂(volume.restrict (Ioi η))
      = 120 * (a m * Real.exp (-η * (b * (m : ℕ))) / (b * (m : ℕ)) ^ 6) := by
    intro m
    have : ∫ s in Ioi η, ‖F m s‖ = ∫ s in Ioi η, F m s :=
      setIntegral_congr_fun measurableSet_Ioi (fun s hs' => Real.norm_of_nonneg (hF_nonneg m s hs'))
    rw [this]
    simp only [hF]
    rw [integral_const_mul, integral_pow_five_exp (hbm m) η]
    ring
  have hsum : Summable (fun m => ∫ s, ‖F m s‖ ∂(volume.restrict (Ioi η))) := by
    simp_rw [hnorm]; exact hs.mul_left 120
  have heq : ∀ s : ℝ, (s - η) ^ 5 * ∑' m : ℕ+, a m * Real.exp (-s * (b * (m : ℕ)))
      = ∑' m : ℕ+, F m s := by
    intro s
    rw [← tsum_mul_left]
    refine tsum_congr fun m => ?_
    simp only [hF]; ring
  simp_rw [heq]
  refine ⟨Legacy.TorusEndpoint.IntegrableSeries.integrable_tsum_of_summable_integral_norm hF_int hsum,
    ?_⟩
  rw [← integral_tsum_of_summable_integral_norm hF_int hsum]
  rw [← tsum_mul_left]
  refine tsum_congr fun m => ?_
  have : ∫ s, F m s ∂(volume.restrict (Ioi η)) = ∫ s in Ioi η, ‖F m s‖ :=
    (setIntegral_congr_fun measurableSet_Ioi
      (fun s hs' => (Real.norm_of_nonneg (hF_nonneg m s hs')).symm))
  rw [this, hnorm]

/-- `σ₅(m) ≤ m⁶` -/
theorem sigma5_le (m : ℕ) : sigma5 m ≤ (m : ℝ) ^ 6 := by
  unfold sigma5
  have h : ArithmeticFunction.sigma 5 m ≤ m ^ 6 := by
    rw [ArithmeticFunction.sigma_apply]
    calc ∑ d ∈ m.divisors, d ^ 5 ≤ ∑ d ∈ m.divisors, m ^ 5 := by
          refine sum_le_sum fun d hd => ?_
          exact Nat.pow_le_pow_left (Nat.divisor_le hd) 5
      _ = m.divisors.card * m ^ 5 := by simp
      _ ≤ m * m ^ 5 := by
          gcongr
          exact Nat.card_divisors_le_self m
      _ = m ^ 6 := by ring
  exact_mod_cast h

theorem sigma5_nonneg (m : ℕ) : 0 ≤ sigma5 m := Nat.cast_nonneg _

end BecknerOnofri.V2.ThetaTail
