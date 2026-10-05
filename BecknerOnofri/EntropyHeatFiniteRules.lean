module

public import BecknerOnofri.EntropyHeatQuadrature
public import BecknerOnofri.EntropyHeatTailIntegral

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped BigOperators
namespace BecknerOnofri.HighDim.EntropyTail

theorem panel_parameter_rounding {v w η ζ U : ℝ} (hv : 0 < v) (hvw : v ≤ w)
    (hζη : ζ ≤ η) (hU : heatComplement v ≤ U) :
    (1/120 : ℝ)*(∫ s in v..w, (max (s-η) 0)^5*heatComplement s) ≤
      (U/720)*((max (w-ζ) 0)^6-(max (v-ζ) 0)^6) := by
  have hm : (∫ s in v..w, (max (s-η) 0)^5*heatComplement s) ≤
      ∫ s in v..w, (max (s-ζ) 0)^5*heatComplement s := by
    apply intervalIntegral.integral_mono_on hvw
      (heat_panel_integrable hv hvw η) (heat_panel_integrable hv hvw ζ)
    intro s hs
    apply mul_le_mul_of_nonneg_right _ (heatComplement_nonneg (hv.trans_le hs.1))
    exact pow_le_pow_left₀ (le_max_right _ _) (max_le_max (by linarith) le_rfl) 5
  have hweight : 0 ≤ (max (w-ζ) 0)^6-(max (v-ζ) 0)^6 := by
    apply sub_nonneg.mpr
    exact pow_le_pow_left₀ (le_max_right _ _) (max_le_max (by linarith) le_rfl) 6
  apply ((mul_le_mul_of_nonneg_left hm (by norm_num : (0 : ℝ) ≤ 1/120)).trans
    (heat_panel_bound hv hvw ζ)).trans
  exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hU (by norm_num)) hweight

theorem positive_mellin_interval {v η T : ℝ} (hv : 0 < v) (hvη : v ≤ η) (hηT : η ≤ T) :
    (∫ s in v..T, (max (s-η) 0)^5*heatComplement s) =
      ∫ s in η..T, (s-η)^5*heatComplement s := by
  have hi1 := heat_panel_integrable hv hvη η
  have hi2 := heat_panel_integrable (hv.trans_le hvη) hηT η
  rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
  have hz : (∫ s in v..η, (max (s-η) 0)^5*heatComplement s) = 0 := by
    calc
      _ = ∫ _s in v..η, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [uIcc_of_le hvη] at hs
        dsimp only
        rw [max_eq_right (by linarith [hs.2]), zero_pow (by norm_num : 5 ≠ 0), zero_mul]
      _ = 0 := by simp
  rw [hz, zero_add]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le hηT] at hs
  dsimp only
  rw [max_eq_left (by linarith [hs.1])]

/-- A checked finite grid and checked endpoint enclosures imply the true G bound.
This theorem does not assert that any numerical enclosure has been checked. -/
theorem heatIntegral_le_finite {n : ℕ} (a U : ℕ → ℝ) (ha : Monotone a)
    (ha0 : 0 < a 0) (haEnd : a n = 20) {η ζ : ℝ}
    (hstart : a 0 ≤ η) (hη20 : η ≤ 20) (hζη : ζ ≤ η)
    (hU : ∀ i < n, heatComplement (a i) ≤ U i) :
    heatIntegral η <
      (∑ i ∈ Finset.range n, (U i/720)*
        ((max (a (i+1)-ζ) 0)^6-(max (a i-ζ) 0)^6)) + 667/(2*10^32) := by
  have hη : 0 < η := ha0.trans_le hstart
  have hapos (i : ℕ) : 0 < a i := ha0.trans_le (ha (Nat.zero_le i))
  have hstep (i : ℕ) : a i ≤ a (i+1) := ha (Nat.le_succ i)
  have hp := RadialQuadrature.finite_interval_upper (n := n) a
    (fun s : ℝ => (1/120)*((max (s-η) 0)^5*heatComplement s))
    (fun i => (U i/720)*((max (a (i+1)-ζ) 0)^6-(max (a i-ζ) 0)^6))
    (fun i _ => (heat_panel_integrable (hapos i) (hstep i) η).const_mul (1/120 : ℝ))
    (fun i hi => by
      rw [intervalIntegral.integral_const_mul]
      exact panel_parameter_rounding (hapos i) (hstep i) hζη (hU i hi))
  rw [haEnd, intervalIntegral.integral_const_mul, positive_mellin_interval ha0 hstart hη20] at hp
  have hsplit := intervalIntegral.integral_Ioi_sub_Ioi (heat_integrable hη) hη20
  have ht := heat_integral_beyond_twenty hη hη20
  unfold heatIntegral
  linarith

#print axioms heatIntegral_le_finite
end BecknerOnofri.HighDim.EntropyTail
