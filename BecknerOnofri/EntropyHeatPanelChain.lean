import BecknerOnofri.EntropyHeatFiniteRules

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
namespace BecknerOnofri.HighDim.EntropyTail.HeatCertificate

structure RationalPanel where
  left : ℚ
  right : ℚ
  upper : ℚ
  deriving DecidableEq

def RationalPanel.weight (p : RationalPanel) (ζ : ℚ) : ℚ :=
  (p.upper/720)*((max (p.right-ζ) 0)^6-(max (p.left-ζ) 0)^6)

def chainCheck (a b : ℚ) : List RationalPanel → Bool
  | [] => decide (a=b)
  | p::ps => decide (a=p.left ∧ p.left≤p.right) && chainCheck p.right b ps

theorem chainCheck_le {a b : ℚ} {ps : List RationalPanel} (h : chainCheck a b ps = true) : a ≤ b := by
  induction ps generalizing a with
  | nil => have he : a=b := of_decide_eq_true h; exact he.le
  | cons p ps ih =>
    obtain ⟨hp, hr⟩ := Bool.and_eq_true_iff.mp h
    have hp' : a=p.left ∧ p.left≤p.right := of_decide_eq_true hp
    exact hp'.1.le.trans (hp'.2.trans (ih hr))

theorem rational_panel_bound (p : RationalPanel) (η : ℝ) (ζ : ℚ)
    (hp : 0 < p.left) (hab : p.left ≤ p.right) (hζη : (ζ : ℝ) ≤ η)
    (hU : heatComplement (p.left : ℝ) ≤ (p.upper : ℝ)) :
    (1/120 : ℝ)*(∫ s in (p.left : ℝ)..(p.right : ℝ),
      (max (s-η) 0)^5*heatComplement s) ≤ (p.weight ζ : ℝ) := by
  have h := panel_parameter_rounding (v := (p.left : ℝ)) (w := (p.right : ℝ))
    (η := η) (ζ := (ζ : ℝ)) (U := (p.upper : ℝ))
    (by exact_mod_cast hp) (by exact_mod_cast hab) hζη hU
  simpa only [RationalPanel.weight, Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat,
    Rat.cast_sub, Rat.cast_pow, Rat.cast_max, Rat.cast_zero] using h

theorem chain_integral_bound (ps : List RationalPanel) {a b : ℚ}
    (hc : chainCheck a b ps = true) (ha : 0 < a)
    (η : ℝ) (ζ : ℚ) (hζη : (ζ : ℝ) ≤ η)
    (hU : ∀ p ∈ ps, heatComplement (p.left : ℝ) ≤ (p.upper : ℝ)) :
    (1/120 : ℝ)*(∫ s in (a : ℝ)..(b : ℝ), (max (s-η) 0)^5*heatComplement s) ≤
      ((ps.map (fun p => p.weight ζ)).sum : ℚ) := by
  induction ps generalizing a with
  | nil =>
    have he : a=b := of_decide_eq_true hc
    subst a
    simp
  | cons p ps ih =>
    obtain ⟨hp, hr⟩ := Bool.and_eq_true_iff.mp hc
    have hp' : a=p.left ∧ p.left≤p.right := of_decide_eq_true hp
    obtain ⟨rfl, hab⟩ := hp'
    have hb : 0 < p.right := ha.trans_le hab
    have hend : p.right ≤ b := chainCheck_le hr
    have hi1 := heat_panel_integrable (v := (p.left : ℝ)) (w := (p.right : ℝ))
      (by exact_mod_cast ha) (by exact_mod_cast hab) η
    have hi2 := heat_panel_integrable (v := (p.right : ℝ)) (w := (b : ℝ))
      (by exact_mod_cast hb) (by exact_mod_cast hend) η
    rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2, mul_add]
    have hfirst := rational_panel_bound p η ζ ha hab hζη (hU p (List.mem_cons_self))
    have hrest := ih hr hb (fun q hq => hU q (List.mem_cons_of_mem p hq))
    simpa only [List.map_cons, List.sum_cons, Rat.cast_add] using add_le_add hfirst hrest

#print axioms chain_integral_bound
end BecknerOnofri.HighDim.EntropyTail.HeatCertificate
