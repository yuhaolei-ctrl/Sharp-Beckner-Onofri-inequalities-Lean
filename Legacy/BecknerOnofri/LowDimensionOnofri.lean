module

public import Legacy.BecknerOnofri.EndpointThroughTen
public import Legacy.BecknerOnofri.EndpointOnofri
public import Legacy.BecknerOnofri.EndpointPotentialSharpness

@[expose] public section

/-! Unconditional potential inequality through dimension ten, including the
manuscript's exact physical normalization and its optimal coefficient. -/
noncomputable section
open MeasureTheory Legacy.TorusEndpoint
namespace Legacy.BecknerOnofri
open TorusSobolev SubcriticalAttainment SobolevCentering EndpointPotential

theorem onofri_through_ten {d : ℕ} (hd : 1 ≤ d) (hd10 : d ≤ 10) {u : TorusL2 d}
    (hr : RealPotential u) (hs : Summable (weightedSquare (fourierIsometry d u))) :
    Integrable (fun x => Real.exp ((u x).re - ∫ y, (u y).re ∂torusMeasure d)) (torusMeasure d) ∧
      Real.log (centeredPartition u) ≤
        (1/(4*(d:ℝ)*endpointSymbolConstant d))*manuscriptEnergy u :=
  manuscript_onofri (by omega) (endpoint_through_ten d hd hd10) hr hs

theorem onofri_coefficient_isLeast {d : ℕ} (hd : 1 ≤ d) (hd10 : d ≤ 10) :
    IsLeast {a : ℝ | ∀ u : TorusL2 d, Admissible u →
      Real.log (partition u) ≤ a*criticalEnergy u} (coefficient d) :=
  coefficient_isLeast (by omega) (endpoint_through_ten d hd hd10)

theorem onofri_sharpness {d : ℕ} (hd : 1 ≤ d) (hd10 : d ≤ 10) {a : ℝ}
    (ha : a < coefficient d) :
    ∃ u : TorusL2 d, Admissible u ∧ Integrable (fun x => Real.exp (u x).re) (torusMeasure d) ∧
      a*criticalEnergy u < Real.log (partition u) :=
  potential_sharpness (by omega) (endpoint_through_ten d hd hd10) ha

theorem centeredPartition_admissible {d : ℕ} {u : TorusL2 d} (hu : Admissible u) :
    centeredPartition u = partition u := by
  rw [centeredPartition_eq]
  have hc : center u = u := by
    unfold center
    rw [hu.2.1]
    have hz : constant d 0 = 0 := by
      apply Lp.ext
      filter_upwards [constant_ae d 0, Lp.coeFn_zero ℂ 2 (torusMeasure d)] with x hx hy
      exact hx.trans hy.symm
    rw [hz, sub_zero]
  rw [hc]

theorem onofri_physical_coefficient_isLeast {d : ℕ} (hd : 1 ≤ d) (hd10 : d ≤ 10) :
    IsLeast {a : ℝ | ∀ u : TorusL2 d, RealPotential u →
      Summable (weightedSquare (fourierIsometry d u)) →
      Real.log (centeredPartition u) ≤ a*manuscriptEnergy u}
      (1/(4*(d:ℝ)*endpointSymbolConstant d)) := by
  refine ⟨fun u hr hs => (onofri_through_ten hd hd10 hr hs).2, ?_⟩
  intro a ha
  have hpos : 0 < (2*Real.pi)^d := pow_pos (mul_pos (by norm_num) Real.pi_pos) _
  have h := coefficient_le_of_potential_bound (by omega) (endpoint_through_ten d hd hd10)
    (a*(2*Real.pi)^d) (by
      intro u hu
      have hh := ha u hu.1 hu.2.2
      rw [centeredPartition_admissible hu, manuscriptEnergy_eq (by omega) u hu.2.2] at hh
      simpa only [mul_assoc] using hh)
  have hc : coefficient d = (1/(4*(d:ℝ)*endpointSymbolConstant d))*(2*Real.pi)^d := by
    rw [← endpointSymbolConstant_mul_sigma (by omega : 0 < d)]
    unfold coefficient endpointConstant
    field_simp
    exact (mul_div_cancel_right₀ (endpointSigma d)
      (endpointSymbolConstant_pos (by omega : 0 < d)).ne').symm
  rw [hc] at h
  exact (mul_le_mul_iff_left₀ hpos).mp h

#print axioms onofri_through_ten
#print axioms onofri_sharpness
#print axioms onofri_physical_coefficient_isLeast
end Legacy.BecknerOnofri
