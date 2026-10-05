import BecknerOnofri.Friedrichs.MixedSpatialDefinitions

noncomputable section
open Set MeasureTheory
namespace BecknerOnofri.Friedrichs.MixedSpatial

lemma formPairing_continuous_right {d : ℕ} {α : MultiIndex d} (v : EnergySpace α) :
    Continuous (formPairing v) := by
  unfold formPairing
  fun_prop

lemma core_test_extends {d : ℕ} {α : MultiIndex d} {v : EnergySpace α} {g : H α}
    (h : ∀ w∈core α,formPairing v w=inner ℝ g w.1) :
    ∀ w∈formClosure α,formPairing v w=inner ℝ g w.1 := by
  intro w hw
  exact closure_minimal h
    (isClosed_eq (formPairing_continuous_right v) (continuous_const.inner continuous_fst)) hw

lemma inner_eq_integral_of_ae {d : ℕ} {α : MultiIndex d} {u v : H α} {f g : Space d → ℝ}
    (hu : (u : Space d → ℝ)=ᵐ[spatialMeasure α] f)
    (hv : (v : Space d → ℝ)=ᵐ[spatialMeasure α] g) :
    inner ℝ u v=∫ x,f x*g x ∂spatialMeasure α := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hu,hv] with x hx hy
  simp [hx,hy,mul_comm]

lemma integrable_mul_of_ae {d : ℕ} {α : MultiIndex d} {u v : H α} {f g : Space d → ℝ}
    (hu : (u : Space d → ℝ)=ᵐ[spatialMeasure α] f)
    (hv : (v : Space d → ℝ)=ᵐ[spatialMeasure α] g) :
    Integrable (fun x => f x*g x) (spatialMeasure α) := by
  apply (L2.integrable_inner (𝕜 := ℝ) u v).congr
  filter_upwards [hu,hv] with x hx hy
  simp [hx,hy,mul_comm]

#print axioms core_test_extends
end BecknerOnofri.Friedrichs.MixedSpatial
