module

public import BecknerOnofri.CosineMixtureStatementDefinitions
public import BecknerOnofri.ExtendedMixtureEnergy
public import BecknerOnofri.EntropyShearer.PaperStatement

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ENNReal
open Finset MeasureTheory
namespace BecknerOnofri.CosineMixtureTransfer
open RectangleLattice RandomRectangles Legacy.TorusEndpoint
open Legacy.BecknerOnofri Legacy.D10

lemma weight_nat_exponent_eq {d r : ℕ} (hr : 0 < r) (k : Frequency d) :
    weight (r:ℝ) k = if k = 0 then 0 else (HighDim.frequencyLength k ^ r)⁻¹ := by
  by_cases hk : k = 0
  · subst k
    simp only [if_true]
    exact weight_zero (by exact_mod_cast hr)
  · rw [if_neg hk]
    unfold weight
    rw [Real.rpow_neg (normSq_nonneg k)]
    congr 1
    change (normSq k)^((r:ℝ)/2) = (Real.sqrt (normSq k))^r
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (normSq_nonneg k)]
    congr 1
    ring

theorem weightedEnergyENN_eq_inversePowerEnergy {d r : ℕ} (hr : 0 < r)
    (f : Torus d → ℝ) : weightedEnergyENN (weight (r:ℝ)) f = HighDim.inversePowerEnergy r f := by
  let g : Frequency d → ℝ≥0∞ := fun k => ENNReal.ofReal (weight (r:ℝ) k * ‖densityFourier f k‖^2)
  have hg : Function.support g ⊆ {k : Frequency d | k ≠ 0} := by
    intro k hk hz
    subst k
    exact hk (by simp [g, weight_zero (by exact_mod_cast hr : (0:ℝ)<r)])
  change (∑' k, g k) = _
  rw [← tsum_subtype_eq_of_support_subset hg]
  unfold HighDim.inversePowerEnergy
  apply tsum_congr
  intro k
  simp only [g, weight_nat_exponent_eq hr, if_neg k.property]
  rfl

lemma countableCosineMixture_eq {d : ℕ} (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ) :
    HighDim.countableCosineMixture w N = CosineMixtureApproximation.rho w N := rfl

lemma fullAvg_congr_ae {d : ℕ} (I : Finset (Fin d)) {f g : Torus d → ℝ}
    (h : f =ᵐ[torusMeasure d] g) :
    HighDim.EntropyShearer.fullAvg I f =ᵐ[torusMeasure d] HighDim.EntropyShearer.fullAvg I g := by
  have h' := (HighDim.EntropyShearer.mix_measurePreserving I).quasiMeasurePreserving.ae h
  have h'' := Measure.ae_ae_of_ae_prod h'
  exact h''.mono (fun x hx => integral_congr_ae hx)

#print axioms weightedEnergyENN_eq_inversePowerEnergy
#print axioms fullAvg_congr_ae
end BecknerOnofri.CosineMixtureTransfer
