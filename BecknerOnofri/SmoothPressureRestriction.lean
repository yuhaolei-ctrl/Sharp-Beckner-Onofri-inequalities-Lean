import BecknerOnofri.PressureDuality
import BecknerOnofri.HeatDensitySmooth

/-! The full pressure supremum can be taken over smooth strictly positive
densities. Heat entropy contraction and convergence of the actual Fourier
energy suffice, including when the pressure is infinite. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped Topology
namespace BecknerOnofri.HighDim

theorem pressure_eq_smooth_sup {d : ℕ} (hd : 0 < d) (β : ℝ) :
    pressure d β = ⨆ (ρ : ProbabilityDensity d) (_ : ρ.FiniteEntropy)
      (_ : SmoothOnTorus ρ.value) (_ : ∀ x, 0 < ρ.value x),
      (β / (2 * spectralThreshold d) : ℝ) * (spectralEnergy ρ).toEReal -
        (entropy ρ : EReal) := by
  apply le_antisymm
  · unfold pressure
    refine iSup_le (fun ρ => iSup_le (fun hρ => ?_))
    let t : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
    have ht (n : ℕ) : 0 < t n := by dsimp [t]; positivity
    let r := fun n => Legacy.BecknerOnofri.HeatDensityApproximation.heatDensity
      (Bridge.density ρ) (ht n)
    let η := fun n => Bridge.rawDensity (r n)
    have hη (n : ℕ) : (η n).FiniteEntropy :=
      Legacy.BecknerOnofri.HeatDensityApproximation.heatDensity_finiteEntropy _ (ht n)
    have hlim := heat_fourierEnergy_tendsto hd (Bridge.density ρ) hρ t ht
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hlim' := EReal.tendsto_coe.mpr
      ((hlim.const_mul (β / (2 * spectralThreshold d))).sub_const (entropy ρ))
    have hterms : Legacy.BecknerOnofri.fourierEnergy (Bridge.density ρ) =
        ∑' k, spectralTerm ρ k := tsum_congr (Bridge.densitySpectralTerm_eq ρ)
    rw [spectralEnergy_coe_eq_tsum hd ρ hρ, ← EReal.coe_mul, ← EReal.coe_sub, ← hterms]
    apply le_of_tendsto hlim'
    refine Eventually.of_forall (fun n => ?_)
    have hent := Legacy.BecknerOnofri.HeatDensityApproximation.heatDensity_entropy_le
      (Bridge.density ρ) hρ (ht n)
    have hs : SmoothOnTorus (η n).value := HeatSmooth.heatValue_smooth _ (ht n)
    have hp : ∀ x, 0 < (η n).value x :=
      Legacy.BecknerOnofri.HeatDensityApproximation.heatValue_pos _ (ht n)
    apply le_trans ?_ (le_iSup_of_le (η n) (le_iSup_of_le (hη n)
      (le_iSup_of_le hs (le_iSup_of_le hp le_rfl))))
    rw [spectralEnergy_coe_eq_tsum hd (η n) (hη n), ← EReal.coe_mul, ← EReal.coe_sub]
    apply EReal.coe_le_coe_iff.mpr
    have he : Legacy.BecknerOnofri.fourierEnergy (r n) =
        ∑' k, spectralTerm (η n) k := tsum_congr (Bridge.densitySpectralTerm_eq (η n))
    rw [he]
    exact sub_le_sub_left hent _
  · refine iSup_le (fun ρ => iSup_le (fun hρ => iSup_le (fun _ => iSup_le (fun _ => ?_))))
    exact le_iSup_of_le ρ (le_iSup_of_le hρ le_rfl)

#print axioms pressure_eq_smooth_sup
end BecknerOnofri.HighDim
