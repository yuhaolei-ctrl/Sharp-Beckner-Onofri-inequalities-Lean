module

public import BecknerOnofri.V2.Vocab.ExternalInputs
public import BecknerOnofri.HeatGreenPairing
public import BecknerOnofri.GreenCoordinateAE
public import BecknerOnofri.SmoothPressureRestriction
public import BecknerOnofri.FiniteEntropyPhysical
public import BecknerOnofri.LowDimensionDefinitions
public import BecknerOnofri.UniformFourierHessian
public import Legacy.BecknerOnofri.Endpoint
public import Legacy.TorusEndpoint.PhysicalGreenFiniteEnergy

@[expose] public section

/-! # `CriticalAdamsInput d`: the critical Adams-type bound without the low-dimensional endpoint chain

The repository's `HighDim.critical_adams_bound` is proved in `AdamsEndpointPressure` from
`AdamsEndpoint.critical_entropy_energy` (coordinate Green comparison, entropy subadditivity of the
coordinate marginals, and the one-dimensional inequality `heatInteraction ρ ≤ Ent ρ` on `𝕋¹`).  The only
place where that chain meets the old endpoint theorems is the one-dimensional inequality, obtained in
`HeatGreenPairing.circle_heatInteraction_entropy` from `Legacy.BecknerOnofri.physical_green_endpoint`
(whose proof calls `endpoint_through_ten`).  Here the same chain is re-run with the one-dimensional
inequality taken from `Legacy.BecknerOnofri.endpoint_one` (the Milin/Euler-recurrence proof,
`Legacy.D10.CircleEntropy.entropy_bound`):

* `circle_physicalGreen_le_entropy`, `circle_heatInteraction_entropy_indep`: `d = 1`;
* `heatInteraction_coordinate_bound`, `coordinate_heatInteraction_entropy_indep`,
  `critical_entropy_energy_indep`: copies of the statements and proofs in `AdamsEndpointEnergy` /
  `HeatGreenPairing`, with only the `d = 1` ingredient replaced;
* `pressure_at_collapse_le`, `coefficient_at_collapse_le`, `critical_adams_bound_indep`: copies of
  the corresponding declarations of `AdamsEndpointPressure`.

The leading constant is the sharp `A_crit(d) = 1/(4 d c_d)` (`collapseCoefficient d`). -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Legacy.TorusEndpoint
open scoped BigOperators

namespace BecknerOnofri.V2.Reaudit.ExternalInputs
open Legacy.BecknerOnofri Legacy.TorusEndpoint.PhysicalGreenL2 Legacy.TorusEndpoint.PhysicalGreenFiniteEnergy
open BecknerOnofri.AdamsEndpoint
open Legacy.BecknerOnofri.GreenHeatPointwise Legacy.BecknerOnofri.TorusMarginals
open Legacy.BecknerOnofri.GreenExponentialIntegrability

/-- `d = 1`: the physical Green energy is at most the entropy, from the Milin/Euler-recurrence proof
(`endpoint_one`), not from `endpoint_through_ten`. -/
theorem circle_physicalGreen_le_entropy (rho : Legacy.TorusEndpoint.ProbabilityDensity 1)
    (hr : rho.FiniteEntropy) : physicalGreenEnergy rho ≤ densityEntropy rho.value := by
  obtain ⟨hs, hE⟩ := Legacy.BecknerOnofri.endpoint_one rho hr
  have hle := (physicalGreen_integrable_and_le_spectral (by norm_num : 0 < 1) rho hs).2
  rw [endpointConstant_one] at hE
  have hn : densitySpectralEnergy rho = fourierEnergy rho / 2 := by
    rw [normalized_energy, endpointSigma_one]
  linarith

theorem circle_heatInteraction_entropy_indep (rho : Legacy.TorusEndpoint.ProbabilityDensity 1)
    (hr : rho.FiniteEntropy) : heatInteraction rho ≤ densityEntropy rho.value := by
  rw [heatInteraction_eq_physical (by norm_num)]
  exact circle_physicalGreen_le_entropy rho hr

theorem coordinate_heatInteraction_entropy_indep {n : ℕ}
    (rho : Legacy.TorusEndpoint.ProbabilityDensity (n+1)) (hr : Continuous rho.value)
    (hpos : ∀ x, 0 < rho.value x) (i : Fin (n+1)) :
    (∫ x, ∫ y, heatGreen (coordinateCircle i x-coordinateCircle i y) * rho.value x * rho.value y
      ∂torusMeasure (n+1) ∂torusMeasure (n+1)) ≤
      densityEntropy (torusMarginalDensity rho hr hpos i).value := by
  rw [torusMarginalDensity_kernel_pairing rho hr hpos i heatGreen (measurable_heatGreen 1)
    ((heatGreen_memLp (by norm_num : 0 < (1 : ℕ))).integrable (by norm_num))]
  exact circle_heatInteraction_entropy_indep _ (torusMarginalDensity_finiteEntropy rho hr hpos i)

theorem heatInteraction_coordinate_bound {d : ℕ} (hd : 0 < d)
    (rho : Legacy.TorusEndpoint.ProbabilityDensity d) (hr : MemLp rho.value 2 (torusMeasure d)) :
    heatInteraction rho ≤
      (∑ i : Fin d, ∫ x, ∫ y,
        heatGreen (coordinateCircle i x-coordinateCircle i y) * rho.value x * rho.value y
          ∂torusMeasure d ∂torusMeasure d) / (d : ℝ) + coordinateComparisonConstant d := by
  let μ := (torusMeasure d).prod (torusMeasure d)
  let F := fun p : Torus d × Torus d => heatGreen (p.1-p.2) * rho.value p.1 * rho.value p.2
  let G := fun (i : Fin d) (p : Torus d × Torus d) =>
    heatGreen (coordinateCircle i (p.1-p.2)) * rho.value p.1 * rho.value p.2
  let W := fun p : Torus d × Torus d => rho.value p.1 * rho.value p.2
  have hF : Integrable F μ := kernelInteraction_integrable rho hr heatGreen (heatGreen_memLp hd)
  have hG (i : Fin d) : Integrable (G i) μ :=
    kernelInteraction_integrable rho hr _
      ((heatGreen_memLp (by norm_num : 0 < (1 : ℕ))).comp_measurePreserving
        (coordinateCircle_measurePreserving i))
  have hW : Integrable W μ := rho.integrable.mul_prod rho.integrable
  have hsum : Integrable (fun p => ∑ i, G i p) μ := integrable_finsetSum _ (fun i _ => hG i)
  have hh : (∫ p, F p ∂μ) ≤ ∫ p,
      (∑ i, G i p) / (d : ℝ) + coordinateComparisonConstant d * W p ∂μ := by
    apply integral_mono_ae hF ((hsum.div_const _).add (hW.const_mul _))
    filter_upwards [(subtraction_measurePreserving d).quasiMeasurePreserving.ae
      (heatGreen_average_coordinates_ae hd), density_product_nonneg_ae rho] with p hp hρ
    change F p ≤ (∑ i, G i p) / (d : ℝ) + coordinateComparisonConstant d * W p
    have hh := mul_le_mul_of_nonneg_right hp (mul_nonneg hρ.1 hρ.2)
    calc
      F p = heatGreen (p.1-p.2) * (rho.value p.1 * rho.value p.2) := by dsimp [F]; ring
      _ ≤ ((∑ i, heatGreen (fun _ : Fin 1 => (p.1-p.2) i)) / (d : ℝ) +
          coordinateComparisonConstant d) * (rho.value p.1 * rho.value p.2) := hh
      _ = _ := by
        have heq : (∑ i, G i p) =
            (∑ i, heatGreen (fun _ : Fin 1 => (p.1-p.2) i)) * rho.value p.1 * rho.value p.2 := by
          change (∑ i, heatGreen (fun _ : Fin 1 => (p.1-p.2) i) * rho.value p.1 * rho.value p.2) = _
          rw [← Finset.sum_mul, ← Finset.sum_mul]
        rw [heq]
        dsimp only [W]
        ring
  rw [integral_add (hsum.div_const _) (hW.const_mul _),integral_div,
    integral_finsetSum _ (fun i _ => hG i), integral_const_mul] at hh
  have hmass : (∫ p, W p ∂μ) = 1 := by
    change (∫ p : Torus d × Torus d, rho.value p.1 * rho.value p.2
      ∂(torusMeasure d).prod (torusMeasure d)) = 1
    rw [integral_prod_mul,rho.mass,one_mul]
  rw [hmass,mul_one,integral_prod F hF] at hh
  change heatInteraction rho ≤ _ at hh
  convert hh using 1
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  exact (integral_prod (G i) (hG i)).symm

theorem critical_entropy_energy_succ_indep {n : ℕ}
    (rho : Legacy.TorusEndpoint.ProbabilityDensity (n+1)) (hr : Continuous rho.value)
    (hpos : ∀ x, 0 < rho.value x) :
    ((n+1 : ℕ) : ℝ) * physicalGreenEnergy rho - densityEntropy rho.value ≤
      ((n+1 : ℕ) : ℝ) * coordinateComparisonConstant (n+1) := by
  have hd : 0 < n+1 := Nat.succ_pos n
  have hdR : (0 : ℝ) < (n+1 : ℕ) := by exact_mod_cast hd
  have hρ : MemLp rho.value 2 (torusMeasure (n+1)) :=
    hr.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hcomp := heatInteraction_coordinate_bound hd rho hρ
  have hm := torusMarginalDensity_entropy_sum_le rho hr hpos
  have hi := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => coordinate_heatInteraction_entropy_indep rho hr hpos i)
  have hsum := hi.trans hm
  have hdiv := div_le_div_of_nonneg_right hsum hdR.le
  rw [heatInteraction_eq_physical hd] at hcomp
  have hbound : physicalGreenEnergy rho ≤ densityEntropy rho.value / ((n+1 : ℕ) : ℝ) +
      coordinateComparisonConstant (n+1) := hcomp.trans (add_le_add hdiv le_rfl)
  have hmul := mul_le_mul_of_nonneg_left hbound hdR.le
  have he : ((n+1 : ℕ) : ℝ) * (densityEntropy rho.value / ((n+1 : ℕ) : ℝ)) =
      densityEntropy rho.value := by field_simp
  nlinarith

theorem critical_entropy_energy_indep {d : ℕ} (hd : 0 < d)
    (rho : Legacy.TorusEndpoint.ProbabilityDensity d) (hr : Continuous rho.value)
    (hpos : ∀ x, 0 < rho.value x) :
    (d : ℝ) * physicalGreenEnergy rho - densityEntropy rho.value ≤
      (d : ℝ) * coordinateComparisonConstant d := by
  cases d with
  | zero => omega
  | succ n => exact critical_entropy_energy_succ_indep rho hr hpos

end BecknerOnofri.V2.Reaudit.ExternalInputs

/-! ### Transfer to the pressure and to the potentials (copy of `AdamsEndpointPressure`) -/

namespace BecknerOnofri.V2.Reaudit.ExternalInputs
open BecknerOnofri.HighDim

theorem pressure_at_collapse_le_indep {d : ℕ} (hd : 0 < d) :
    pressure d (2*(d:ℝ)) ≤ ((d:ℝ)*AdamsEndpoint.coordinateComparisonConstant d : ℝ) := by
  rw [pressure_eq_smooth_sup hd]
  refine iSup_le (fun ρ => iSup_le (fun hρ => iSup_le (fun hs => iSup_le (fun hp => ?_))))
  have hc := critical_entropy_energy_indep hd (Bridge.density ρ)
    (UniformFourier.smooth_continuous hs) hp
  rw [FiniteEntropyPhysical.physical_eq_spectral hd (Bridge.density ρ) hρ,
    Legacy.BecknerOnofri.normalized_energy] at hc
  have he : Legacy.BecknerOnofri.fourierEnergy (Bridge.density ρ) = ∑' k, spectralTerm ρ k :=
    tsum_congr (Bridge.densitySpectralTerm_eq ρ)
  rw [he] at hc
  change (d:ℝ)*((∑' k, spectralTerm ρ k)/spectralThreshold d)-entropy ρ ≤ _ at hc
  rw [spectralEnergy_coe_eq_tsum hd ρ hρ,← EReal.coe_mul,← EReal.coe_sub]
  apply EReal.coe_le_coe_iff.mpr
  convert hc using 1 <;> ring

theorem coefficient_at_collapse_le_indep {d : ℕ} (hd : 0 < d) :
    coefficientDefect d (collapseCoefficient d) ≤
      ((d:ℝ)*AdamsEndpoint.coordinateComparisonConstant d : ℝ) := by
  have hβ : 0 < 2*(d:ℝ) := mul_pos (by norm_num) (Nat.cast_pos.mpr hd)
  have he : spectralThreshold d / (2*(2*(d:ℝ))*(2*Real.pi)^d) = collapseCoefficient d := by
    unfold collapseCoefficient
    congr 1
    ring
  have hh := pressure_at_collapse_le_indep hd
  rw [pressure_eq_coefficientDefect hd hβ,he] at hh
  exact hh

/-- Same statement as `HighDim.critical_adams_bound`. -/
theorem critical_adams_bound_indep {d : ℕ} (hd : 0 < d) :
    ∃ B : ℝ, ∀ u : HighDim.Torus d → ℝ, InCriticalSobolev u →
      logPartition u ≤ ((collapseCoefficient d * potentialEnergy u + B : ℝ) : EReal) := by
  refine ⟨(d:ℝ)*AdamsEndpoint.coordinateComparisonConstant d, fun u hu => ?_⟩
  have hself : logPartition u - ((collapseCoefficient d * potentialEnergy u : ℝ) : EReal) ≤
      coefficientDefect d (collapseCoefficient d) :=
    le_iSup_of_le u (le_iSup_of_le hu le_rfl)
  have hh := hself.trans (coefficient_at_collapse_le_indep hd)
  rw [logPartition_eq_log_integral hd u hu,← EReal.coe_sub] at hh
  have hreal := EReal.coe_le_coe_iff.mp hh
  rw [logPartition_eq_log_integral hd u hu]
  apply EReal.coe_le_coe_iff.mpr
  linarith

/-- **`eq:section2-critical-adams`** (the Prop `V2.Vocab.CriticalAdamsInput d`), all `d ≥ 1`, with the
sharp leading constant `A_crit(d) = 1/(4 d c_d)`. -/
theorem criticalAdams {d : ℕ} (hd : 0 < d) : V2.Vocab.CriticalAdamsInput d :=
  (V2.Vocab.criticalAdamsInput_iff hd).2 (critical_adams_bound_indep hd)

end BecknerOnofri.V2.Reaudit.ExternalInputs
