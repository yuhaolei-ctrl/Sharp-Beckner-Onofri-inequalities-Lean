import BecknerOnofri.HeatGreenPairing
import BecknerOnofri.GreenCoordinateAE

/-! Critical entropy-energy bound by coordinate Green comparison and the
one-dimensional sharp inequality. The constants are actual finite reals. -/
noncomputable section
open MeasureTheory Legacy.TorusEndpoint
open scoped BigOperators
namespace BecknerOnofri.AdamsEndpoint
open Legacy.BecknerOnofri GreenHeatPointwise TorusMarginals
open Legacy.TorusEndpoint.PhysicalGreenL2 Legacy.TorusEndpoint.PhysicalGreenFiniteEnergy

theorem heatInteraction_coordinate_bound {d : ℕ} (hd : 0 < d)
    (rho : ProbabilityDensity d) (hr : MemLp rho.value 2 (torusMeasure d)) :
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

theorem critical_entropy_energy_succ {n : ℕ}
    (rho : ProbabilityDensity (n+1)) (hr : Continuous rho.value)
    (hpos : ∀ x, 0 < rho.value x) :
    ((n+1 : ℕ) : ℝ) * physicalGreenEnergy rho - densityEntropy rho.value ≤
      ((n+1 : ℕ) : ℝ) * coordinateComparisonConstant (n+1) := by
  have hd : 0 < n+1 := Nat.succ_pos n
  have hdR : (0 : ℝ) < (n+1 : ℕ) := by exact_mod_cast hd
  have hρ : MemLp rho.value 2 (torusMeasure (n+1)) := hr.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hcomp := heatInteraction_coordinate_bound hd rho hρ
  have hm := torusMarginalDensity_entropy_sum_le rho hr hpos
  have hi := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => coordinate_heatInteraction_entropy rho hr hpos i)
  have hsum := hi.trans hm
  have hdiv := div_le_div_of_nonneg_right hsum hdR.le
  rw [heatInteraction_eq_physical hd] at hcomp
  have hbound : physicalGreenEnergy rho ≤ densityEntropy rho.value / ((n+1 : ℕ) : ℝ) +
      coordinateComparisonConstant (n+1) := hcomp.trans (add_le_add hdiv le_rfl)
  have hmul := mul_le_mul_of_nonneg_left hbound hdR.le
  have he : ((n+1 : ℕ) : ℝ) * (densityEntropy rho.value / ((n+1 : ℕ) : ℝ)) =
      densityEntropy rho.value := by field_simp
  nlinarith

theorem critical_entropy_energy {d : ℕ} (hd : 0 < d)
    (rho : ProbabilityDensity d) (hr : Continuous rho.value)
    (hpos : ∀ x, 0 < rho.value x) :
    (d : ℝ) * physicalGreenEnergy rho - densityEntropy rho.value ≤
      (d : ℝ) * coordinateComparisonConstant d := by
  cases d with
  | zero => omega
  | succ n => exact critical_entropy_energy_succ rho hr hpos

#print axioms critical_entropy_energy
end BecknerOnofri.AdamsEndpoint
