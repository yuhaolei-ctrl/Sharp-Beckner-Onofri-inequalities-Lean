import BecknerOnofri.GibbsDifferenceBound
import BecknerOnofri.UniformReducedCubic

/-! Quantitative dependence of the actual complementary graph on the parameter. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter Asymptotics
open scoped Topology
namespace BecknerOnofri.HighDim.UniformComplementBounds
open ContinuousGibbs ContinuousFirstShell ContinuousComplement GreenLocalBranch ReducedEquation
open ReducedCubicExpansion QuadraticSlaving

def sliceMap (d : ℕ) (x : ℝ × Coordinates d) : ℝ × Coordinates d := (1,x.2)

theorem sliceMap_tendsto (d : ℕ) : Tendsto (sliceMap d) (𝓝 (1,0)) (𝓝 (1,0)) :=
  (continuous_const.prodMk continuous_snd).continuousAt

theorem correction_equation {d : ℕ} (hd : 12 ≤ d) (x : ℝ × Coordinates d)
    (hx : projectedEquation (greenContinuous d) (x,correction hd x) = 0) :
    correction hd x - x.1 • (continuousComplementGreen (by omega) (correction hd x) +
      nonlinearGreen d (nonlinearRemainder (potential hd x))) = 0 := by
  rw [projectedEquation_eq (greenContinuous d) (green_first_complement_zero (by omega)),
    linearPart_eq (by omega)] at hx
  exact hx

theorem correction_difference_resolvent {d : ℕ} (hd : 12 ≤ d) (x : ℝ × Coordinates d)
    (hx : projectedEquation (greenContinuous d) (x,correction hd x) = 0)
    (hs : projectedEquation (greenContinuous d) (sliceMap d x,correction hd (sliceMap d x)) = 0)
    (hμ0 : 0 ≤ x.1) (hμ2 : x.1 ≤ 2) :
    correction hd x - correction hd (sliceMap d x) =
      continuousComplementInverse hd hμ0 hμ2
        ((x.1-1) • (continuousComplementGreen (by omega) (correction hd (sliceMap d x)) +
          nonlinearGreen d (nonlinearRemainder (potential hd (sliceMap d x)))) +
         x.1 • nonlinearGreen d (nonlinearRemainder (potential hd x) -
           nonlinearRemainder (potential hd (sliceMap d x)))) := by
  let e := continuousComplementContinuousLinearEquiv hd hμ0 hμ2
  have he : e (correction hd x - correction hd (sliceMap d x)) =
      (x.1-1) • (continuousComplementGreen (by omega) (correction hd (sliceMap d x)) +
        nonlinearGreen d (nonlinearRemainder (potential hd (sliceMap d x)))) +
      x.1 • nonlinearGreen d (nonlinearRemainder (potential hd x) -
        nonlinearRemainder (potential hd (sliceMap d x))) := by
    have ht := congrArg (fun F : complement d →L[ℝ] complement d =>
      F (correction hd x - correction hd (sliceMap d x)))
      (continuousComplementContinuousLinearEquiv_toCLM hd hμ0 hμ2)
    change e _ = _ at ht
    rw [ht]
    have h1 := correction_equation hd x hx
    have h2 := correction_equation hd (sliceMap d x) hs
    simp only [show (sliceMap d x).1 = 1 from rfl, one_smul] at h2
    change correction hd x - correction hd (sliceMap d x) -
      x.1 • continuousComplementGreen (by omega) (correction hd x - correction hd (sliceMap d x)) = _
    rw [map_sub, map_sub]
    calc
      _ = (correction hd x - x.1 • (continuousComplementGreen (by omega) (correction hd x) +
              nonlinearGreen d (nonlinearRemainder (potential hd x)))) -
            (correction hd (sliceMap d x) - (continuousComplementGreen (by omega)
              (correction hd (sliceMap d x)) + nonlinearGreen d
              (nonlinearRemainder (potential hd (sliceMap d x))))) +
            ((x.1-1) • (continuousComplementGreen (by omega) (correction hd (sliceMap d x)) +
              nonlinearGreen d (nonlinearRemainder (potential hd (sliceMap d x)))) +
              x.1 • (nonlinearGreen d (nonlinearRemainder (potential hd x)) -
                nonlinearGreen d (nonlinearRemainder (potential hd (sliceMap d x))))) := by module
      _ = _ := by rw [h1, h2]; simp only [sub_zero, zero_add]
  exact ((e.symm_apply_eq).mpr he.symm).symm

theorem potential_difference {d : ℕ} (hd : 12 ≤ d) (x : ℝ × Coordinates d) :
    potential hd x - potential hd (sliceMap d x) =
      ((correction hd x - correction hd (sliceMap d x) : complement d) : Space d) := by
  change (assembly d x.2 + (correction hd x : Space d)) -
    (assembly d x.2 + (correction hd (sliceMap d x) : Space d)) = _
  change _ = (correction hd x : Space d) - (correction hd (sliceMap d x) : Space d)
  abel

end BecknerOnofri.HighDim.UniformComplementBounds
