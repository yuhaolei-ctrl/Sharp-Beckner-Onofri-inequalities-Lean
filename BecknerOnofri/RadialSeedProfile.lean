import BecknerOnofri.RadialGreenFinite
import BecknerOnofri.RadialOrigin
import BecknerOnofri.RadialEndpointChange

/-! The source's actual diagonal profile and finite upper profile, including the
singular logarithmic majorant used for rigorous integration at the origin. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped BigOperators
namespace BecknerOnofri.HighDim.RadialSeedReduction
open RadialGreenHeat RadialGreenPoisson RadialThetaTail SpatialThetaDiagonal RadialQuadrature

abbrev sourceC : ℝ := Real.pi^6/120
abbrev sourceS₀ : ℝ := 1/2^48

abbrev upperProfile := finiteRadialUpper

def originConstant (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  heatFiniteUpper a n 0-(5771/10000:ℝ)*sourceC+RadialPoissonImages.J12-1/720+2*sourceC*sourceS₀

theorem source_power_pos : 0 < (6:ℝ)-(7/10:ℝ)*sourceC := by
  have hp : Real.pi^6<(3.15:ℝ)^6 := by gcongr; exact Real.pi_lt_d2
  norm_num at hp
  dsimp [sourceC]
  nlinarith

theorem sourceS₀_pos : 0 < sourceS₀ := by norm_num [sourceS₀]
theorem sourceS₀_lt : sourceS₀ < (7/16:ℝ) := by norm_num [sourceS₀]

theorem profile_origin_bound (a : ℕ → ℝ) (n : ℕ) (ha : Monotone a) (ha0 : a 0=1)
    {S : ℝ} (hS : S∈Ioc (0:ℝ) sourceS₀) :
    radialGreen 12 S≤originConstant a n-sourceC*Real.log S := by
  have hS1 : S≤1 := hS.2.trans (le_of_lt (lt_trans sourceS₀_lt (by norm_num)))
  have hh := radialGreen_le_E1_images_heat (show S∈Ioc (0:ℝ) 12 by
    exact ⟨hS.1,by linarith⟩)
  have hheat := heatPart_diagonal_le_finite_zero a n ha ha0
    (radialAngle_mem (by norm_num : 0<12) ⟨hS.1.le,by norm_num; linarith⟩)
  have he := mul_le_mul_of_nonneg_left (RadialOrigin.origin_E1_bound hS.1 hS.2
    (show sourceS₀≤1 by exact le_of_lt (lt_trans sourceS₀_lt (by norm_num))))
    (show 0≤sourceC by positivity)
  dsimp only [originConstant,sourceC] at *
  linarith

#print axioms profile_origin_bound

#print axioms source_power_pos
end BecknerOnofri.HighDim.RadialSeedReduction
