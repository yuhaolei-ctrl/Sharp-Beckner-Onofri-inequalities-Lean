import BecknerOnofri.RadialGreenBounds
import BecknerOnofri.RadialHeatPanels

/-! The full finite upper profile used by the radial seed, connected to the
actual Fourier Green kernel through the proved heat and Poisson identities. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped BigOperators
namespace BecknerOnofri.HighDim.RadialGreenHeat
open RadialGreenPoisson RadialThetaTail SpatialThetaDiagonal

theorem heatPart_diagonal_eq (y : ℝ) : heatPart (fun _ : Fin 12 => y)=diagonalHeat y := by
  simp only [heatPart,sourceMellin,diagonalHeat,Finset.prod_const,Finset.card_univ,Fintype.card_fin]

theorem heatPart_diagonal_le_finite (a : ℕ → ℝ) (n : ℕ)
    (ha : Monotone a) (ha0 : a 0=1) (y : ℝ) :
    heatPart (fun _ : Fin 12 => y)≤heatFiniteUpper a n y := by
  rw [heatPart_diagonal_eq]
  exact diagonalHeat_le_finite a n ha ha0 y

/-- The actual heat contribution decreases along the positive diagonal. -/
theorem diagonalHeat_antitone : AntitoneOn diagonalHeat (Icc (0:ℝ) (1/2)) := by
  intro y hy z hz hyz
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ)≤1/120)
  apply integral_mono_ae (heat_tail_integrable (by norm_num : (0:ℝ)<1) z)
    (heat_tail_integrable (by norm_num : (0:ℝ)<1) y)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0<t := zero_lt_one.trans ht
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg ht0.le 5)
  exact sub_le_sub_right (pow_le_pow_left₀ (RadialThetaTail.theta_pos ht0 z).le
    (SpatialThetaDiagonal.theta_antitone ht0 hy hz hyz) 12) 1

/-- A single finite heat computation at zero controls the actual heat part
on the entire diagonal and hence the singular-origin estimate. -/
theorem heatPart_diagonal_le_finite_zero (a : ℕ → ℝ) (n : ℕ)
    (ha : Monotone a) (ha0 : a 0=1) {y : ℝ} (hy : y∈Icc (0:ℝ) (1/2)) :
    heatPart (fun _ : Fin 12 => y)≤heatFiniteUpper a n 0 := by
  rw [heatPart_diagonal_eq]
  exact (diagonalHeat_antitone (by constructor <;> norm_num) hy hy.1).trans
    (diagonalHeat_le_finite a n ha ha0 0)

/-- Exact real expression whose finitely many elementary terms can be
outwardly rounded by a numerical certificate. -/
def finiteRadialUpper (a : ℕ → ℝ) (n : ℕ) (S : ℝ) : ℝ :=
  (Real.pi^6/120)*RadialE1.E1 (Real.pi^2*12*(radialAngle 12 S)^2)+RadialPoissonImages.J12-
    1/720+heatFiniteUpper a n (radialAngle 12 S)

theorem radialGreen_le_finite (a : ℕ → ℝ) (n : ℕ) (ha : Monotone a) (ha0 : a 0=1)
    {S : ℝ} (hS : S∈Ioc (0:ℝ) 12) : radialGreen 12 S≤finiteRadialUpper a n S := by
  exact (radialGreen_le_E1_images_heat hS).trans
    (add_le_add (le_refl _) (heatPart_diagonal_le_finite a n ha ha0 (radialAngle 12 S)))

#print axioms heatPart_diagonal_le_finite_zero
#print axioms radialGreen_le_finite
end BecknerOnofri.HighDim.RadialGreenHeat
