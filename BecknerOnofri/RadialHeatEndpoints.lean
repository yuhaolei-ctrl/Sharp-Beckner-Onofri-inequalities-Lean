module

public import BecknerOnofri.RadialGreenFinite

@[expose] public section

/-! The source's exact rational heat-time partition: ratio 1025/1024,
clipped at 64, with exactly 4261 nonempty panels. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option exponentiation.threshold 5000
set_option maxHeartbeats 4000000
open MeasureTheory Set
open scoped BigOperators
namespace BecknerOnofri.HighDim.RadialHeatEndpoints
open RadialThetaTail RadialGreenHeat SpatialThetaDiagonal

def ratio : ℝ := 1025/1024

def endpoint (i : ℕ) : ℝ := min 64 (ratio^i)

theorem ratio_gt_one : 1<ratio := by norm_num [ratio]

theorem ratio_pow_4260_lt : ratio^4260<64 := by norm_num [ratio]

theorem ratio_pow_4261_gt : 64<ratio^4261 := by norm_num [ratio]

theorem endpoint_monotone : Monotone endpoint := by
  intro i j hij
  exact min_le_min_left 64 (pow_le_pow_right₀ ratio_gt_one.le hij)

theorem endpoint_zero : endpoint 0=1 := by norm_num [endpoint]

theorem endpoint_last : endpoint 4261=64 := min_eq_left ratio_pow_4261_gt.le

theorem endpoint_mem (i : ℕ) : endpoint i∈Icc (1:ℝ) 64 :=
  ⟨by simpa only [endpoint_zero] using endpoint_monotone (Nat.zero_le i),min_le_left _ _⟩

theorem endpoint_before_last {i : ℕ} (hi : i<4261) : endpoint i=ratio^i := by
  apply min_eq_right
  exact (pow_le_pow_right₀ ratio_gt_one.le (by omega : i≤4260)).trans ratio_pow_4260_lt.le

theorem endpoint_strict_panel {i : ℕ} (hi : i<4261) : endpoint i<endpoint (i+1) := by
  rw [endpoint_before_last hi]
  apply lt_min
  · exact (pow_le_pow_right₀ ratio_gt_one.le (by omega : i≤4260)).trans_lt ratio_pow_4260_lt
  · exact pow_lt_pow_right₀ ratio_gt_one (Nat.lt_succ_self i)

/-- The exact source heat upper function, using all 4261 signed panels and
the rigorously bounded complete infinite-time remainder beyond 64. -/
def heatUpper (y : ℝ) : ℝ := heatFiniteUpper endpoint 4261 y

theorem heatUpper_eq (y : ℝ) : heatUpper y=
    (∑ i∈Finset.range 4261,((endpoint (i+1)^6-endpoint i^6)/720)*
      panelHeatUpper (endpoint i) (endpoint (i+1)) y)+heatTailUpper 64 := by
  rw [heatUpper,heatFiniteUpper,endpoint_last]

theorem diagonalHeat_le_heatUpper (y : ℝ) : diagonalHeat y≤heatUpper y :=
  diagonalHeat_le_finite endpoint 4261 endpoint_monotone endpoint_zero y

theorem heatPart_diagonal_le_heatUpper (y : ℝ) :
    RadialGreenPoisson.heatPart (fun _ : Fin 12=>y)≤heatUpper y :=
  heatPart_diagonal_le_finite endpoint 4261 endpoint_monotone endpoint_zero y

theorem heatPart_diagonal_le_heatUpper_zero {y : ℝ} (hy : y∈Icc (0:ℝ) (1/2)) :
    RadialGreenPoisson.heatPart (fun _ : Fin 12=>y)≤heatUpper 0 :=
  heatPart_diagonal_le_finite_zero endpoint 4261 endpoint_monotone endpoint_zero hy

/-- The source's fully specified radial numerical upper profile. -/
def radialUpper (S : ℝ) : ℝ := finiteRadialUpper endpoint 4261 S

theorem radialUpper_eq (S : ℝ) : radialUpper S=
    (Real.pi^6/120)*RadialE1.E1 (Real.pi^2*12*(radialAngle 12 S)^2)+RadialPoissonImages.J12-
      1/720+heatUpper (radialAngle 12 S) := rfl

theorem radialGreen_le_radialUpper {S : ℝ} (hS : S∈Ioc (0:ℝ) 12) :
    radialGreen 12 S≤radialUpper S :=
  radialGreen_le_finite endpoint 4261 endpoint_monotone endpoint_zero hS

#print axioms ratio_pow_4260_lt
#print axioms ratio_pow_4261_gt
#print axioms endpoint_last
#print axioms radialGreen_le_radialUpper
end BecknerOnofri.HighDim.RadialHeatEndpoints
