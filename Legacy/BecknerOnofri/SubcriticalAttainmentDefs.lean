module

public import Legacy.BecknerOnofri.TorusSobolevCompactness
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

/-! Actual real mean-zero torus potentials, their partition function, and the
explicit rough exponential estimate needed for subcritical attainment. -/
noncomputable section
open Set Filter MeasureTheory Legacy.TorusEndpoint
open scoped BigOperators Topology ENNReal
namespace Legacy.BecknerOnofri.SubcriticalAttainment
open TorusSobolev

def RealPotential {d : ℕ} (u : TorusL2 d) : Prop :=
  ∀ᵐ x ∂torusMeasure d, (u x).im = 0

def Admissible {d : ℕ} (u : TorusL2 d) : Prop := RealPotential u ∧ CriticalSobolev u

def partition {d : ℕ} (u : TorusL2 d) : ℝ :=
  ∫ x, Real.exp ((u x).re) ∂torusMeasure d

def functional {d : ℕ} (A : ℝ) (u : TorusL2 d) : ℝ :=
  Real.log (partition u) - A * criticalEnergy u

/-- This hypothesis asserts an inequality for every actual Sobolev potential,
including integrability; it assumes neither attainment nor convergence. -/
def RoughExponentialBound (d : ℕ) (b Ab : ℝ) : Prop :=
  ∀ u : TorusL2 d, Admissible u → ∀ p : ℝ, 0 < p →
    Integrable (fun x => Real.exp (p * (u x).re)) (torusMeasure d) ∧
      Real.log (∫ x, Real.exp (p * (u x).re) ∂torusMeasure d) ≤
        p^2 * criticalEnergy u / (4*b) + Real.log Ab

def realSobolevBall (d : ℕ) (B : ℝ) : Set (TorusL2 d) :=
  sobolevBall d B ∩ {u | RealPotential u}

theorem realPotential_iff_imLp_zero {d : ℕ} (u : TorusL2 d) :
    RealPotential u ↔ Complex.imCLM.compLpL 2 (torusMeasure d) u = 0 := by
  constructor
  · intro hu
    apply Lp.ext
    filter_upwards [Complex.imCLM.coeFn_compLpL u, hu,
      (Lp.coeFn_zero ℝ 2 (torusMeasure d))] with x hx hi hz
    simpa only [Complex.imCLM_apply, hi, hz, Pi.zero_apply] using hx
  · intro hu
    have he := Complex.imCLM.coeFn_compLpL (p := 2) (μ := torusMeasure d) u
    rw [hu] at he
    filter_upwards [he, (Lp.coeFn_zero ℝ 2 (torusMeasure d))] with x hx hz
    simpa only [Complex.imCLM_apply, hz, Pi.zero_apply] using hx.symm

theorem realPotential_isClosed (d : ℕ) : IsClosed {u : TorusL2 d | RealPotential u} := by
  simp_rw [realPotential_iff_imLp_zero]
  exact isClosed_eq (Complex.imCLM.compLpL 2 (torusMeasure d)).continuous continuous_const

theorem sobolevBall_isClosed (d : ℕ) (B : ℝ) : IsClosed (sobolevBall d B) := by
  have he : sobolevBall d B = (fourierIsometry d) ⁻¹' coefficientBall d B := by
    ext u
    simp [sobolevBall, CriticalSobolev, coefficientBall, criticalEnergy, and_assoc]
  rw [he]
  exact (coefficientBall_isClosed d B).preimage (fourierIsometry d).continuous

theorem realSobolevBall_isClosed (d : ℕ) (B : ℝ) : IsClosed (realSobolevBall d B) :=
  (sobolevBall_isClosed d B).inter (realPotential_isClosed d)

theorem realSobolevBall_isCompact {d : ℕ} (hd : 0 < d) {B : ℝ} (hB : 0 ≤ B) :
    IsCompact (realSobolevBall d B) :=
  (TorusSobolev.sobolevBall_isCompact hd hB).inter_right (realPotential_isClosed d)

theorem energy_nonneg {d : ℕ} (u : TorusL2 d) : 0 ≤ criticalEnergy u :=
  tsum_nonneg (weightedSquare_nonneg (fourierIsometry d u))

theorem energy_lowerSemicontinuousOn (d : ℕ) (B : ℝ) :
    LowerSemicontinuousOn (criticalEnergy (d := d)) (realSobolevBall d B) := by
  rw [lowerSemicontinuousOn_iff_preimage_Iic]
  intro c
  refine ⟨sobolevBall d c, sobolevBall_isClosed d c, ?_⟩
  ext u
  change ((u ∈ realSobolevBall d B) ∧ criticalEnergy u ≤ c) ↔
    ((u ∈ realSobolevBall d B) ∧ CriticalSobolev u ∧ criticalEnergy u ≤ c)
  exact ⟨fun h => ⟨h.1, h.1.1.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩

@[simp] theorem realPotential_zero (d : ℕ) : RealPotential (0 : TorusL2 d) := by
  filter_upwards [Lp.coeFn_zero ℂ 2 (torusMeasure d)] with x hx
  simp

@[simp] theorem criticalSobolev_zero (d : ℕ) : CriticalSobolev (0 : TorusL2 d) := by
  constructor
  · change fourierIsometry d 0 0 = 0
    rw [(fourierIsometry d).map_zero]
    rfl
  · simp only [map_zero]
    have he : weightedSquare (0 : Coefficients (Frequency d)) = 0 := by
      funext k; simp [weightedSquare]
    rw [he]
    exact summable_zero

@[simp] theorem energy_zero (d : ℕ) : criticalEnergy (0 : TorusL2 d) = 0 := by
  simp [criticalEnergy, coefficientEnergy, weightedSquare]

@[simp] theorem admissible_zero (d : ℕ) : Admissible (0 : TorusL2 d) :=
  ⟨realPotential_zero d, criticalSobolev_zero d⟩

@[simp] theorem partition_zero (d : ℕ) : partition (0 : TorusL2 d) = 1 := by
  unfold partition
  calc
    _ = ∫ _x, (1 : ℝ) ∂torusMeasure d := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_zero ℂ 2 (torusMeasure d)] with x hx
      simp
    _ = 1 := by simp

@[simp] theorem functional_zero (d : ℕ) (A : ℝ) : functional A (0 : TorusL2 d) = 0 := by
  simp [functional]

#print axioms realPotential_isClosed
#print axioms realSobolevBall_isCompact
#print axioms energy_lowerSemicontinuousOn

end Legacy.BecknerOnofri.SubcriticalAttainment
