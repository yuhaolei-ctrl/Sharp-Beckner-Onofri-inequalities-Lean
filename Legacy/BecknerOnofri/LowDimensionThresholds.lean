module

public import Legacy.BecknerOnofri.LowDimensionOnofri

@[expose] public section

/-! Exact zero-defect regions in the manuscript's coefficient and pressure
variables. Extended nonnegative suprema include arbitrarily large defects;
the zero test is precisely the corresponding inequality for every input. -/
noncomputable section
open MeasureTheory Legacy.TorusEndpoint
open scoped ENNReal
namespace Legacy.BecknerOnofri.LowDimensionThresholds
open TorusSobolev SubcriticalAttainment EndpointPotential

/-- The sharp additive defect for the actual centered Sobolev potential
problem, represented as an extended nonnegative number. -/
def coefficientDefect (d : ℕ) (A : ℝ) : ℝ≥0∞ :=
  ⨆ u : TorusL2 d, ⨆ (_ : RealPotential u),
    ⨆ (_ : Summable (weightedSquare (fourierIsometry d u))),
      ENNReal.ofReal (Real.log (centeredPartition u) - A*manuscriptEnergy u)

/-- Attractive macroscopic pressure over actual finite-entropy densities. -/
def pressure (d : ℕ) (β : ℝ) : ℝ≥0∞ :=
  ⨆ r : ProbabilityDensity d, ⨆ (_ : r.FiniteEntropy),
    ENNReal.ofReal ((β/2)*densitySpectralEnergy r - densityEntropy r.value)

theorem coefficientDefect_zero_iff_bound (d : ℕ) (A : ℝ) :
    coefficientDefect d A = 0 ↔ ∀ u : TorusL2 d, RealPotential u →
      Summable (weightedSquare (fourierIsometry d u)) →
      Real.log (centeredPartition u) ≤ A*manuscriptEnergy u := by
  simp only [coefficientDefect, ENNReal.iSup_eq_zero, ENNReal.ofReal_eq_zero, sub_nonpos]

theorem pressure_zero_iff_bound (d : ℕ) (β : ℝ) :
    pressure d β = 0 ↔ ∀ r : ProbabilityDensity d, r.FiniteEntropy →
      (β/2)*densitySpectralEnergy r ≤ densityEntropy r.value := by
  simp only [pressure, ENNReal.iSup_eq_zero, ENNReal.ofReal_eq_zero, sub_nonpos]

theorem manuscriptEnergy_nonnegative {d : ℕ} (u : TorusL2 d) : 0 ≤ manuscriptEnergy u := by
  apply tsum_nonneg
  intro k
  exact mul_nonneg (pow_nonneg (mul_nonneg (by positivity) (frequencyRadius_nonneg _)) _) (sq_nonneg _)

theorem coefficientDefect_zero_iff {d : ℕ} (hd : 1 ≤ d) (hd10 : d ≤ 10) (A : ℝ) :
    coefficientDefect d A = 0 ↔ 1/(4*(d:ℝ)*endpointSymbolConstant d) ≤ A := by
  rw [coefficientDefect_zero_iff_bound]
  constructor
  · exact fun h => (onofri_physical_coefficient_isLeast hd hd10).2 h
  · intro hA u hr hs
    exact (onofri_through_ten hd hd10 hr hs).2.trans
      (mul_le_mul_of_nonneg_right hA (manuscriptEnergy_nonnegative u))

theorem pressure_zero_iff {d : ℕ} (hd : 1 ≤ d) (hd10 : d ≤ 10) (β : ℝ) :
    pressure d β = 0 ↔ β ≤ 2*(d:ℝ) := by
  have hσ := endpointSigma_pos (by omega : 0 < d)
  rw [pressure_zero_iff_bound]
  constructor
  · intro h
    have hC := coefficient_le_endpointConstant (by omega : 0 < d) (β/(2*endpointSigma d)) (by
      intro r hr
      have hh := h r hr
      rw [normalized_energy] at hh
      convert hh using 1
      ring)
    change β/(2*endpointSigma d) ≤ (d:ℝ)/endpointSigma d at hC
    have hh := (div_le_div_iff₀ (by positivity : 0 < 2*endpointSigma d) hσ).mp hC
    have hm : β*endpointSigma d ≤ (2*(d:ℝ))*endpointSigma d := by
      nlinarith only [hh]
    exact (mul_le_mul_iff_left₀ hσ).mp hm
  · intro hβ r hr
    have hG : 0 ≤ densitySpectralEnergy r := by
      rw [normalized_energy]
      exact div_nonneg (SteinerEndpointReduction.energy_nonneg r) hσ.le
    have hb : β/2 ≤ (d:ℝ) := by linarith
    exact (mul_le_mul_of_nonneg_right hb hG).trans (normalized_entropy_endpoint hd hd10 r hr)

theorem coefficientDefect_at_collapse {d : ℕ} (hd : 1 ≤ d) (hd10 : d ≤ 10) :
    coefficientDefect d (1/(4*(d:ℝ)*endpointSymbolConstant d)) = 0 :=
  (coefficientDefect_zero_iff hd hd10 _).mpr le_rfl

theorem pressure_at_collapse {d : ℕ} (hd : 1 ≤ d) (hd10 : d ≤ 10) :
    pressure d (2*(d:ℝ)) = 0 := (pressure_zero_iff hd hd10 _).mpr le_rfl

theorem collapse_isGreatest_zeroPressure {d : ℕ} (hd : 1 ≤ d) (hd10 : d ≤ 10) :
    IsGreatest {β : ℝ | pressure d β = 0} (2*(d:ℝ)) :=
  ⟨pressure_at_collapse hd hd10, fun _ h => (pressure_zero_iff hd hd10 _).mp h⟩

#print axioms coefficientDefect_zero_iff
#print axioms pressure_zero_iff
#print axioms collapse_isGreatest_zeroPressure
end Legacy.BecknerOnofri.LowDimensionThresholds
