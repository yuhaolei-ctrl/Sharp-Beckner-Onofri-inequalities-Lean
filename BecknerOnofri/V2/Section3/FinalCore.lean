module

public import BecknerOnofri.V2.Section3.Lemma31
public import BecknerOnofri.V2.Section3.CircleCase
public import BecknerOnofri.VariationalExtendedConvexity
public import BecknerOnofri.V2.Reaudit.Obstruction.ConcentrationObstruction

@[expose] public section

/-! # Consequences of the full entropy bound (G04)

Route-independent consequences used by both `Final.lean` (legacy-discharge route) and
`FinalWritten.lean` (written route): the converse directions of the equality cases, the extended
entropy bound on all of `𝒫_ac`, minimality of `A_c(d)`, the pressure formula and `β_gm(d) = 2d`, each
from the single hypothesis `hfull : ∀ σ, σ.FiniteEntropy → EntropyBound d σ`. -/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology ComplexConjugate

namespace BecknerOnofri.V2.Section3
open BecknerOnofri.HighDim BecknerOnofri.V2.Vocab

variable {d : ℕ}
/-! ## The converse directions of the equality cases -/

theorem negSobolevEnergy_uniform (d : ℕ) : negSobolevEnergy (uniformDensity d).value = 0 := by
  unfold negSobolevEnergy
  refine ENNReal.tsum_eq_zero.mpr fun k => ?_
  have : fourierCoeff (uniformDensity d).value k.val = 0 := uniformDensity_fourierCoeff_nonzero _ k.property
  simp [this]

theorem torusEntropy_uniform (d : ℕ) : torusEntropy (uniformDensity d).value = 0 := by
  rw [torusEntropy_density_eq_ofReal_entropy _ (uniformDensity_finiteEntropy d),
    uniformDensity_entropy]
  simp

/-- A density that is a.e. `1` has equality in the entropy bound (both sides vanish). -/
theorem entropyEquality_of_uniform (ρ : ProbabilityDensity d)
    (h : ρ.value =ᵐ[torusMeasure d] fun _ => 1) : EntropyEquality d ρ := by
  have hu : ρ.value =ᵐ[torusMeasure d] (uniformDensity d).value := h
  unfold EntropyEquality
  rw [negSobolevEnergy_congr_ae hu, torusEntropy_congr_ae hu, negSobolevEnergy_uniform,
    torusEntropy_uniform]
  simp

/-- A critical Sobolev function that is a.e. constant has equality in the potential inequality. -/
theorem potential_equality_of_const (hd : 0 < d) (u : Torus d → ℝ) (hu : InCriticalSobolev u)
    (c : ℝ) (h : u =ᵐ[torusMeasure d] fun _ => c) :
    logPartition u = ((collapseCoefficient d * potentialEnergy u : ℝ) : EReal) := by
  have hf : ∀ k : NonzeroFrequency d, fourierCoeff u k.val = 0 := fun k => by
    rw [congrFun (BecknerOnofri.V2.Rearrangement.fourierCoeff_congr_ae' h) k.val]
    exact fourierCoeff_const_nonzero c k.property
  have hE : potentialEnergy u = 0 := by
    simp [potentialEnergy, potentialTerm, hf]
  have hmean : (∫ y, u y ∂torusMeasure d) = c := by
    rw [integral_congr_ae h]; simp
  have hcen : centered u =ᵐ[torusMeasure d] fun _ => (0 : ℝ) := by
    filter_upwards [h] with x hx
    simp [centered, hx, hmean]
  have hZ : (∫ x, Real.exp (centered u x) ∂torusMeasure d) = 1 := by
    rw [integral_congr_ae (by filter_upwards [hcen] with x hx; rw [hx])]
    simp
  rw [logPartition_eq_log_integral hd u hu, hZ, hE]
  simp

/-! ## Theorem 1.1 -/

/-- The entropy bound `eq:intro-low-dual`, on the whole of `𝒫_ac` (extended values: both sides in
`[0,∞]`; the right side is `⊤` for infinite entropy). -/
def ExtendedBound (d : ℕ) (ρ : ProbabilityDensity d) : Prop :=
  ENNReal.ofReal ((d : ℝ) * kernelConstant d) * negSobolevEnergy ρ.value ≤ torusEntropy ρ.value

theorem extendedBound_of_full (hd : 0 < d)
    (hfull : ∀ σ : ProbabilityDensity d, σ.FiniteEntropy → EntropyBound d σ)
    (ρ : ProbabilityDensity d) : ExtendedBound d ρ := by
  by_cases hρ : ρ.FiniteEntropy
  · have hN : negSobolevEnergy ρ.value ≠ ∞ :=
      (negSobolevEnergy_ne_top_iff ρ).2 (finiteEntropy_spectralEnergy_ne_top hd ρ hρ)
    have hc := kernelConstant_pos hd
    have hd' : (0 : ℝ) < d := by exact_mod_cast hd
    have hb := hfull ρ hρ
    unfold EntropyBound at hb
    unfold ExtendedBound
    rw [← ENNReal.ofReal_toReal hN, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_toReal ((torusEntropy_density_ne_top_iff ρ).2 hρ)]
    exact ENNReal.ofReal_le_ofReal hb
  · rw [ExtendedBound, torusEntropy_density_eq_top ρ hρ]
    exact le_top

/-- The coefficient `A_c(d)` is the least admissible coefficient (sharpness by concentration,
Lemma 2.3). -/
theorem collapse_isLeast (hd : 0 < d)
    (hfull : ∀ σ : ProbabilityDensity d, σ.FiniteEntropy → EntropyBound d σ) :
    IsLeast {A : ℝ | ∀ u : Torus d → ℝ, InCriticalSobolev u →
      logPartition u ≤ ((A * potentialEnergy u : ℝ) : EReal)} (collapseCoefficient d) := by
  refine ⟨fun u hu => (potential_bound_of_full hd hfull u hu).2, fun A hA => ?_⟩
  by_contra hlt
  have hlt := not_le.mp hlt
  have htop := Reaudit.Obstruction.coefficientDefect_eq_top_of_lt_critical hd hlt
  have hle : coefficientDefect d A ≤ 0 := by
    unfold coefficientDefect
    refine iSup₂_le fun u hu => ?_
    have h := hA u hu
    rw [logPartition_eq_log_integral hd u hu] at h ⊢
    rw [← EReal.coe_sub, ← EReal.coe_zero, EReal.coe_le_coe_iff]
    have h' := EReal.coe_le_coe_iff.mp h
    linarith
  rw [htop] at hle
  exact absurd hle (by simp)

/-- The pressure on the whole line: `P_d(β) = 0` for `β ≤ 2d` and `+∞` above. -/
theorem pressure_formula (hd : 0 < d)
    (hfull : ∀ σ : ProbabilityDensity d, σ.FiniteEntropy → EntropyBound d σ) (β : ℝ) :
    pressure d β = if β ≤ 2 * (d : ℝ) then 0 else ⊤ := by
  split_ifs with h
  · exact le_antisymm
      ((VariationalCurves.pressure_monotone hd h).trans
        (pressure_two_d_eq_zero_of_full hd hfull).le) (pressure_nonneg d β)
  · exact Reaudit.Obstruction.pressure_eq_top_of_critical_lt hd (not_le.mp h)

/-- `β_gm(d) = 2d` (`= β_c(d)`). -/
theorem globalTransition_eq (hd : 0 < d)
    (hfull : ∀ σ : ProbabilityDensity d, σ.FiniteEntropy → EntropyBound d σ) :
    VariationalCurves.globalTransition d = 2 * (d : ℝ) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  refine IsGreatest.csSup_eq ⟨⟨by positivity, pressure_two_d_eq_zero_of_full hd hfull⟩, ?_⟩
  rintro β ⟨-, hβ⟩
  by_contra hlt
  rw [Reaudit.Obstruction.pressure_eq_top_of_critical_lt hd (not_le.mp hlt)] at hβ
  exact EReal.top_ne_zero hβ
end BecknerOnofri.V2.Section3
