/-
Copyright (c) 2026 Yuhao Lei, Matthew Rosenzweig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuhao Lei, Matthew Rosenzweig
-/
module

public import BecknerOnofri.V2.Reaudit.Final.All
public import BecknerOnofri.V2.Reaudit.Final.ManuscriptLemmas2

/-!
# Solution: sharp Beckner–Onofri inequalities on the flat torus

The statements of `Challenge.lean`, proved from the route-aligned development of the second pass
(`BecknerOnofri.V2.Reaudit`): each theorem is a direct consequence of a declaration whose proof follows the
written route (low dimensions: `Reaudit.Mixtures`; dimension eleven: `Reaudit.Final.Section4`; `d ≥ 12`:
`Reaudit.Final.high_endpoint_printed`, the proof of `cor:section5-high-endpoint` as printed).
The vocabulary (`BecknerOnofri.HighDim.pressure`, `spectralEnergy`, …) is the library's own;
Comparator checks that it coincides with the definitions restated in `Challenge.lean`.
-/

@[expose] public section

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace BecknerOnofri

open HighDim
open scoped ComplexConjugate

/-! ## Theorem 1.1: dimensions `1 ≤ d ≤ 10`

The sharp coefficient is the concentration coefficient `A_c(d) = 1/(4 d c_d)`, and
`β_gm(d) = β_c(d) = 2d`. -/

/-- **Theorem 1.1, (eq:intro-low-dual).** For `1 ≤ d ≤ 10` and every probability density `ρ`,
`Ent(ρ) ≥ d c_d ‖ρ‖²_{Ḣ^{-d/2}}`. Since `c_d ‖ρ‖²_{Ḣ^{-d/2}} = spectralEnergy ρ / β_s(d)`,
this is `(d/β_s(d)) · spectralEnergy ρ ≤ Ent(ρ)`, with `Ent(ρ) = ∞` allowed. -/
theorem low_dim_entropy_inequality (d : ℕ) (hd : 1 ≤ d) (hd10 : d ≤ 10)
    (ρ : ProbabilityDensity d) :
    (((d : ℝ) / spectralThreshold d : ℝ) : EReal) * (spectralEnergy ρ).toEReal ≤
      extendedEntropy ρ :=
  BecknerOnofri.V2.Reaudit.Mixtures.low_dim_entropy_inequality d hd hd10 ρ

/-- **Theorem 1.1, (eq:intro-low-primal).** For `1 ≤ d ≤ 10` and every `u ∈ H^{d/2}(𝕋ᵈ)`, `e^{u-ū}`
is integrable and `log ∫ e^{u - ū} dm_d ≤ A_c(d) ‖u‖²_{Ḣ^{d/2}}`. -/
theorem low_dim_beckner_onofri (d : ℕ) (hd : 1 ≤ d) (hd10 : d ≤ 10)
    (u : Torus d → ℝ) (hu : InCriticalSobolev u) :
    Integrable (fun x => Real.exp (centered u x)) (torusMeasure d) ∧
      logPartition u ≤ ((collapseCoefficient d * potentialEnergy u : ℝ) : EReal) :=
  BecknerOnofri.V2.Reaudit.Mixtures.low_dim_beckner_onofri d hd hd10 u hu

/-- **Theorem 1.1, sharpness.** For `1 ≤ d ≤ 10`, `A_c(d)` is the least coefficient `A`
for which `log ∫ e^{u - ū} dm_d ≤ A ‖u‖²_{Ḣ^{d/2}}` holds for every `u ∈ H^{d/2}(𝕋ᵈ)`. -/
theorem low_dim_coefficient_sharp (d : ℕ) (hd : 1 ≤ d) (hd10 : d ≤ 10) :
    IsLeast {A : ℝ | ∀ u : Torus d → ℝ, InCriticalSobolev u →
      logPartition u ≤ ((A * potentialEnergy u : ℝ) : EReal)} (collapseCoefficient d) :=
  BecknerOnofri.V2.Reaudit.Mixtures.low_dim_coefficient_sharp d hd hd10

/-- **Theorem 1.1, equality for `d = 1` (potentials).** For `u ∈ H^{1/2}(𝕋)`, equality holds
in (eq:intro-low-primal) exactly for `u = -2 log |1 - ā e^{2πix}| + c` with `|a| < 1`, `c ∈ ℝ`
(the family (eq:intro-circle-extremizers)), up to a null set. -/
theorem circle_beckner_onofri_eq_iff (u : Torus 1 → ℝ) (hu : InCriticalSobolev u) :
    logPartition u = ((collapseCoefficient 1 * potentialEnergy u : ℝ) : EReal) ↔
      ∃ a : ℂ, ‖a‖ < 1 ∧ ∃ c : ℝ,
        u =ᵐ[torusMeasure 1] fun x => -2 * Real.log ‖1 - conj a * fourier 1 (x 0)‖ + c :=
  BecknerOnofri.V2.Reaudit.Mixtures.circle_beckner_onofri_eq_iff u hu

/-- **Theorem 1.1, equality for `d = 1` (densities).** For a finite-entropy density on the
circle, equality holds in (eq:intro-low-dual) exactly for the Poisson kernels
`ρ_a(x) = (1 - |a|²)/|e^{2πix} - a|²` with `|a| < 1` (the family (eq:intro-circle-poisson)). -/
theorem circle_entropy_eq_iff (ρ : ProbabilityDensity 1) (hρ : ρ.FiniteEntropy) :
    (((1 : ℝ) / spectralThreshold 1 : ℝ) : EReal) * (spectralEnergy ρ).toEReal =
        (entropy ρ : EReal) ↔
      ∃ a : ℂ, ‖a‖ < 1 ∧
        ρ.value =ᵐ[torusMeasure 1] fun x => (1 - ‖a‖ ^ 2) / ‖fourier 1 (x 0) - a‖ ^ 2 :=
  BecknerOnofri.V2.Reaudit.Mixtures.circle_entropy_eq_iff ρ hρ

/-- **Theorem 1.1, equality for `2 ≤ d ≤ 10` (densities).** For a finite-entropy density,
equality holds in (eq:intro-low-dual) only for `ρ ≡ 1`. -/
theorem low_dim_entropy_eq_iff (d : ℕ) (hd : 2 ≤ d) (hd10 : d ≤ 10)
    (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy) :
    (((d : ℝ) / spectralThreshold d : ℝ) : EReal) * (spectralEnergy ρ).toEReal =
        (entropy ρ : EReal) ↔
      ρ.value =ᵐ[torusMeasure d] fun _ => 1 :=
  BecknerOnofri.V2.Reaudit.Mixtures.low_dim_entropy_eq_iff d hd hd10 ρ hρ

/-- **Theorem 1.1, equality for `2 ≤ d ≤ 10` (potentials).** Equality holds in (eq:intro-low-primal)
only for constant `u`. -/
theorem low_dim_beckner_onofri_eq_iff (d : ℕ) (hd : 2 ≤ d) (hd10 : d ≤ 10)
    (u : Torus d → ℝ) (hu : InCriticalSobolev u) :
    logPartition u = ((collapseCoefficient d * potentialEnergy u : ℝ) : EReal) ↔
      ∃ c : ℝ, u =ᵐ[torusMeasure d] fun _ => c :=
  BecknerOnofri.V2.Reaudit.Mixtures.low_dim_beckner_onofri_eq_iff d hd hd10 u hu

/-- **(eq:intro-low-coefficient-consequence).** For `1 ≤ d ≤ 10` the pressure vanishes up to `β_c(d)
= 2d` and is infinite beyond it. -/
theorem low_dim_pressure_eq (d : ℕ) (hd : 1 ≤ d) (hd10 : d ≤ 10) (β : ℝ) :
    pressure d β = if β ≤ 2 * (d : ℝ) then 0 else ⊤ :=
  BecknerOnofri.V2.Reaudit.Mixtures.low_dim_pressure_eq d hd hd10 β

/-- **(eq:intro-low-coefficient-consequence).** For `1 ≤ d ≤ 10` the defect vanishes for `A ≥
A_c(d)` and is infinite for `A < A_c(d)`; in particular `C_d(A_c(d)) = 0`. -/
theorem low_dim_defect_eq (d : ℕ) (hd : 1 ≤ d) (hd10 : d ≤ 10) (A : ℝ) :
    coefficientDefect d A = if collapseCoefficient d ≤ A then 0 else ⊤ :=
  BecknerOnofri.V2.Reaudit.Mixtures.low_dim_defect_eq d hd hd10 A

/-- **(eq:intro-low-coefficient-consequence).** For `1 ≤ d ≤ 10`, `β_gm(d) = β_c(d) = 2d`. -/
theorem low_dim_globalTransition (d : ℕ) (hd : 1 ≤ d) (hd10 : d ≤ 10) :
    VariationalCurves.globalTransition d = 2 * (d : ℝ) :=
  BecknerOnofri.V2.Reaudit.Mixtures.low_dim_globalTransition d hd hd10

/-! ## Theorem 1.2: dimension eleven

A first-order transition strictly before spectral instability. -/

/-- **Theorem 1.2, (eq:intro-rho-star).** The normalizing constant of the Euclidean profile,
`C₁₁ = Γ(11)/(π^{11/2} Γ(11/2))`, equals the constant `122880/π⁶` used in
`Eleven.euclideanProfile`. -/
theorem eleven_profile_constant :
    Real.Gamma 11 / (Real.pi ^ ((11 : ℝ) / 2) * Real.Gamma (11 / 2)) = 122880 / Real.pi ^ 6 :=
  BecknerOnofri.V2.Final.eleven_profile_constant

/-- **Theorem 1.2, (eq:intro-d11-certificate).** The periodized profile
`ρ_*(x) = Σ_{n ∈ ℤ¹¹} 5¹¹ C₁₁ (1 + 25|x + n|²)^{-11}` is a smooth, strictly positive probability
density with `Ent(ρ_*) < 14.4088` and `(2π)¹¹/2 · ‖ρ_*‖²_{Ḣ^{-11/2}} > 14.4753`; here
`(2π)¹¹ ‖ρ_*‖²_{Ḣ^{-11/2}} = spectralEnergy ρ_*`. -/
theorem eleven_competitor :
    ∃ ρ : ProbabilityDensity 11, ρ.value = Eleven.periodizedProfile ∧
      SmoothOnTorus ρ.value ∧ (∀ x, 0 < ρ.value x) ∧ ρ.FiniteEntropy ∧
      entropy ρ < (144088 : ℝ) / 10000 ∧
      ENNReal.ofReal (2 * ((144753 : ℝ) / 10000)) < spectralEnergy ρ :=
  BecknerOnofri.V2.Reaudit.Final.eleven_competitor_route

/-- **Theorem 1.2, (eq:intro-d11-threshold).** `C_11(A_s(11)) = P_11(β_s(11)) > 1/30`. -/
theorem eleven_spectral_pressure :
    coefficientDefect 11 (spectralCoefficient 11) = pressure 11 (spectralThreshold 11) ∧
      (1 / 30 : EReal) < pressure 11 (spectralThreshold 11) :=
  BecknerOnofri.V2.Reaudit.Final.eleven_spectral_pressure_route

/-- **Theorem 1.2, (eq:intro-d11-threshold).** `17.715 < β_gm(11) < 20.630 < β_s(11) < 22`. -/
theorem eleven_globalTransition_bounds :
    (3543 : ℝ) / 200 < VariationalCurves.globalTransition 11 ∧
      VariationalCurves.globalTransition 11 < 2063 / 100 ∧
      (2063 : ℝ) / 100 < spectralThreshold 11 ∧ spectralThreshold 11 < 22 :=
  BecknerOnofri.V2.Reaudit.Final.eleven_globalTransition_bounds_route

/-- **Theorem 1.2, coexistence.** At `β = β_gm(11)`, both the uniform density and a
nonuniform smooth strictly positive density are global minimizers of `𝓔_β`. -/
theorem eleven_coexistence :
    IsGlobalMinimizer (VariationalCurves.globalTransition 11) (uniformDensity 11) ∧
      ∃ ρ : ProbabilityDensity 11,
        IsGlobalMinimizer (VariationalCurves.globalTransition 11) ρ ∧
        SmoothOnTorus ρ.value ∧ (∀ x, 0 < ρ.value x) ∧
        ¬ (ρ.value =ᵐ[torusMeasure 11] fun _ => 1) :=
  BecknerOnofri.V2.Reaudit.Final.eleven_coexistence_route

/-- **Theorem 1.2, local stability.** At `β = β_gm(11)` the Hessian of the free energy at
the uniform density is strictly positive: with `θ = 1 - β_gm(11)/β_s(11) > 0`,
`d²/dt² 𝓔_β(1 + t h)|_{t=0} ≥ θ ∫ h²` for every smooth mean-zero `h`. -/
theorem eleven_uniform_hessian_pos :
    0 < 1 - VariationalCurves.globalTransition 11 / spectralThreshold 11 ∧
      ∀ h : Torus 11 → ℝ, SmoothOnTorus h → MeanZero h →
        (1 - VariationalCurves.globalTransition 11 / spectralThreshold 11) *
            (∫ x, h x ^ 2 ∂torusMeasure 11) ≤
          Eleven.uniformHessian (VariationalCurves.globalTransition 11) h :=
  BecknerOnofri.V2.Reaudit.Final.eleven_uniform_hessian_pos_route

/-- **Theorem 1.2, pressure corner.** `P_11` is finite on `(0, 22)` and is not
differentiable at `β_gm(11)`. -/
theorem eleven_pressure_corner :
    (∀ β : ℝ, 0 < β → β < 22 → pressure 11 β = ((pressure 11 β).toReal : EReal)) ∧
      ¬ DifferentiableAt ℝ (fun β => (pressure 11 β).toReal)
        (VariationalCurves.globalTransition 11) :=
  BecknerOnofri.V2.Reaudit.Final.eleven_pressure_corner_route

/-- **Theorem 1.2, first-order transition.** The one-sided derivatives of `P_11` at
`β_gm(11)` are `P'_-(β_gm) = 0 < P'_+(β_gm)`. -/
theorem eleven_pressure_derivative_jump :
    ∃ p : ℝ, 0 < p ∧
      HasDerivWithinAt (fun β => (pressure 11 β).toReal) 0
        (Set.Iio (VariationalCurves.globalTransition 11))
        (VariationalCurves.globalTransition 11) ∧
      HasDerivWithinAt (fun β => (pressure 11 β).toReal) p
        (Set.Ioi (VariationalCurves.globalTransition 11))
        (VariationalCurves.globalTransition 11) :=
  BecknerOnofri.V2.Reaudit.Final.eleven_pressure_derivative_jump_route

/-- **Theorem 1.2, defect corner.** `C_11` is finite near `A_gm(11)` and is not
differentiable there. -/
theorem eleven_defect_corner :
    (∃ ε : ℝ, 0 < ε ∧ ε < VariationalCurves.zeroDefectCoefficient 11 ∧
      ∀ A : ℝ, |A - VariationalCurves.zeroDefectCoefficient 11| < ε →
        coefficientDefect 11 A = ((coefficientDefect 11 A).toReal : EReal)) ∧
      ¬ DifferentiableAt ℝ (fun A => (coefficientDefect 11 A).toReal)
        (VariationalCurves.zeroDefectCoefficient 11) :=
  BecknerOnofri.V2.Reaudit.Final.eleven_defect_corner_route

/-! ## Theorem 1.3: dimensions `d ≥ 12`

The sharp coefficient is the first-shell coefficient `A_s(d) = 1/(2(2π)^d)`,
`β_gm(d) = β_s(d)`, and the pressure detaches quadratically above `β_s(d)`. -/

/-- **Theorem 1.3, (eq:intro-high-dual).** For `d ≥ 12` and every probability density `ρ`,
`Ent(ρ) ≥ (2π)^d/2 · ‖ρ‖²_{Ḣ^{-d/2}} = spectralEnergy ρ / 2`, with `Ent(ρ) = ∞` allowed. -/
theorem high_dim_entropy_inequality (d : ℕ) (hd : 12 ≤ d) (ρ : ProbabilityDensity d) :
    ((1 / 2 : ℝ) : EReal) * (spectralEnergy ρ).toEReal ≤ extendedEntropy ρ :=
  BecknerOnofri.V2.Reaudit.Final.high_dim_entropy_inequality_printed d hd ρ

/-- **Theorem 1.3, equality in (eq:intro-high-dual).** For `d ≥ 12` and a finite-entropy density,
`spectralEnergy ρ = 2 Ent(ρ)` if and only if `ρ ≡ 1`. -/
theorem high_dim_entropy_eq_iff (d : ℕ) (hd : 12 ≤ d)
    (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy) :
    spectralEnergy ρ = ENNReal.ofReal (2 * entropy ρ) ↔
      ρ.value =ᵐ[torusMeasure d] fun _ => 1 :=
  ((BecknerOnofri.V2.Reaudit.Final.high_endpoint_printed d hd).1 ρ hρ).2

/-- **Theorem 1.3, (eq:intro-high-primal).** For `d ≥ 12` and every `u ∈ H^{d/2}(𝕋ᵈ)`, `e^{u-ū}` is
integrable and `log ∫ e^{u - ū} dm_d ≤ A_s(d) ‖u‖²_{Ḣ^{d/2}}`. -/
theorem high_dim_beckner_onofri (d : ℕ) (hd : 12 ≤ d)
    (u : Torus d → ℝ) (hu : InCriticalSobolev u) :
    Integrable (fun x => Real.exp (centered u x)) (torusMeasure d) ∧
      logPartition u ≤ ((spectralCoefficient d * potentialEnergy u : ℝ) : EReal) :=
  ⟨((BecknerOnofri.V2.Reaudit.Final.high_endpoint_printed d hd).2.1 u hu).1,
    ((BecknerOnofri.V2.Reaudit.Final.high_endpoint_printed d hd).2.1 u hu).2.1⟩

/-- **Theorem 1.3, equality in (eq:intro-high-primal).** Equality holds only for constant `u`. -/
theorem high_dim_beckner_onofri_eq_iff (d : ℕ) (hd : 12 ≤ d)
    (u : Torus d → ℝ) (hu : InCriticalSobolev u) :
    logPartition u = ((spectralCoefficient d * potentialEnergy u : ℝ) : EReal) ↔
      ∃ c : ℝ, u =ᵐ[torusMeasure d] fun _ => c :=
  ((BecknerOnofri.V2.Reaudit.Final.high_endpoint_printed d hd).2.1 u hu).2.2

/-- **Theorem 1.3, (eq:intro-high-threshold).** For `d ≥ 12`, `β_s(d)` is the largest coupling with
zero pressure, `A_s(d)` is the least coefficient with zero defect, and therefore `β_gm(d) = β_s(d)`
and `A_gm(d) = A_s(d)`. -/
theorem high_dim_thresholds (d : ℕ) (hd : 12 ≤ d) :
    IsGreatest {β : ℝ | 0 ≤ β ∧ pressure d β = 0} (spectralThreshold d) ∧
      IsLeast {A : ℝ | 0 < A ∧ coefficientDefect d A = 0} (spectralCoefficient d) ∧
      VariationalCurves.globalTransition d = spectralThreshold d ∧
      VariationalCurves.zeroDefectCoefficient d = spectralCoefficient d :=
  BecknerOnofri.V2.Reaudit.Final.high_dim_thresholds_printed d hd

/-- **(eq:intro-kappa).** `κ_d = -(2a_d + (d - 1) b_d) > 0` for every `d ≥ 12`. -/
theorem kappa_pos (d : ℕ) (hd : 12 ≤ d) : 0 < kappa d :=
  BecknerOnofri.V2.Final.kappa_pos d hd

/-- **Theorem 1.3, (eq:intro-onset-range)–(eq:intro-onset-branch).** There is `ε_d > 0` and a family
`U_β` such that for `β_s(d) < β < β_s(d) + ε_d`: `U_β` is a smooth stationary potential with all `d`
coordinate first-shell modes active, lying on a Morse–Bott maximum orbit of the potential
functional; global minimizers of `𝓔_β` exist; and the global minimizers are exactly the Gibbs
densities `e^{U_β(· - x₀)}/∫ e^{U_β}` of the translates. Moreover, for each fixed `s ≥ 0`, `U_β(· -
x₀) = 2√(δ/κ_d) Σ_j cos(2π(x_j - x₀_j)) + O_{H^s}(δ)` uniformly in `x₀`, where `δ = 1 - β_s(d)/β`.
-/
theorem high_dim_onset_branch (d : ℕ) (hd : 12 ≤ d) : FullBranchOnset d :=
  BecknerOnofri.V2.Reaudit.Final.Onset.high_dim_onset_branch_route d hd

/-- **Theorem 1.3, (eq:intro-pressure-onset).** `P_d(β) = (d/(2κ_d)) (1 - β_s(d)/β)² + O((β -
β_s(d))³)` as `β ↓ β_s(d)`, with the pressure finite there. -/
theorem high_dim_pressure_onset (d : ℕ) (hd : 12 ≤ d) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 ≤ C ∧
      ∀ β : ℝ, spectralThreshold d < β → β < spectralThreshold d + ε →
        ∃ p : ℝ, pressure d β = (p : EReal) ∧
          |p - (d : ℝ) / (2 * kappa d) * (1 - spectralThreshold d / β) ^ 2| ≤
            C * (β - spectralThreshold d) ^ 3 :=
  BecknerOnofri.V2.Reaudit.Final.Onset.high_dim_pressure_onset_route d hd

/-- **Theorem 1.3, (eq:intro-C-onset).** `C_d(A) = (d/(2κ_d)) (1 - A/A_s(d))² + O((1 - A/A_s(d))³)`
as `A ↑ A_s(d)`, with the defect finite there. -/
theorem high_dim_defect_onset (d : ℕ) (hd : 12 ≤ d) :
    ∃ ε C : ℝ, 0 < ε ∧ ε < spectralCoefficient d ∧ 0 ≤ C ∧
      ∀ A : ℝ, spectralCoefficient d - ε < A → A < spectralCoefficient d →
        ∃ c : ℝ, coefficientDefect d A = (c : EReal) ∧
          |c - (d : ℝ) / (2 * kappa d) * (1 - A / spectralCoefficient d) ^ 2| ≤
            C * (1 - A / spectralCoefficient d) ^ 3 :=
  BecknerOnofri.V2.Reaudit.Final.Onset.high_dim_defect_onset_route d hd

end BecknerOnofri
