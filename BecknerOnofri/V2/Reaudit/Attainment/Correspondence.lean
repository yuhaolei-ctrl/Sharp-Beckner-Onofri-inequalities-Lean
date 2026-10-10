module

public import BecknerOnofri.V2.Reaudit.Attainment.DirectMethod
public import BecknerOnofri.V2.Reaudit.Attainment.Fourier
public import BecknerOnofri.V2.Reaudit.Attainment.GapIdentities
public import BecknerOnofri.V2.Vocab.Section2Gibbs
public import BecknerOnofri.V2.Vocab.Section2Bridge
public import BecknerOnofri.OptimizerDuality

@[expose] public section

/-! # The extremizer correspondence (`cor:section2-extremizer-correspondence` (i), (ii); row S009)

Printed proof: "By Proposition `prop:section2-coefficient-pressure-duality`, the two suprema
coincide. The gap identity `eq:section2-primal-gap-identity` gives (i): its Sobolev remainder
vanishes if and only if `u = u_{ρ_u}`, since both potentials have mean zero. Similarly,
`eq:section2-dual-gap-identity` gives (ii), since `H_r(ρ | ρ_{u_ρ}) = 0` if and only if
`ρ = ρ_{u_ρ}`."

This file follows that argument.  The two gap identities are no longer taken from the repository's
`primal_gap_manuscript`/`dual_gap_manuscript`: `coefficientValue_gap` and `densityValue_gap` below are
proved in `GapIdentities.lean` by the printed argument (Fourier square completion with the pairing
identification of `Pairing.lean`, the Gibbs entropy formula, and the relative entropy formula).
Reused declarations: `coefficient_pressure_duality` (the printed duality),
`pressureValue_eq_manuscript`/`densityValue_eq_manuscript` (translation of the repository's free
energy into the printed normalization).  New: the two vanishing statements (Fourier uniqueness,
`Fourier.lean`; the equality case of relative entropy via Mathlib's `klDiv_eq_zero_iff`) and the
bookkeeping that converts between suprema in
`EReal` and attained maxima. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped Topology ENNReal

namespace BecknerOnofri.V2.Reaudit.Attainment
open BecknerOnofri.HighDim BecknerOnofri.V2.Vocab

variable {d : ℕ}

/-! ## Attained maxima of `C_d(A)` -/

/-- `u` attains the supremum defining `C_d(A)`: a mean-zero `u ∈ H^{d/2}` whose value is at least the
value of every `v ∈ H^{d/2}`.  (`coefficientValue` is the real number `log ∫ e^{u-ū} - A ‖u‖²`.) -/
def IsCoefficientMaximizer (d : ℕ) (A : ℝ) (u : Torus d → ℝ) : Prop :=
  InCriticalSobolev u ∧ MeanZero u ∧
    ∀ v : Torus d → ℝ, InCriticalSobolev v → coefficientValue A v ≤ coefficientValue A u

/-- The repository's `coefficientDefect d A` (an extended-real supremum) is the supremum of
`coefficientValue A` over `H^{d/2}`. -/
theorem coefficientDefect_eq_iSup (hd : 0 < d) (A : ℝ) :
    coefficientDefect d A =
      ⨆ v : Torus d → ℝ, ⨆ (_ : InCriticalSobolev v), ((coefficientValue A v : ℝ) : EReal) := by
  unfold coefficientDefect
  refine iSup_congr fun v => iSup_congr fun hv => ?_
  exact logPartition_sub_eq_coefficientValue hd A hv

/-- Attainment in terms of the extended-real supremum: `u` is a maximizer exactly when
`C_d(A) = value(u)`. -/
theorem isCoefficientMaximizer_iff (hd : 0 < d) (A : ℝ) (u : Torus d → ℝ) :
    IsCoefficientMaximizer d A u ↔
      InCriticalSobolev u ∧ MeanZero u ∧
        coefficientDefect d A = ((coefficientValue A u : ℝ) : EReal) := by
  rw [coefficientDefect_eq_iSup hd]
  unfold IsCoefficientMaximizer
  refine and_congr_right fun hu => and_congr_right fun hm => ?_
  constructor
  · intro h
    refine le_antisymm (iSup₂_le fun v hv => EReal.coe_le_coe_iff.mpr (h v hv)) ?_
    exact le_iSup₂_of_le u hu le_rfl
  · intro h v hv
    have : ((coefficientValue A v : ℝ) : EReal) ≤ ((coefficientValue A u : ℝ) : EReal) :=
      h ▸ le_iSup₂_of_le v hv le_rfl
    exact EReal.coe_le_coe_iff.mp this

/-! ## Relative entropy: the equality case -/

theorem densityMeasure_eq_iff (ρ σ : ProbabilityDensity d) :
    densityMeasure ρ = densityMeasure σ ↔ ρ.value =ᵐ[torusMeasure d] σ.value := by
  unfold densityMeasure
  rw [withDensity_eq_iff_of_sigmaFinite ρ.integrable.aemeasurable.ennreal_ofReal
    σ.integrable.aemeasurable.ennreal_ofReal]
  constructor
  · intro h
    filter_upwards [h, ρ.nonneg, σ.nonneg] with x hx h1 h2
    have := congrArg ENNReal.toReal hx
    rwa [ENNReal.toReal_ofReal h1, ENNReal.toReal_ofReal h2] at this
  · intro h
    filter_upwards [h] with x hx
    rw [hx]

/-- `H_r(ρ | σ) = 0` if and only if `ρ = σ` almost everywhere. -/
theorem measureEntropy_density_eq_zero_iff (ρ σ : ProbabilityDensity d) :
    measureEntropy (densityMeasure ρ) (densityMeasure σ) = 0 ↔
      ρ.value =ᵐ[torusMeasure d] σ.value := by
  rw [measureEntropy_eq_klDiv, InformationTheory.klDiv_eq_zero_iff, densityMeasure_eq_iff]

/-! ## Real-valued form of the pressure integrand -/

/-- For a finite-entropy density the extended-real pressure integrand is the real number
`Gap.densityValue β ρ = β c_d/2 ‖ρ‖²_{Ḣ^{-d/2}} - Ent ρ`. -/
theorem pressureValue_eq_densityValue (hd : 0 < d) (β : ℝ) (ρ : ProbabilityDensity d)
    (hρ : ρ.FiniteEntropy) : pressureValue β ρ = ((Gap.densityValue β ρ.value : ℝ) : EReal) := by
  rw [pressureValue_eq_manuscript hd β ρ hρ, densityValue_eq_manuscript hd β ρ hρ]
  have hN : negSobolevEnergy ρ.value ≠ ∞ :=
    (negSobolevEnergy_ne_top_iff ρ).2 (finiteEntropy_spectralEnergy_ne_top hd ρ hρ)
  have hent : torusEntropy ρ.value ≠ ∞ := (torusEntropy_density_ne_top_iff ρ).2 hρ
  rw [← EReal.coe_ennreal_toReal hN, ← EReal.coe_ennreal_toReal hent, ← EReal.coe_mul,
    ← EReal.coe_sub]

/-- `ρ` is a global minimizer exactly when it has finite entropy and attains the extended-real
pressure. -/
theorem isGlobalMinimizer_iff_pressure (d : ℕ) (β : ℝ) (ρ : ProbabilityDensity d) :
    IsGlobalMinimizer β ρ ↔ ρ.FiniteEntropy ∧ pressure d β = pressureValue β ρ := by
  unfold IsGlobalMinimizer pressure
  refine and_congr_right fun hρ => ?_
  constructor
  · intro h
    refine le_antisymm (iSup₂_le fun σ hσ => h σ hσ) ?_
    exact le_iSup₂_of_le ρ hρ le_rfl
  · intro h σ hσ
    rw [← h]
    exact le_iSup₂_of_le σ hσ le_rfl

theorem pressureValue_le_pressure (d : ℕ) (β : ℝ) (σ : ProbabilityDensity d)
    (hσ : σ.FiniteEntropy) : pressureValue β σ ≤ pressure d β :=
  le_iSup₂_of_le σ hσ le_rfl

/-! ## Mean zero of differences -/

theorem meanZero_sub {u v : Torus d → ℝ} (hu : MemLp u 2 (torusMeasure d))
    (hv : MemLp v 2 (torusMeasure d)) (hmu : MeanZero u) (hmv : MeanZero v) :
    MeanZero (u - v) := by
  unfold MeanZero at *
  have h1 := hu.integrable one_le_two
  have h2 := hv.integrable one_le_two
  have : (∫ x, (u - v) x ∂torusMeasure d) = (∫ x, u x ∂torusMeasure d) - ∫ x, v x ∂torusMeasure d :=
    integral_sub h1 h2
  rw [this, hmu, hmv]; simp

/-! ## The two gap identities in terms of `coefficientValue` -/

/-- The printed primal gap identity `eq:section2-primal-gap-identity`, written with
`coefficientValue`: for mean-zero `u ∈ H^{d/2}`, `σ = e^u / ∫ e^u` and `β = (2 A c_d)⁻¹`,
`value(u) = (β c_d/2 ‖σ‖² - Ent σ) - A ‖u - β g * σ‖²_{Ḣ^{d/2}}`. -/
theorem coefficientValue_gap (hd : 0 < d) {A : ℝ} (hA : 0 < A) {u : Torus d → ℝ}
    (hu : InCriticalSobolev u) (hm : MeanZero u) :
    ∃ _ : InCriticalSobolev (Gap.densityPotential (Gap.coefficient d A) (normalizedGibbs u)),
      coefficientValue A u =
        Gap.densityValue (Gap.coefficient d A) (normalizedGibbs u) -
          A * potentialEnergy (u - Gap.densityPotential (Gap.coefficient d A) (normalizedGibbs u)) := by
  exact coefficientValue_gap_written hd hA hu hm

/-- The printed dual gap identity `eq:section2-dual-gap-identity`, written with `coefficientValue`:
for a finite-entropy density `ρ`, `β = (2 A c_d)⁻¹` and `u_ρ = β g * ρ`,
`β c_d/2 ‖ρ‖² - Ent ρ = value(u_ρ) - H_r(ρ | e^{u_ρ}/∫e^{u_ρ})`, with the relative entropy finite. -/
theorem densityValue_gap (hd : 0 < d) {A : ℝ} (hA : 0 < A) (ρ : ProbabilityDensity d)
    (hρ : ρ.FiniteEntropy) :
    ∃ (hu : InCriticalSobolev (Gap.densityPotential (Gap.coefficient d A) ρ.value))
      (hm : MeanZero (Gap.densityPotential (Gap.coefficient d A) ρ.value)),
      measureEntropy (densityMeasure ρ)
        (densityMeasure (normalizedGibbsDensity hd _ hu hm)) ≠ ∞ ∧
      Gap.densityValue (Gap.coefficient d A) ρ.value =
        coefficientValue A (Gap.densityPotential (Gap.coefficient d A) ρ.value) -
          (measureEntropy (densityMeasure ρ)
            (densityMeasure (normalizedGibbsDensity hd _ hu hm))).toReal := by
  exact densityValue_gap_written hd hA ρ hρ

/-! ## `cor:section2-extremizer-correspondence` (i) -/

/-- **Corollary 2.6 (i)** (`cor:section2-extremizer-correspondence`).  For `A > 0` and
`β = (2 A c_d)⁻¹`, a mean-zero `u ∈ H^{d/2}` maximizes `C_d(A)` if and only if the density
`ρ_u = e^u / ∫ e^u` maximizes `P_d(β)` (i.e. minimizes the free energy) and `u = β g * ρ_u`
(as elements of `H^{d/2}`, i.e. almost everywhere). -/
theorem coefficientMaximizer_iff (hd : 0 < d) {A : ℝ} (hA : 0 < A) {u : Torus d → ℝ}
    (hu : InCriticalSobolev u) (hm : MeanZero u) :
    IsCoefficientMaximizer d A u ↔
      IsGlobalMinimizer (Gap.coefficient d A) (normalizedGibbsDensity hd u hu hm) ∧
        u =ᵐ[torusMeasure d] Gap.densityPotential (Gap.coefficient d A) (normalizedGibbs u) := by
  have hβ : 0 < Gap.coefficient d A := Gap.coefficient_pos hd hA
  set β := Gap.coefficient d A with hβdef
  set σ := normalizedGibbsDensity hd u hu hm with hσdef
  have hσf : σ.FiniteEntropy := normalizedGibbsDensity_finiteEntropy hd u hu hm
  have hσv : σ.value = normalizedGibbs u := rfl
  obtain ⟨hreg, hgap⟩ := coefficientValue_gap hd hA hu hm
  have hdual := coefficient_pressure_duality hd hA
  rw [← gapCoefficient_eq hd hA] at hdual
  rw [isCoefficientMaximizer_iff hd]
  have hE0 : 0 ≤ potentialEnergy (u - Gap.densityPotential β (normalizedGibbs u)) :=
    potentialEnergy_nonneg _
  have hsubC : InCriticalSobolev (u - Gap.densityPotential β (normalizedGibbs u)) :=
    FullHessianDecomposition.critical_sub _ _ hu hreg
  have hmuσ : MeanZero (Gap.densityPotential β (normalizedGibbs u)) :=
    (Gap.densityPotential_regular hd hβ σ hσf).2
  have hmsub : MeanZero (u - Gap.densityPotential β (normalizedGibbs u)) :=
    meanZero_sub hu.1 hreg.1 hm hmuσ
  constructor
  · rintro ⟨-, -, hC⟩
    -- the value of `u` is `C_d(A) = P_d(β)`
    have hP : pressure d β = ((coefficientValue A u : ℝ) : EReal) := hdual.symm.trans hC
    have hle : Gap.densityValue β (normalizedGibbs u) ≤ coefficientValue A u := by
      have h1 := pressureValue_le_pressure d β σ hσf
      rw [pressureValue_eq_densityValue hd β σ hσf, hP, hσv] at h1
      exact EReal.coe_le_coe_iff.mp h1
    have hzero : potentialEnergy (u - Gap.densityPotential β (normalizedGibbs u)) = 0 := by
      have : A * potentialEnergy (u - Gap.densityPotential β (normalizedGibbs u)) ≤ 0 := by
        linarith
      exact le_antisymm (by nlinarith) hE0
    have heq : Gap.densityValue β (normalizedGibbs u) = coefficientValue A u := by
      rw [hgap, hzero]; ring
    refine ⟨(isGlobalMinimizer_iff_pressure d β σ).2 ⟨hσf, ?_⟩, ?_⟩
    · rw [hP, pressureValue_eq_densityValue hd β σ hσf, hσv, heq]
    · have h0 := ae_eq_zero_of_potentialEnergy_eq_zero hsubC hmsub hzero
      filter_upwards [h0] with x hx
      have : u x - Gap.densityPotential β (normalizedGibbs u) x = 0 := hx
      linarith
  · rintro ⟨hmin, hae⟩
    obtain ⟨-, hP⟩ := (isGlobalMinimizer_iff_pressure d β σ).1 hmin
    have hzero : potentialEnergy (u - Gap.densityPotential β (normalizedGibbs u)) = 0 := by
      have hz : (u - Gap.densityPotential β (normalizedGibbs u)) =ᵐ[torusMeasure d] 0 := by
        filter_upwards [hae] with x hx
        simp [hx]
      rw [Gap.potentialEnergy_congr hz]
      have h := potentialEnergy_const_mul 0 (fun _ : Torus d => (1 : ℝ))
      have h' : potentialEnergy (fun _ : Torus d => (0 : ℝ)) = 0 := by simpa using h
      exact h'
    refine ⟨hu, hm, ?_⟩
    rw [hdual, hP, pressureValue_eq_densityValue hd β σ hσf, hσv, hgap, hzero]
    norm_num
    rfl

/-! ## `cor:section2-extremizer-correspondence` (ii) -/

/-- **Corollary 2.6 (ii)** (`cor:section2-extremizer-correspondence`).  For `A > 0`,
`β = (2 A c_d)⁻¹` and a finite-entropy density `ρ`, `ρ` maximizes `P_d(β)` if and only if the
potential `u_ρ = β g * ρ` maximizes `C_d(A)` and `ρ = e^{u_ρ} / ∫ e^{u_ρ}` (almost everywhere). -/
theorem densityMinimizer_iff (hd : 0 < d) {A : ℝ} (hA : 0 < A) (ρ : ProbabilityDensity d)
    (hρ : ρ.FiniteEntropy) :
    IsGlobalMinimizer (Gap.coefficient d A) ρ ↔
      IsCoefficientMaximizer d A (Gap.densityPotential (Gap.coefficient d A) ρ.value) ∧
        ρ.value =ᵐ[torusMeasure d]
          normalizedGibbs (Gap.densityPotential (Gap.coefficient d A) ρ.value) := by
  have hβ : 0 < Gap.coefficient d A := Gap.coefficient_pos hd hA
  set β := Gap.coefficient d A with hβdef
  obtain ⟨hu, hm, hfin, hgap⟩ := densityValue_gap hd hA ρ hρ
  set σ := normalizedGibbsDensity hd (Gap.densityPotential β ρ.value) hu hm with hσdef
  have hσv : σ.value = normalizedGibbs (Gap.densityPotential β ρ.value) := rfl
  have hdual := coefficient_pressure_duality hd hA
  rw [← gapCoefficient_eq hd hA] at hdual
  rw [isGlobalMinimizer_iff_pressure, isCoefficientMaximizer_iff hd]
  have hH0 : 0 ≤ (measureEntropy (densityMeasure ρ) (densityMeasure σ)).toReal := ENNReal.toReal_nonneg
  have hHz : (measureEntropy (densityMeasure ρ) (densityMeasure σ)).toReal = 0 ↔
      ρ.value =ᵐ[torusMeasure d] normalizedGibbs (Gap.densityPotential β ρ.value) := by
    rw [ENNReal.toReal_eq_zero_iff]
    constructor
    · rintro (h | h)
      · exact (measureEntropy_density_eq_zero_iff ρ σ).1 h
      · exact absurd h hfin
    · intro h
      exact Or.inl ((measureEntropy_density_eq_zero_iff ρ σ).2 h)
  constructor
  · rintro ⟨-, hP⟩
    rw [pressureValue_eq_densityValue hd β ρ hρ] at hP
    have hC : coefficientDefect d A = ((Gap.densityValue β ρ.value : ℝ) : EReal) := by
      rw [hdual, hP]
    have hcv : coefficientValue A (Gap.densityPotential β ρ.value) ≤ Gap.densityValue β ρ.value := by
      have h1 : ((coefficientValue A (Gap.densityPotential β ρ.value) : ℝ) : EReal) ≤
          coefficientDefect d A := by
        rw [coefficientDefect_eq_iSup hd]
        exact le_iSup₂_of_le _ hu le_rfl
      rw [hC] at h1
      exact EReal.coe_le_coe_iff.mp h1
    have hHzero : (measureEntropy (densityMeasure ρ) (densityMeasure σ)).toReal = 0 := by
      linarith
    refine ⟨⟨hu, hm, ?_⟩, hHz.1 hHzero⟩
    rw [hC, hgap, hHzero, sub_zero]
  · rintro ⟨⟨-, -, hC⟩, hae⟩
    have hHzero := hHz.2 hae
    refine ⟨hρ, ?_⟩
    rw [pressureValue_eq_densityValue hd β ρ hρ, hdual.symm.trans hC, hgap, hHzero, sub_zero]

end BecknerOnofri.V2.Reaudit.Attainment
