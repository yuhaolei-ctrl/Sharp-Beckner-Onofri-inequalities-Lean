module

public import BecknerOnofri.V2.Reaudit.Attainment.Pairing
public import BecknerOnofri.V2.Reaudit.Attainment.PotentialFourier
public import BecknerOnofri.V2.Reaudit.Attainment.DirectMethod

@[expose] public section

/-! # Fourier square completion and the two gap identities, from the printed argument
(`prop:section2-gap-identities`; used by row S009)

Printed proof of the gap identities: completing squares with `u_ρ = β g * ρ`,
`\hat u_ρ(k) = β c_d \hat ρ(k) / (2π|k|)^d`, and `2 A β c_d = 1` gives
`∫ u ρ - A ‖u‖² = (β c_d / 2) ‖ρ‖²_{Ḣ^{-d/2}} - A ‖u - u_ρ‖²`
(`eq:section2-square-completion-identity`).  Here the ordinary integral `∫ u ρ` is the Fourier pairing
by `Pairing.lean` (`pairing_identification_nonzero`; decisions §5.7). -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped Topology ENNReal ComplexConjugate

namespace BecknerOnofri.V2.Reaudit.Attainment
open BecknerOnofri.HighDim BecknerOnofri.V2.Vocab

variable {d : ℕ}

/-- Completing the square for a single frequency: if `v = (t/w) y` then
`w |x - v|² = w |x|² - 2 t Re(conj x · y) + t² |y|² / w`. -/
theorem weighted_sub_sq {w t : ℝ} (hw : 0 < w) (x y : ℂ) :
    w * ‖x - ((t / w : ℝ) : ℂ) * y‖ ^ 2 =
      w * ‖x‖ ^ 2 - 2 * t * (conj x * y).re + t ^ 2 * (‖y‖ ^ 2 / w) := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
  field_simp
  ring

/-- The Fourier coefficients of `u_ρ = β g * ρ` in the form `\hat u_ρ(k) = (β c_d / (2π|k|)^d) \hat ρ(k)`
for `k ≠ 0`. -/
theorem fourierCoeff_densityPotential_eq (hd : 0 < d) {β : ℝ} (hβ : 0 < β)
    (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy) (k : NonzeroFrequency d) :
    fourierCoeff (Gap.densityPotential β ρ.value) k.val =
      ((β * kernelConstant d / (2 * Real.pi * frequencyLength k.val) ^ d : ℝ) : ℂ) *
        fourierCoeff ρ.value k.val := by
  have h := fourierCoeff_densityPotential hd hβ ρ hρ k.2
  have hL : 0 < frequencyLength k.val ^ d :=
    pow_pos (lt_of_lt_of_le zero_lt_one (BecknerOnofri.V2.Onset.one_le_frequencyLength k.2)) d
  have hLc : ((frequencyLength k.val : ℂ)) ^ d ≠ 0 := by exact_mod_cast hL.ne'
  have hs := spectralThreshold_pos' hd
  have hkc := kernelConstant_mul_spectralThreshold hd
  have hc := kernelConstant_pos hd
  have hreal : β * kernelConstant d / (2 * Real.pi * frequencyLength k.val) ^ d =
      (β / spectralThreshold d) / frequencyLength k.val ^ d := by
    rw [mul_pow, ← hkc]
    field_simp
  rw [hreal]
  have e : fourierCoeff (Gap.densityPotential β ρ.value) k.val =
      ((frequencyLength k.val : ℂ) ^ d)⁻¹ * (((β / spectralThreshold d : ℝ) : ℂ) *
        fourierCoeff ρ.value k.val) := by
    rw [← h]
    field_simp
  rw [e]
  push_cast
  ring

/-- **Fourier square completion** (`eq:section2-square-completion-identity`).  For `A > 0`,
`β = (2 A c_d)⁻¹`, a finite-entropy density `ρ`, and `u ∈ H^{d/2}` of mean zero,
`∫ u ρ - A ‖u‖²_{Ḣ^{d/2}} = (β c_d / 2) ‖ρ‖²_{Ḣ^{-d/2}} - A ‖u - u_ρ‖²_{Ḣ^{d/2}}`,
where `u_ρ = β g * ρ`. -/
theorem square_completion (hd : 0 < d) {A : ℝ} (hA : 0 < A) (ρ : ProbabilityDensity d)
    (hρ : ρ.FiniteEntropy) {u : Torus d → ℝ} (hu : InCriticalSobolev u) (hm : MeanZero u) :
    (∫ x, ρ.value x * u x ∂torusMeasure d) - A * potentialEnergy u =
      Gap.coefficient d A * kernelConstant d / 2 * (negSobolevEnergy ρ.value).toReal -
        A * potentialEnergy (u - Gap.densityPotential (Gap.coefficient d A) ρ.value) := by
  set β : ℝ := Gap.coefficient d A with hβdef
  have hβ : 0 < β := Gap.coefficient_pos hd hA
  have hc := kernelConstant_pos hd
  set κ : ℝ := β * kernelConstant d with hκ
  have h2Aκ : 2 * A * κ = 1 := by
    rw [hκ, hβdef, gapCoefficient_eq hd hA]
    field_simp
  obtain ⟨hreg, -⟩ := Gap.densityPotential_regular hd hβ ρ hρ
  have hsub : InCriticalSobolev (u - Gap.densityPotential β ρ.value) :=
    FullHessianDecomposition.critical_sub _ _ hu hreg
  -- the four series
  have hP := pairing_identification_nonzero hd ρ hρ hu hm
  have hE := hu.2.hasSum
  have hE' := hsub.2.hasSum
  set g : NonzeroFrequency d → ℝ := fun k =>
    ((2 * Real.pi * frequencyLength k.val) ^ d)⁻¹ * ‖fourierCoeff ρ.value k.val‖ ^ 2 with hg
  have hgs : Summable g := by
    have hs := (finiteEntropy_spectralTerm_summable hd ρ hρ).mul_left (((2 * Real.pi) ^ d)⁻¹)
    refine hs.congr fun k => ?_
    unfold spectralTerm
    simp only [hg, mul_pow]
    ring
  have hN : (negSobolevEnergy ρ.value).toReal = ∑' k, g k := by
    have hn : ∀ k, 0 ≤ g k := fun k => by
      simp only [hg]; unfold frequencyLength; positivity
    unfold negSobolevEnergy
    rw [← ENNReal.ofReal_tsum_of_nonneg hn hgs, ENNReal.toReal_ofReal (tsum_nonneg hn)]
  have hpt : ∀ k : NonzeroFrequency d, potentialTerm (u - Gap.densityPotential β ρ.value) k =
      potentialTerm u k - 2 * κ * (conj (fourierCoeff u k.val) * fourierCoeff ρ.value k.val).re +
        κ ^ 2 * g k := by
    intro k
    have hw : 0 < (2 * Real.pi * frequencyLength k.val) ^ d := by
      have : 1 ≤ frequencyLength k.val := BecknerOnofri.V2.Onset.one_le_frequencyLength k.2
      have := Real.pi_pos
      positivity
    unfold potentialTerm
    rw [FullHessianDecomposition.fourierCoeff_sub u _ hu.1 hreg.1,
      fourierCoeff_densityPotential_eq hd hβ ρ hρ k]
    have := weighted_sub_sq hw (fourierCoeff u k.val) (fourierCoeff ρ.value k.val) (t := κ)
    simp only [hg]
    rw [hκ] at this ⊢
    rw [this]
    ring
  have hcomb : HasSum (potentialTerm (u - Gap.densityPotential β ρ.value))
      (potentialEnergy u - 2 * κ * (∫ x, ρ.value x * u x ∂torusMeasure d) +
        κ ^ 2 * ∑' k, g k) := by
    have := (hE.sub (hP.mul_left (2 * κ))).add (hgs.hasSum.mul_left (κ ^ 2))
    refine this.congr_fun fun k => ?_
    rw [hpt k]
  have huniq := hE'.unique hcomb
  rw [hN]
  unfold potentialEnergy at huniq ⊢
  linear_combination A * huniq + (-(((∫ x, ρ.value x * u x ∂torusMeasure d)) - (∑' k, g k) * κ / 2)) * h2Aκ

/-! ## The Gibbs entropy formula and the relative entropy formula -/

/-- `eq:section2-duality-gibbs-entropy`: for a mean-zero `u ∈ H^{d/2}`, the Gibbs density
`ρ_u = e^u / ∫ e^u` satisfies `u ρ_u ∈ L¹` and `Ent(ρ_u) = ∫ u ρ_u - log ∫ e^u`. -/
theorem gibbs_entropy_formula (hd : 0 < d) {u : Torus d → ℝ} (hu : InCriticalSobolev u)
    (hm : MeanZero u) :
    Integrable (fun x => normalizedGibbs u x * u x) (torusMeasure d) ∧
      (∫ x, normalizedGibbs u x * Real.log (normalizedGibbs u x) ∂torusMeasure d) =
        (∫ x, normalizedGibbs u x * u x ∂torusMeasure d) -
          Real.log (∫ x, Real.exp (u x) ∂torusMeasure d) := by
  set σ := normalizedGibbsDensity hd u hu hm with hσ
  have hσf : σ.FiniteEntropy := normalizedGibbsDensity_finiteEntropy hd u hu hm
  have hint : Integrable (fun x => normalizedGibbs u x * u x) (torusMeasure d) :=
    (pairing_identification hd σ hσf hu hm).1
  refine ⟨hint, ?_⟩
  have hZ := partition_pos hd u hu hm
  have hpt : ∀ x, normalizedGibbs u x * Real.log (normalizedGibbs u x) =
      normalizedGibbs u x * u x - Real.log (∫ y, Real.exp (u y) ∂torusMeasure d) *
        normalizedGibbs u x := by
    intro x
    unfold normalizedGibbs
    rw [Real.log_div (Real.exp_pos _).ne' hZ.ne', Real.log_exp]
    ring
  have hI : Integrable (fun x => Real.log (∫ y, Real.exp (u y) ∂torusMeasure d) *
      normalizedGibbs u x) (torusMeasure d) := σ.integrable.const_mul _
  simp_rw [hpt]
  rw [integral_sub hint hI, integral_const_mul]
  have hmass : (∫ x, normalizedGibbs u x ∂torusMeasure d) = 1 := σ.mass
  rw [hmass, mul_one]

/-- `eq:section2-relative-entropy-gibbs`: for a finite-entropy density `ρ` and a mean-zero
`u ∈ H^{d/2}`, `ρ log(ρ / ρ_u)` is integrable and
`H_r(ρ | ρ_u) = Ent(ρ) - ∫ u ρ + log ∫ e^u`. -/
theorem relativeEntropy_gibbs_formula (hd : 0 < d) (ρ : ProbabilityDensity d)
    (hρ : ρ.FiniteEntropy) {u : Torus d → ℝ} (hu : InCriticalSobolev u) (hm : MeanZero u) :
    Integrable (fun x => ρ.value x * Real.log (ρ.value x / normalizedGibbs u x))
        (torusMeasure d) ∧
      Gap.relativeEntropy ρ.value (normalizedGibbs u) =
        entropy ρ - (∫ x, ρ.value x * u x ∂torusMeasure d) +
          Real.log (∫ x, Real.exp (u x) ∂torusMeasure d) := by
  have hZ := partition_pos hd u hu hm
  have hpair := (pairing_identification hd ρ hρ hu hm).1
  have hae : (fun x => ρ.value x * Real.log (ρ.value x / normalizedGibbs u x)) =ᵐ[torusMeasure d]
      fun x => ρ.value x * Real.log (ρ.value x) - ρ.value x * u x +
        ρ.value x * Real.log (∫ y, Real.exp (u y) ∂torusMeasure d) := by
    filter_upwards [ρ.nonneg] with x hx
    rcases hx.eq_or_lt with h0 | hpos
    · rw [← h0]; simp
    · unfold normalizedGibbs
      rw [Real.log_div hpos.ne' (div_pos (Real.exp_pos _) hZ).ne', Real.log_div (Real.exp_pos _).ne'
        hZ.ne', Real.log_exp]
      ring
  have hint : Integrable (fun x => ρ.value x * Real.log (ρ.value x) - ρ.value x * u x +
      ρ.value x * Real.log (∫ y, Real.exp (u y) ∂torusMeasure d)) (torusMeasure d) :=
    (hρ.sub hpair).add (ρ.integrable.mul_const _)
  refine ⟨hint.congr hae.symm, ?_⟩
  have hfg : Integrable (fun x => ρ.value x * Real.log (ρ.value x) - ρ.value x * u x)
      (torusMeasure d) := hρ.sub hpair
  have hc : Integrable (fun x => ρ.value x * Real.log (∫ y, Real.exp (u y) ∂torusMeasure d))
      (torusMeasure d) := ρ.integrable.mul_const _
  unfold Gap.relativeEntropy
  rw [integral_congr_ae hae, integral_add hfg hc, integral_sub hρ hpair, integral_mul_const,
    ρ.mass, one_mul]
  rfl

theorem potentialEnergy_zero' : potentialEnergy (fun _ : Torus d => (0 : ℝ)) = 0 := by
  have h := potentialEnergy_const_mul 0 (fun _ : Torus d => (1 : ℝ))
  simpa using h

/-! ## The two gap identities, from the Fourier square completion -/

/-- **`eq:section2-primal-gap-identity`** (printed route).  For `A > 0`, `β = (2 A c_d)⁻¹`, a
mean-zero `u ∈ H^{d/2}` and `σ = e^u / ∫ e^u`:
`value(u) = (β c_d / 2 ‖σ‖² - Ent σ) - A ‖u - β g * σ‖²_{Ḣ^{d/2}}`.
Proof: `Ent σ = ∫ u σ - log ∫ e^u` (`gibbs_entropy_formula`) and `square_completion` with `ρ = σ`. -/
theorem coefficientValue_gap_written (hd : 0 < d) {A : ℝ} (hA : 0 < A) {u : Torus d → ℝ}
    (hu : InCriticalSobolev u) (hm : MeanZero u) :
    ∃ _ : InCriticalSobolev (Gap.densityPotential (Gap.coefficient d A) (normalizedGibbs u)),
      coefficientValue A u =
        Gap.densityValue (Gap.coefficient d A) (normalizedGibbs u) -
          A * potentialEnergy (u - Gap.densityPotential (Gap.coefficient d A) (normalizedGibbs u)) := by
  set σ := normalizedGibbsDensity hd u hu hm with hσ
  have hσf : σ.FiniteEntropy := normalizedGibbsDensity_finiteEntropy hd u hu hm
  have hβ : 0 < Gap.coefficient d A := Gap.coefficient_pos hd hA
  refine ⟨(Gap.densityPotential_regular hd hβ σ hσf).1, ?_⟩
  obtain ⟨-, hent⟩ := gibbs_entropy_formula hd hu hm
  have hsc := square_completion hd hA σ hσf hu hm
  have hdv := densityValue_eq_manuscript hd (Gap.coefficient d A) σ hσf
  have hE := entropy_eq_toReal_torusEntropy σ hσf
  unfold coefficientValue
  rw [centered_eq_self hm]
  have hdv' : Gap.densityValue (Gap.coefficient d A) (normalizedGibbs u) =
      Gap.coefficient d A * kernelConstant d / 2 * (negSobolevEnergy (normalizedGibbs u)).toReal -
        (torusEntropy (normalizedGibbs u)).toReal := hdv
  have hE' : (∫ x, normalizedGibbs u x * Real.log (normalizedGibbs u x) ∂torusMeasure d) =
      (torusEntropy (normalizedGibbs u)).toReal := hE
  have hsc' : (∫ x, normalizedGibbs u x * u x ∂torusMeasure d) - A * potentialEnergy u =
      Gap.coefficient d A * kernelConstant d / 2 * (negSobolevEnergy (normalizedGibbs u)).toReal -
        A * potentialEnergy (u - Gap.densityPotential (Gap.coefficient d A) (normalizedGibbs u)) :=
    hsc
  rw [hdv']
  linarith

/-- **`eq:section2-dual-gap-identity`** (printed route).  For a finite-entropy density `ρ`,
`β = (2 A c_d)⁻¹`, `u_ρ = β g * ρ` (in `H^{d/2}` with mean zero) and `σ = e^{u_ρ} / ∫ e^{u_ρ}`:
`H_r(ρ | σ) < ∞` and `β c_d / 2 ‖ρ‖² - Ent ρ = value(u_ρ) - H_r(ρ | σ)`.
Proof: `gibbs`-formula for the relative entropy (`relativeEntropy_gibbs_formula`) and
`square_completion` with `u = u_ρ`, for which the remainder `‖u_ρ - u_ρ‖² = 0`. -/
theorem densityValue_gap_written (hd : 0 < d) {A : ℝ} (hA : 0 < A) (ρ : ProbabilityDensity d)
    (hρ : ρ.FiniteEntropy) :
    ∃ (hu : InCriticalSobolev (Gap.densityPotential (Gap.coefficient d A) ρ.value))
      (hm : MeanZero (Gap.densityPotential (Gap.coefficient d A) ρ.value)),
      measureEntropy (densityMeasure ρ)
        (densityMeasure (normalizedGibbsDensity hd _ hu hm)) ≠ ∞ ∧
      Gap.densityValue (Gap.coefficient d A) ρ.value =
        coefficientValue A (Gap.densityPotential (Gap.coefficient d A) ρ.value) -
          (measureEntropy (densityMeasure ρ)
            (densityMeasure (normalizedGibbsDensity hd _ hu hm))).toReal := by
  have hβ : 0 < Gap.coefficient d A := Gap.coefficient_pos hd hA
  obtain ⟨hu, hm⟩ := Gap.densityPotential_regular hd hβ ρ hρ
  refine ⟨hu, hm, ?_⟩
  set v := Gap.densityPotential (Gap.coefficient d A) ρ.value with hv
  have hpos := normalizedGibbs_pos hd v hu hm
  obtain ⟨hint, hrel⟩ := relativeEntropy_gibbs_formula hd ρ hρ hu hm
  have hpos' : ∀ x, 0 < (normalizedGibbsDensity hd v hu hm).value x := hpos
  have hfin : measureEntropy (densityMeasure ρ)
      (densityMeasure (normalizedGibbsDensity hd v hu hm)) ≠ ∞ := by
    rw [Ne, measureEntropy_density_eq_top_iff (σ := normalizedGibbsDensity hd v hu hm) hpos',
      not_not]
    exact hint
  refine ⟨hfin, ?_⟩
  have hsc := square_completion hd hA ρ hρ hu hm
  rw [sub_self, show (0 : Torus d → ℝ) = fun _ => 0 from rfl, potentialEnergy_zero', mul_zero,
    sub_zero] at hsc
  have hdv := densityValue_eq_manuscript hd (Gap.coefficient d A) ρ hρ
  have hE := entropy_eq_toReal_torusEntropy ρ hρ
  have hrel' := relativeEntropy_eq_toReal_measureEntropy (ρ := ρ)
    (σ := normalizedGibbsDensity hd v hu hm) hpos'
  unfold coefficientValue
  rw [centered_eq_self hm, ← hrel']
  have hrel2 : Gap.relativeEntropy ρ.value (normalizedGibbsDensity hd v hu hm).value =
      entropy ρ - (∫ x, ρ.value x * v x ∂torusMeasure d) +
        Real.log (∫ x, Real.exp (v x) ∂torusMeasure d) := hrel
  rw [hrel2]
  have hE' : entropy ρ = (torusEntropy ρ.value).toReal := hE
  have hpe : potentialEnergy (Gap.densityPotential (Gap.coefficient d A) ρ.value) =
      potentialEnergy v := rfl
  linarith

end BecknerOnofri.V2.Reaudit.Attainment
