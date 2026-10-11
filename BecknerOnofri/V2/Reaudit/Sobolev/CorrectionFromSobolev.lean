module

public import BecknerOnofri.V2.Reaudit.Sobolev.Reduction
public import BecknerOnofri.V2.Reaudit.Compactness.EulerSobolev

@[expose] public section

/-! # The complement correction of Section 5 from the Sobolev implicit-function theorem

Manuscript Section 5, `subsec:section5-lyapunov-schmidt`: the complement graph `w(τ, z)` is
produced by the analytic implicit-function theorem on the Sobolev Banach algebra
`H^s_0(𝕋^d)`, `s > d/2`.  Here `s = d`.  This module lies below
`LocalEleven.GreenLocalBranch` and proves the five-clause statement
`LocalEleven.GreenLocalBranch.exists_analytic_complement` (with the topology of the continuous
functions in the uniqueness clause) for the witness `HsC.toComplement ∘ graph`:

* clauses 1-4 (analyticity, value and derivative `0` at `(1, 0)`, solution of the projected
  equation) are transported from `graph` through the continuous inclusion
  `HsC.toComplement : K^⊥ ∩ H^d → K^⊥ ⊂ C(𝕋^d)` and `toComplement_complementEq`;
* clause 5 (uniqueness among *continuous* `w`, small in the sup norm) uses that a continuous
  solution of `w = μ P_{K^⊥} T (e^{v+w}/∫e^{v+w} - 1)` automatically lies in `H^d`, with
  `‖w‖_{H^d} ≤ (1+4π²)^{d/2} |μ| ‖e^{v+w}/∫e^{v+w} - 1‖_{L²}` (the multiplier `|k|^{-d}`,
  `|k| ≥ 1` off `0`, as in `sobolev_green_bound`), and this tends to `0` with the sup norm of
  `(z, w)`; hence small continuous solutions lie in the `H^d`-ball in which `graph_unique`
  applies. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter Asymptotics
open scoped ENNReal Topology ContDiff

namespace BecknerOnofri.V2.Reaudit.Sobolev
open BecknerOnofri.HighDim ContinuousGibbs ContinuousFirstShell ContinuousComplement

variable {d : ℕ}

/-! ## Compatibility with the continuous-function equation -/

/-- The inclusion `H^s_{K^⊥} → C(𝕋^d)_{K^⊥}` intertwines the `H^s` complement equation with the
continuous projected equation. -/
theorem toComplement_complementEq {s : ℝ} [SobolevIndex d s] (τ : ℝ) (z : Coordinates d)
    (w : HsC d s) :
    HsC.toComplement d s (complementEq d s τ z w) =
      projectedEquation (greenContinuous d) ((τ, z), HsC.toComplement d s w) := by
  unfold complementEq projectedEquation
  rw [map_sub, map_smul, Hs.toComplement_complMap]
  congr 2
  rw [Hs.greenH_val, Hs.val_sub, Hs.val_gibbs, Hs.val_one, Hs.reconstructionH_val]

/-! ## A continuous solution of the projected equation lies in `H^d` -/

/-- Fourier-multiplier estimate for a function whose Fourier coefficients are dominated by those
of `h` times the Green symbol `|c| |k|^{-d}` (`k ≠ 0`), `0` at `k = 0`: it lies in `H^d` and
`‖u‖_{H^d} ≤ (1+4π²)^{d/2} |c| ‖h‖_{L²}`.  (Same proof as
`Compactness.sobolev_green_bound`, with an inequality instead of an identity between the
coefficients, so that it also applies after the projection `P_{K^⊥}`.) -/
theorem sobolev_green_dominated (hd : 0 < d) (c : ℝ) (h u : Space d)
    (hu : ∀ k : Frequency d, ‖fourierCoeff (⇑u) k‖ ≤
      |c| * (if k = 0 then 0 else 1 / frequencyLength k ^ d : ℝ) * ‖fourierCoeff (⇑h) k‖) :
    InSobolev (d : ℝ) ⇑u ∧
      sobolevNorm (d : ℝ) ⇑u ≤
        Real.sqrt ((1 + (2 * Real.pi) ^ 2) ^ d) * |c| *
          Real.sqrt (∫ x, (h x) ^ 2 ∂torusMeasure d) := by
  set C : ℝ := (1 + (2 * Real.pi) ^ 2) ^ d with hC
  have hCpos : 0 < C := by positivity
  have hterm : ∀ k : Frequency d, sobolevTerm (d : ℝ) ⇑u k ≤ C * c ^ 2 * ‖fourierCoeff (⇑h) k‖ ^ 2 := by
    intro k
    by_cases hk : k = 0
    · subst hk
      have h0 : ‖fourierCoeff (⇑u) 0‖ = 0 := by
        have := hu 0
        simp only [ite_true, mul_zero, zero_mul] at this
        exact le_antisymm this (norm_nonneg _)
      rw [sobolevTerm, h0]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]
      positivity
    · have hL := Compactness.one_le_frequencyLength hd hk
      have hL0 : 0 < frequencyLength k := lt_of_lt_of_le one_pos hL
      have hu' := hu k
      simp only [hk, ↓reduceIte] at hu'
      rw [sobolevTerm, Real.rpow_natCast]
      have h1 : (1 + (2 * Real.pi * frequencyLength k) ^ 2) ≤
          (1 + (2 * Real.pi) ^ 2) * frequencyLength k ^ 2 := by
        nlinarith [sq_nonneg (2 * Real.pi), mul_pow (2 * Real.pi) (frequencyLength k) 2]
      have h2 : (1 + (2 * Real.pi * frequencyLength k) ^ 2) ^ d ≤
          C * (frequencyLength k ^ d) ^ 2 := by
        calc (1 + (2 * Real.pi * frequencyLength k) ^ 2) ^ d
            ≤ ((1 + (2 * Real.pi) ^ 2) * frequencyLength k ^ 2) ^ d :=
              pow_le_pow_left₀ (by positivity) h1 d
          _ = C * (frequencyLength k ^ d) ^ 2 := by
              rw [mul_pow, hC, ← pow_mul, ← pow_mul, mul_comm 2 d]
      have hp : 0 < frequencyLength k ^ d := pow_pos hL0 d
      have hsq : ‖fourierCoeff (⇑u) k‖ ^ 2 ≤
          (|c| * (1 / frequencyLength k ^ d) * ‖fourierCoeff (⇑h) k‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hu' 2
      calc (1 + (2 * Real.pi * frequencyLength k) ^ 2) ^ d * ‖fourierCoeff (⇑u) k‖ ^ 2
          ≤ C * (frequencyLength k ^ d) ^ 2 *
            (|c| * (1 / frequencyLength k ^ d) * ‖fourierCoeff (⇑h) k‖) ^ 2 := by
            gcongr
        _ = C * c ^ 2 * ‖fourierCoeff (⇑h) k‖ ^ 2 := by
            field_simp
            rw [sq_abs]
            ring
  have hps := UniformFourier.parseval h
  have hsum : Summable (sobolevTerm (d : ℝ) ⇑u) :=
    Summable.of_nonneg_of_le (fun k => mul_nonneg (by positivity) (sq_nonneg _)) hterm
      (hps.summable.mul_left (C * c ^ 2))
  refine ⟨⟨u.continuous.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _), hsum⟩, ?_⟩
  have htsum : ∑' k, sobolevTerm (d : ℝ) ⇑u k ≤ C * c ^ 2 * ∫ x, (h x) ^ 2 ∂torusMeasure d := by
    calc ∑' k, sobolevTerm (d : ℝ) ⇑u k ≤ ∑' k, C * c ^ 2 * ‖fourierCoeff (⇑h) k‖ ^ 2 :=
          hsum.tsum_le_tsum hterm (hps.summable.mul_left _)
      _ = C * c ^ 2 * ∫ x, (h x) ^ 2 ∂torusMeasure d := by
          rw [tsum_mul_left, hps.tsum_eq]
  unfold sobolevNorm
  calc Real.sqrt (∑' k, sobolevTerm (d : ℝ) ⇑u k)
      ≤ Real.sqrt (C * c ^ 2 * ∫ x, (h x) ^ 2 ∂torusMeasure d) := Real.sqrt_le_sqrt htsum
    _ = Real.sqrt C * |c| * Real.sqrt (∫ x, (h x) ^ 2 ∂torusMeasure d) := by
        rw [Real.sqrt_mul (by positivity : 0 ≤ C * c ^ 2), Real.sqrt_mul hCpos.le,
          Real.sqrt_sq_eq_abs]

/-- The density deviation `ρ_{v+w} - 1` appearing in the projected equation. -/
def densityDeviation (z : Coordinates d) (w : complement d) : Space d :=
  normalized (reconstruction d (z, w)) - 1

/-- A continuous solution `w` of the projected equation has Fourier coefficients dominated by
`|μ| |k|^{-d}` times those of the density deviation. -/
theorem coeff_le_of_projectedEquation (hd : 0 < d) (μ : ℝ) (z : Coordinates d) (w : complement d)
    (hw : projectedEquation (greenContinuous d) ((μ, z), w) = 0) (k : Frequency d) :
    ‖fourierCoeff (⇑(w : Space d)) k‖ ≤
      |μ| * (if k = 0 then 0 else 1 / frequencyLength k ^ d : ℝ) *
        ‖fourierCoeff (⇑(densityDeviation z w)) k‖ := by
  classical
  have hw' : w = μ • complementMap d (greenContinuous d (densityDeviation z w)) :=
    sub_eq_zero.mp hw
  have hcoef : coefficient k (w : Space d) =
      μ * (if ComplementFrequency k then
        ((if k = 0 then 0 else 1 / frequencyLength k ^ d : ℝ) : ℂ) *
          coefficient k (densityDeviation z w) else 0) := by
    have h1 : (w : Space d) = μ • (complementMap d (greenContinuous d (densityDeviation z w)) : Space d) :=
      congrArg (fun x : complement d => (x : Space d)) hw'
    rw [h1, map_smul, QuadraticModes.complementMap_coefficient, Complex.real_smul]
    by_cases hk : ComplementFrequency k
    · simp only [hk, ↓reduceIte]
      rw [coefficient_green hd]
    · simp only [hk, ↓reduceIte, mul_zero]
  have hmul : ‖coefficient k (w : Space d)‖ =
      |μ| * ((if ComplementFrequency k then
        (if k = 0 then 0 else 1 / frequencyLength k ^ d : ℝ) *
          ‖coefficient k (densityDeviation z w)‖ else 0)) := by
    rw [hcoef, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    congr 1
    by_cases hk : ComplementFrequency k
    · simp only [hk, ↓reduceIte]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
      split_ifs
      · exact le_rfl
      · have : 0 ≤ frequencyLength k := Real.sqrt_nonneg _
        positivity
    · simp only [hk, ↓reduceIte, norm_zero]
  rw [← coefficient_eq_fourierCoeff, ← coefficient_eq_fourierCoeff, hmul]
  have hnn : 0 ≤ (if k = 0 then 0 else 1 / frequencyLength k ^ d : ℝ) := by
    split_ifs
    · exact le_rfl
    · have : 0 ≤ frequencyLength k := Real.sqrt_nonneg _
      positivity
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg μ)
  by_cases hk : ComplementFrequency k
  · simp only [hk, ↓reduceIte]; exact le_rfl
  · simp only [hk, ↓reduceIte]; exact mul_nonneg hnn (norm_nonneg _)

theorem integral_sq_le_norm_sq (h : Space d) : ∫ x, (h x) ^ 2 ∂torusMeasure d ≤ ‖h‖ ^ 2 := by
  have : IsProbabilityMeasure (torusMeasure d) := inferInstance
  calc ∫ x, (h x) ^ 2 ∂torusMeasure d ≤ ∫ _x, ‖h‖ ^ 2 ∂torusMeasure d := by
        apply integral_mono
        · exact (h.continuous.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
        · exact integrable_const _
        · intro x
          have := h.norm_coe_le_norm x
          show (h x) ^ 2 ≤ ‖h‖ ^ 2
          calc (h x) ^ 2 = ‖h x‖ ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
            _ ≤ ‖h‖ ^ 2 := by gcongr
    _ = ‖h‖ ^ 2 := by simp

/-- **A continuous solution of the projected equation lies in `H^d`**, with
`‖w‖_{H^d} ≤ (1+4π²)^{d/2} |μ| ‖ρ_{v+w} - 1‖_∞`. -/
theorem projected_solution_inSobolev (hd : 0 < d) (μ : ℝ) (z : Coordinates d) (w : complement d)
    (hw : projectedEquation (greenContinuous d) ((μ, z), w) = 0) :
    InSobolev (d : ℝ) ⇑(w : Space d) ∧
      sobolevNorm (d : ℝ) ⇑(w : Space d) ≤
        Real.sqrt ((1 + (2 * Real.pi) ^ 2) ^ d) * |μ| * ‖densityDeviation z w‖ := by
  obtain ⟨h1, h2⟩ := sobolev_green_dominated hd μ (densityDeviation z w) (w : Space d)
    (coeff_le_of_projectedEquation hd μ z w hw)
  refine ⟨h1, h2.trans ?_⟩
  gcongr
  exact Real.sqrt_le_iff.mpr ⟨norm_nonneg _, integral_sq_le_norm_sq _⟩

theorem sobolevIndex_self (hd : 0 < d) : SobolevIndex d (d : ℝ) :=
  ⟨hd, by have : (0 : ℝ) < d := by exact_mod_cast hd
          linarith⟩

/-- **The complement correction of Section 5**: the analytic graph `graph : ℝ × ℂ^d → K^⊥ ⊂ H^d`
of the Sobolev implicit-function theorem (`Reduction.lean`, `s = d`), viewed in `K^⊥ ⊂ C(𝕋^d)`
through the inclusion `H^d ↪ C(𝕋^d)`. -/
def sobolevCorrection (hd : 11 ≤ d) : ℝ × Coordinates d → complement d :=
  haveI := sobolevIndex_self (d := d) (by omega)
  fun x => HsC.toComplement d (d : ℝ) (graph (s := (d : ℝ)) hd x)

/-- **The five properties of the complement correction** (the statement of
`LocalEleven.GreenLocalBranch.exists_analytic_complement`, with uniqueness in the topology of the
continuous functions) for `sobolevCorrection`. -/
theorem sobolevCorrection_spec (hd : 11 ≤ d) :
    AnalyticAt ℝ (sobolevCorrection hd) (1, 0) ∧ sobolevCorrection hd (1, 0) = 0 ∧
      HasFDerivAt (𝕜 := ℝ) (sobolevCorrection hd) 0 (1, 0) ∧
      (∀ᶠ x in 𝓝 (1, (0 : Coordinates d)),
        projectedEquation (greenContinuous d) (x, sobolevCorrection hd x) = 0) ∧
      (∀ᶠ x in 𝓝 ((1, (0 : Coordinates d)), (0 : complement d)),
        projectedEquation (greenContinuous d) x = 0 ↔ sobolevCorrection hd x.1 = x.2) := by
  have hd0 : 0 < d := by omega
  have : SobolevIndex d (d : ℝ) := sobolevIndex_self hd0
  have hdef : sobolevCorrection hd =
      fun x => HsC.toComplement d (d : ℝ) (graph (s := (d : ℝ)) hd x) := rfl
  rw [hdef]
  have hsolves : ∀ᶠ x in 𝓝 (1, (0 : Coordinates d)),
      projectedEquation (greenContinuous d) (x, HsC.toComplement d (d : ℝ) (graph hd x)) = 0 := by
    filter_upwards [graph_solves (s := (d : ℝ)) hd] with x hx
    rw [← toComplement_complementEq, hx, map_zero]
  refine ⟨?_, ?_, ?_, hsolves, ?_⟩
  · exact (HsC.toComplement d (d : ℝ)).analyticAt _ |>.comp (graph_analytic (s := (d : ℝ)) hd)
  · simp
  · have h := (HsC.toComplement d (d : ℝ)).hasFDerivAt.comp (1, (0 : Coordinates d))
      (graph_derivative_zero (s := (d : ℝ)) hd)
    convert! h using 1
  · -- uniqueness in the continuous topology
    have hU : ∀ᶠ y in (𝓝 (1, (0 : Coordinates d)) ×ˢ 𝓝 (0 : HsC d (d : ℝ))),
        complementEq d (d : ℝ) y.1.1 y.1.2 y.2 = 0 ↔ graph hd y.1 = y.2 := by
      rw [← nhds_prod_eq]; exact graph_unique (s := (d : ℝ)) hd
    obtain ⟨pa, hpa, pb, hpb, himp⟩ := (Filter.eventually_prod_iff).mp hU
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hpb
    set K : ℝ := 2 * (BecknerOnofri.V2.Onset.sobolevAlgConst d (d : ℝ) *
      Real.sqrt ((1 + (2 * Real.pi) ^ 2) ^ d)) with hK
    have hKpos : 0 < K := by
      have := algConst_pos d (d : ℝ)
      positivity
    have hN : Continuous (normalized : Space d → Space d) :=
      continuous_iff_continuousAt.2 fun u => (normalized_analytic u).continuousAt
    have hΦ : Continuous fun x : (ℝ × Coordinates d) × complement d =>
        ‖densityDeviation x.1.2 x.2‖ := by
      unfold densityDeviation
      fun_prop
    have h0 : ‖densityDeviation (0 : Coordinates d) (0 : complement d)‖ < ε / K := by
      have : ‖densityDeviation (0 : Coordinates d) (0 : complement d)‖ = 0 := by
        simp [densityDeviation]
      rw [this]; exact div_pos hε hKpos
    let base : (ℝ × Coordinates d) × complement d := ((1, 0), 0)
    have E1 : ∀ᶠ x in 𝓝 base, pa x.1 :=
      (continuous_fst.tendsto base).eventually hpa
    have E2 : ∀ᶠ x in 𝓝 base, |x.1.1| < 2 := by
      have hc : Continuous fun x : (ℝ × Coordinates d) × complement d => |x.1.1| := by fun_prop
      exact (hc.continuousAt (x := base)).eventually_lt
        (continuousAt_const (y := (2 : ℝ))) (by norm_num [base])
    have E3 : ∀ᶠ x in 𝓝 base, ‖densityDeviation x.1.2 x.2‖ < ε / K :=
      (hΦ.continuousAt (x := base)).eventually_lt (continuousAt_const (y := ε / K)) h0
    have E4 : ∀ᶠ x in 𝓝 base, projectedEquation (greenContinuous d)
          (x.1, HsC.toComplement d (d : ℝ) (graph hd x.1)) = 0 :=
      (continuous_fst.tendsto base).eventually hsolves
    filter_upwards [E1, E2, E3, E4] with x hx1 hx2 hx3 hx4
    constructor
    · intro hproj
      have hproj' : projectedEquation (greenContinuous d) ((x.1.1, x.1.2), x.2) = 0 := hproj
      obtain ⟨hS, hnormS⟩ := projected_solution_inSobolev hd0 x.1.1 x.1.2 x.2 hproj'
      let wH : HsC d (d : ℝ) := ⟨Hs.mk (x.2 : Space d) hS, x.2.property⟩
      have hwH : HsC.toComplement d (d : ℝ) wH = x.2 := Subtype.ext rfl
      have hC := algConst_pos d (d : ℝ)
      have hsq : 0 ≤ Real.sqrt ((1 + (2 * Real.pi) ^ 2) ^ d) := Real.sqrt_nonneg _
      have hn : ‖wH‖ < ε := by
        have e1 : ‖wH‖ = BecknerOnofri.V2.Onset.sobolevAlgConst d (d : ℝ) *
            sobolevNorm (d : ℝ) ⇑(x.2 : Space d) := Hs.norm_eq (Hs.mk (x.2 : Space d) hS)
        have e2 : sobolevNorm (d : ℝ) ⇑(x.2 : Space d) ≤
            Real.sqrt ((1 + (2 * Real.pi) ^ 2) ^ d) * 2 * ‖densityDeviation x.1.2 x.2‖ := by
          refine hnormS.trans ?_
          have : |x.1.1| ≤ 2 := hx2.le
          gcongr
        have e3 : ‖wH‖ ≤ K * ‖densityDeviation x.1.2 x.2‖ := by
          rw [e1, hK]
          calc BecknerOnofri.V2.Onset.sobolevAlgConst d (d : ℝ) * sobolevNorm (d : ℝ) ⇑(x.2 : Space d)
              ≤ BecknerOnofri.V2.Onset.sobolevAlgConst d (d : ℝ) *
                (Real.sqrt ((1 + (2 * Real.pi) ^ 2) ^ d) * 2 * ‖densityDeviation x.1.2 x.2‖) := by
                gcongr
            _ = _ := by ring
        calc ‖wH‖ ≤ K * ‖densityDeviation x.1.2 x.2‖ := e3
          _ < K * (ε / K) := by gcongr
          _ = ε := by field_simp
      have hpbw : pb wH := hball (by rw [dist_zero_right]; exact hn)
      have hcmp : complementEq d (d : ℝ) x.1.1 x.1.2 wH = 0 := by
        apply HsC.toComplement_injective
        rw [toComplement_complementEq, map_zero, hwH]
        exact hproj'
      have hg : graph hd x.1 = wH := (himp hx1 hpbw).mp hcmp
      show HsC.toComplement d (d : ℝ) (graph hd x.1) = x.2
      rw [hg, hwH]
    · intro hψ
      have hψ' : HsC.toComplement d (d : ℝ) (graph hd x.1) = x.2 := hψ
      rw [hψ'] at hx4
      exact hx4

/-- The five-clause statement of `LocalEleven.GreenLocalBranch.exists_analytic_complement`,
proved from the Sobolev implicit-function theorem. -/
theorem exists_analytic_complement_sobolev (hd : 11 ≤ d) :
    ∃ ψ : ℝ × Coordinates d → complement d,
      AnalyticAt ℝ ψ (1, 0) ∧ ψ (1, 0) = 0 ∧
      HasFDerivAt (𝕜 := ℝ) ψ 0 (1, 0) ∧
      (∀ᶠ x in 𝓝 (1, (0 : Coordinates d)),
        projectedEquation (greenContinuous d) (x, ψ x) = 0) ∧
      (∀ᶠ x in 𝓝 ((1, (0 : Coordinates d)), (0 : complement d)),
        projectedEquation (greenContinuous d) x = 0 ↔ ψ x.1 = x.2) :=
  ⟨sobolevCorrection hd, sobolevCorrection_spec hd⟩

#print axioms exists_analytic_complement_sobolev

end BecknerOnofri.V2.Reaudit.Sobolev
