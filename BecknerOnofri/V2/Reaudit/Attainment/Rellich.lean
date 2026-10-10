module

public import BecknerOnofri.V2.Reaudit.Attainment.Basic
public import BecknerOnofri.V2.Onset.Bootstrap

@[expose] public section

/-! # Compactness step of the direct method (`eq:section2-maximizer-compactness`)

Manuscript (proof of `prop:section2-subcritical-attainment`): a sequence of mean-zero potentials
bounded in `H^{d/2}` has a subsequence converging in `L²` and almost everywhere to a mean-zero
`u ∈ H^{d/2}`, and the seminorm of `u` is at most the `liminf` of the seminorms.

The statement is made for raw real functions `u : Torus d → ℝ` with `InCriticalSobolev u`.  The
`L²`-convergent subsequence is obtained from the repository's Rellich theorem for the
Fourier-coefficient energy ball
(`Legacy.BecknerOnofri.SubcriticalAttainment.realSobolevBall_isCompact`); the almost-everywhere
subsequence is the standard consequence of convergence in measure.  The lower semicontinuity of
the seminorm is the repository's `energy_lowerSemicontinuousOn`.

Route difference from the printed proof: the printed statement also asserts weak convergence
`u_n ⇀ u` in `H^{d/2}` and uses weak lower semicontinuity of the squared seminorm.  Weak convergence
is *not* formalized here.  The two consequences that the proof uses, namely convergence in `L²` and
almost everywhere and the inequality `‖u‖² ≤ liminf ‖u_n‖²`, are obtained directly: the first two
from the extraction in the compact ball of coefficient space, the third from the lower
semicontinuity of the seminorm for `L²` convergence (`energy_lowerSemicontinuousOn`). -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped Topology ENNReal

namespace BecknerOnofri.V2.Reaudit.Attainment
open BecknerOnofri.HighDim
open Legacy.BecknerOnofri.TorusSobolev Legacy.BecknerOnofri.SubcriticalAttainment

variable {d : ℕ}

theorem eLpNorm_real_sub_eq {u : Torus d → ℝ} (hu : MemLp u 2 (torusMeasure d))
    (v : TorusL2 d) (hv : RealPotential v) :
    eLpNorm (fun x => u x - RawAttainment.realValue v x) 2 (torusMeasure d) =
      eLpNorm (⇑(Bridge.potentialLp u hu - v) : Torus d → ℂ) 2 (torusMeasure d) := by
  apply eLpNorm_congr_norm_ae
    (hu.aestronglyMeasurable.sub (RawAttainment.realValue_memLp v).aestronglyMeasurable)
    (Lp.aestronglyMeasurable _)
  filter_upwards [Bridge.potentialLp_ae u hu, hv, Lp.coeFn_sub (Bridge.potentialLp u hu) v] with x h1 h2 h3
  rw [h3]
  simp only [Pi.sub_apply, h1, RawAttainment.realValue]
  have : (u x : ℂ) - v x = ((u x - (v x).re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp
    · simp [h2]
  rw [this, Complex.norm_real]

theorem eLpNorm_tendsto {u : ℕ → Torus d → ℝ} (hu : ∀ n, MemLp (u n) 2 (torusMeasure d))
    (v : TorusL2 d) (hv : RealPotential v)
    (h : Tendsto (fun n => Bridge.potentialLp (u n) (hu n)) atTop (𝓝 v)) :
    Tendsto (fun n => eLpNorm (fun x => u n x - RawAttainment.realValue v x) 2 (torusMeasure d))
      atTop (𝓝 0) := by
  simp_rw [eLpNorm_real_sub_eq (hu _) v hv]
  have h2 := tendsto_iff_norm_sub_tendsto_zero.mp h
  have h3 : Tendsto (fun n => ENNReal.ofReal ‖Bridge.potentialLp (u n) (hu n) - v‖) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal h2
  refine h3.congr fun n => ?_
  rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]
  rfl

theorem exists_L2_ae_limit (hd : 0 < d) {E : ℝ} (u : ℕ → Torus d → ℝ)
    (hu : ∀ n, InCriticalSobolev (u n)) (hm : ∀ n, MeanZero (u n))
    (hE : ∀ n, potentialEnergy (u n) ≤ E) :
    ∃ (φ : ℕ → ℕ) (v : Torus d → ℝ), StrictMono φ ∧ InCriticalSobolev v ∧ MeanZero v ∧
      Tendsto (fun n => eLpNorm (fun x => u (φ n) x - v x) 2 (torusMeasure d)) atTop (𝓝 0) ∧
      (∀ᵐ x ∂torusMeasure d, Tendsto (fun n => u (φ n) x) atTop (𝓝 (v x))) ∧
      (∀ ε > 0, ∀ᶠ n in atTop, potentialEnergy v ≤ potentialEnergy (u (φ n)) + ε) := by
  have hc : 0 < (2 * Real.pi) ^ d := pow_pos (by positivity) d
  have hE0 : 0 ≤ E := (potentialEnergy_nonneg (u 0)).trans (hE 0)
  set B : ℝ := E / (2 * Real.pi) ^ d with hB
  have hB0 : 0 ≤ B := div_nonneg hE0 hc.le
  let P : ℕ → TorusL2 d := fun n => Bridge.potentialLp (u n) (hu n).1
  have hcrit : ∀ n, CriticalSobolev (P n) := by
    intro n
    refine ⟨?_, Bridge.potentialLp_summable hd (u n) (hu n)⟩
    rw [Bridge.potentialLp_fourier]
    exact BecknerOnofri.V2.Onset.fourierCoeff_zero_meanZero (hm n)
  have hen : ∀ n, criticalEnergy (P n) = potentialEnergy (u n) / (2 * Real.pi) ^ d := by
    intro n
    show criticalEnergy (Bridge.potentialLp (u n) (hu n).1) = _
    rw [Bridge.potentialLp_energy hd (u n) (hu n)]
    field_simp
  have hball : ∀ n, P n ∈ realSobolevBall d B := by
    intro n
    refine ⟨⟨hcrit n, ?_⟩, Bridge.potentialLp_real _ _⟩
    rw [hen n, hB]
    exact div_le_div_of_nonneg_right (hE n) hc.le
  obtain ⟨v, hv, φ, hφ, hlim⟩ := (realSobolevBall_isCompact hd hB0).isSeqCompact hball
  have hvadm : Admissible v := ⟨hv.2, hv.1.1⟩
  have hL2 := eLpNorm_tendsto (u := fun n => u (φ n)) (fun n => (hu (φ n)).1) v hv.2 hlim
  set w : Torus d → ℝ := RawAttainment.realValue v with hw
  have hwmem : MemLp w 2 (torusMeasure d) := RawAttainment.realValue_memLp v
  have hmeas : TendstoInMeasure (torusMeasure d) (fun n => u (φ n)) atTop w := by
    exact tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num) hL2
  obtain ⟨ψ, hψ, hae⟩ := hmeas.exists_seq_tendsto_ae
  refine ⟨φ ∘ ψ, w, hφ.comp hψ, RawAttainment.realValue_sobolev v hvadm,
    RawAttainment.realValue_meanZero v hvadm, ?_, hae, ?_⟩
  · exact hL2.comp hψ.tendsto_atTop
  · intro ε hε
    have hlsc := energy_lowerSemicontinuousOn d B v hv
    have hnh : Tendsto (fun n => P (φ (ψ n))) atTop (nhdsWithin v (realSobolevBall d B)) :=
      tendsto_nhdsWithin_iff.mpr ⟨(hlim.comp hψ.tendsto_atTop), Eventually.of_forall fun n => hball _⟩
    have hlt : criticalEnergy v - ε / (2 * Real.pi) ^ d < criticalEnergy v := by
      have : 0 < ε / (2 * Real.pi) ^ d := div_pos hε hc
      linarith
    filter_upwards [hnh.eventually (hlsc _ hlt)] with n hn
    rw [hen] at hn
    have hwe : potentialEnergy w = (2 * Real.pi) ^ d * criticalEnergy v :=
      RawAttainment.realValue_energy hd v hvadm
    rw [hwe]
    have : criticalEnergy v < potentialEnergy (u (φ (ψ n))) / (2 * Real.pi) ^ d + ε / (2 * Real.pi) ^ d := by
      linarith
    rw [← add_div, lt_div_iff₀ hc] at this
    simp only [Function.comp_apply]
    nlinarith

end BecknerOnofri.V2.Reaudit.Attainment
