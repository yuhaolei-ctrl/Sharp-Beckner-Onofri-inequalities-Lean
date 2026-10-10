module

public import BecknerOnofri.V2.Reaudit.MorseBott.TranslateInvariance
public import BecknerOnofri.LocalElevenCore.SupportedFullIdentification
public import BecknerOnofri.LocalElevenCore.SupportedDeltaExhaustiveness
public import BecknerOnofri.RawSubspectralLocalUniqueness
public import BecknerOnofri.GeneralSobolevEmbedding
public import BecknerOnofri.OptimizerTranslation

@[expose] public section

/-! # The local critical set near the full-support branch is the translation orbit

Let `u = branch univ δ` be the full-support branch (all first-shell coefficients nonzero).  Every
critical point `v ∈ H^s` (`s > d/2`) which is `H^s`-close to `u` is a translate of `u`.  This uses the
existing local classification `small_solution_branch` of small critical points (sup-norm
neighbourhood of `(1, 0)`), which fixes the common amplitude, together with the embedding
`H^s ⊂ C⁰`. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped Topology BigOperators

namespace BecknerOnofri.V2.Reaudit.MorseBott
open BecknerOnofri.HighDim BecknerOnofri.HighDim.LocalEleven

theorem exists_ball_critical {d : ℕ} (hd : 11 ≤ d) {s : ℝ} (hs : (d : ℝ) / 2 < s) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∃ ρ : ℝ, 0 < ρ ∧ ∀ v : Torus d → ℝ, InSobolev s v → MeanZero v →
      IsCritical (1 / (1 - δ)) v →
      InSobolev s (fun x => v x - SupportedFamily.branch hd Finset.univ δ x) →
      sobolevNorm s (fun x => v x - SupportedFamily.branch hd Finset.univ δ x) < ρ →
      ∃ a : Torus d, v =ᵐ[torusMeasure d] translate (SupportedFamily.branch hd Finset.univ δ) a := by
  have hd0 : 0 < d := by omega
  obtain ⟨ε, hε, hlocal⟩ := Metric.eventually_nhds_iff.mp (SupportedFamily.small_solution_branch hd)
  set C := ‖SobolevEmbedding.inverseScaleLp hd0 hs‖ with hCdef
  have hC : 0 ≤ C := norm_nonneg _
  have hδ1 : Tendsto (fun δ : ℝ => 1 / (1 - δ)) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have : ContinuousAt (fun δ : ℝ => 1 / (1 - δ)) 0 :=
      continuousAt_const.div (continuousAt_const.sub continuousAt_id) (by norm_num)
    simpa using this.tendsto.mono_left nhdsWithin_le_nhds
  have hprof : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ I : Finset (Fin d), I.Nonempty →
      (∀ j : Fin d, fourierCoeff (SupportedFamily.branch hd I δ) (axisFrequency j) =
        if j ∈ I then ((Real.sqrt (SupportedFamily.amplitude hd I.card δ)) : ℂ) else 0) ∧
      (∀ j : Fin d, fourierCoeff (SupportedFamily.branch hd I δ) (axisFrequency j) ≠ 0 ↔ j ∈ I) ∧
      0 < SupportedFamily.amplitude hd I.card δ := by
    apply eventually_all.mpr
    intro I
    by_cases hI : I.Nonempty
    · filter_upwards [(SupportedFamily.branch_profile hd I hI).1.2] with δ h _
      exact ⟨h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2, h.1⟩
    · exact Eventually.of_forall (fun δ h => (hI h).elim)
  have hsmall : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ‖SupportedFamily.branch hd Finset.univ δ‖ < ε / 2 := by
    have := (SupportedFamily.branch_profile hd Finset.univ ⟨⟨0, hd0⟩, Finset.mem_univ _⟩).1.1
    exact this.eventually (Metric.ball_mem_nhds 0 (half_pos hε)) |>.mono
      (fun δ h => by simpa using h)
  filter_upwards [hprof, hsmall, hδ1.eventually (Metric.ball_mem_nhds 1 hε), self_mem_nhdsWithin,
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)).filter_mono nhdsWithin_le_nhds]
    with δ hpr hsm hμ hδpos hδhalf
  have hδpos' : 0 < δ := hδpos
  obtain ⟨hco, hnz, hamp⟩ := hpr Finset.univ ⟨⟨0, hd0⟩, Finset.mem_univ _⟩
  set u := SupportedFamily.branch hd Finset.univ δ with hu
  set m := Real.sqrt (SupportedFamily.amplitude hd (Finset.univ : Finset (Fin d)).card δ) with hm
  have hmpos : 0 < m := Real.sqrt_pos.mpr hamp
  have hcoef : ∀ j : Fin d, fourierCoeff u (axisFrequency j) = (m : ℂ) := by
    intro j; rw [hco j]; simp
  refine ⟨min (ε / 2 / (C + 1)) (m / 2 / (C + 1)), lt_min (by positivity) (by positivity), ?_⟩
  intro v hSv hmv hcv hSw hn
  set w : Torus d → ℝ := fun x => v x - u x with hw
  obtain ⟨wc, hwc, hwcS, hwcn⟩ := SobolevEmbedding.exists_continuous_representative hd0 hs w hSw
  have hnε : ‖wc‖ < ε / 2 := by
    have h1 : sobolevNorm s w < ε / 2 / (C + 1) := hn.trans_le (min_le_left _ _)
    have h2 := (lt_div_iff₀ (by positivity : 0 < C + 1)).mp h1
    have hN : 0 ≤ sobolevNorm s w := Real.sqrt_nonneg _
    nlinarith
  have hnm : C * sobolevNorm s w < m / 2 := by
    have h1 : sobolevNorm s w < m / 2 / (C + 1) := hn.trans_le (min_le_right _ _)
    have h2 := (lt_div_iff₀ (by positivity : 0 < C + 1)).mp h1
    have hN : 0 ≤ sobolevNorm s w := Real.sqrt_nonneg _
    nlinarith
  -- the continuous representative of `v`
  let vc : ContinuousGibbs.Space d := u + wc
  have hvc : (vc : Torus d → ℝ) =ᵐ[torusMeasure d] v := by
    filter_upwards [hwc] with x hx
    simp only [vc, ContinuousMap.add_apply, hx, hw]
    ring
  have hmvc : MeanZero (vc : Torus d → ℝ) := (integral_congr_ae hvc).trans hmv
  have heq : LocalEleven.ReducedEquation.full d (1 / (1 - δ)) vc = 0 := by
    apply (LocalEleven.ReducedEquation.full_zero_iff_stationary hd0 _ vc).mpr
    refine ⟨hmvc, fun k => ?_⟩
    rw [HighDim.fourierCoeff_congr_ae hvc,
      HighDim.fourierCoeff_congr_ae (HighDim.RawSubspectralLocalUniqueness.gibbs_congr_ae hvc)]
    have := hcv k
    simpa only [Complex.ofReal_pow] using this
  -- the first-shell coefficients of `vc` are close to those of `u`
  have hcoefvc : ∀ j : Fin d, m / 2 < ‖ContinuousFirstShell.coefficient (axisFrequency j) vc‖ := by
    intro j
    have hlin : ContinuousFirstShell.coefficient (axisFrequency j) vc =
        (m : ℂ) + ContinuousFirstShell.coefficient (axisFrequency j) wc := by
      simp only [vc, map_add]
      rw [ContinuousFirstShell.coefficient_eq_fourierCoeff (axisFrequency j) u, hcoef j]
    have hwj : ‖ContinuousFirstShell.coefficient (axisFrequency j) wc‖ ≤ C * sobolevNorm s w := by
      rw [ContinuousFirstShell.coefficient_eq_fourierCoeff, HighDim.fourierCoeff_congr_ae hwc]
      refine le_trans ?_ (SobolevEmbedding.fourier_sum_bound hd0 hs w hSw)
      exact (SobolevEmbedding.fourier_summable hd0 hs w hSw).le_tsum (axisFrequency j)
        (fun k _ => norm_nonneg _)
    rw [hlin]
    have : ‖(m : ℂ)‖ - ‖ContinuousFirstShell.coefficient (axisFrequency j) wc‖ ≤
        ‖(m : ℂ) + ContinuousFirstShell.coefficient (axisFrequency j) wc‖ := by
      have := norm_sub_norm_le (m : ℂ) (-(ContinuousFirstShell.coefficient (axisFrequency j) wc))
      simpa [sub_eq_add_neg] using this
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hmpos] at this
    linarith
  have hvcne : vc ≠ 0 := by
    intro h0
    have := hcoefvc ⟨0, hd0⟩
    rw [h0, map_zero, norm_zero] at this
    linarith
  have hnear : dist ((1 / (1 - δ), vc) : ℝ × ContinuousGibbs.Space d) (1, 0) < ε := by
    rw [Prod.dist_eq, max_lt_iff]
    refine ⟨by simpa [Real.dist_eq] using hμ, ?_⟩
    rw [dist_zero_right]
    calc ‖vc‖ ≤ ‖u‖ + ‖wc‖ := norm_add_le _ _
      _ < ε / 2 + ε / 2 := add_lt_add hsm hnε
      _ = ε := by ring
  have hlocal' := hlocal hnear hmvc heq hvcne
  obtain ⟨-, I, hIne, a, hvca⟩ := hlocal'
  have hδeq : 1 - 1 / (1 / (1 - δ)) = δ := by
    have h1 : (1 - δ) ≠ 0 := by
      have : δ < 1 / 2 := hδhalf
      linarith
    field_simp
    ring
  rw [hδeq] at hvca
  have hvca' : vc = ContinuousSymmetry.translation a (SupportedFamily.branch hd I δ) := hvca
  -- the support is full
  have hcoefvc' : ∀ j : Fin d, fourierCoeff (vc : Torus d → ℝ) (axisFrequency j) ≠ 0 := by
    intro j h0
    have := hcoefvc j
    rw [ContinuousFirstShell.coefficient_eq_fourierCoeff, h0, norm_zero] at this
    linarith
  have hIuniv : I = Finset.univ := by
    rw [Finset.eq_univ_iff_forall]
    intro j
    have h1 := hcoefvc' j
    rw [hvca', OptimizerTranslation.coe_translation] at h1
    exact ((hpr I hIne).2.1 j).mp (by simpa using h1)
  subst hIuniv
  refine ⟨a, ?_⟩
  have := hvc.symm
  rw [hvca', OptimizerTranslation.coe_translation] at this
  exact this

end BecknerOnofri.V2.Reaudit.MorseBott

#print axioms BecknerOnofri.V2.Reaudit.MorseBott.exists_ball_critical
