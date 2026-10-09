module

public import BecknerOnofri.V2.Onset.UniformBounds
public import BecknerOnofri.V2.Onset.Compactness
public import BecknerOnofri.V2.Onset.Continuity
public import BecknerOnofri.V2.Onset.Inputs
public import BecknerOnofri.ContinuousOptimizers

@[expose] public section

/-! # Sobolev smallness of near-threshold optimizers (Proposition 5.24)

Manuscript route: uniform bounds (`UniformBounds`) feed the Euler/Sobolev-algebra bootstrap, which gives
bounds in every `H^{(m+1)d}`; Sobolev compactness (`Compactness`) extracts a limit in every fixed
`H^r`; the dual functional is upper semicontinuous (`Continuity`), so the limit has `Φ_1 ≥ 0`;
the spectral inequality with its rigidity (`OnsetEndpointInputs`) forces the limit to vanish.  An
argument by contradiction then gives uniform smallness in each fixed `H^r`
(`eq:section5-onset-uniform-convergence`). -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped Topology

namespace BecknerOnofri.V2.Onset
open BecknerOnofri.HighDim ContinuousGibbs ContinuousFirstShell
open Legacy.BecknerOnofri.SubcriticalAttainment Legacy.BecknerOnofri.TorusSobolev
open BecknerOnofri.HighDim.LocalEleven.ContinuousEnergy

/-- `Φ_μ(u) = functional (1/(2μ)) (toL2 u)` for mean-zero critical `u`. -/
theorem value_eq_functional {d : ℕ} (hd : 0 < d) {μ : ℝ} (hμ : 0 < μ) (u : Space d)
    (hu : InCriticalSobolev ⇑u) (hm : MeanZero ⇑u) :
    value μ u = functional (1 / (2 * μ)) (toL2 d u) := by
  have hσ : spectralThreshold d ≠ 0 := (Legacy.TorusEndpoint.endpointSigma_pos hd).ne'
  have h1 := value_eq_dual hd μ u hm
  have h2 := ContinuousOptimizers.dualFunctional_eq_toL2 hd (μ * spectralThreshold d) u hu hm
  rw [h1] at h2
  have h3 : spectralThreshold d / (2 * (μ * spectralThreshold d)) = 1 / (2 * μ) := by
    field_simp
  rw [h3] at h2
  exact_mod_cast h2

theorem value_nonneg_of_maximizer {d : ℕ} (hd : 0 < d) {μ : ℝ} (hμ : 0 < μ) (u : Space d)
    (hu : InCriticalSobolev ⇑u) (hm : MeanZero ⇑u)
    (hmax : ∀ v : Torus d → ℝ, InCriticalSobolev v →
      dualFunctional (μ * spectralThreshold d) v ≤ dualFunctional (μ * spectralThreshold d) ⇑u) :
    0 ≤ value μ u := by
  have hσ : 0 < spectralThreshold d := Legacy.TorusEndpoint.endpointSigma_pos hd
  obtain ⟨_, hUmax⟩ := legacy_maximizer hd u hu hm hmax
  have h := hUmax 0 (admissible_zero d)
  have h3 : spectralThreshold d / (2 * (μ * spectralThreshold d)) = 1 / (2 * μ) := by
    field_simp
  rw [h3] at h
  rw [value_eq_functional hd hμ u hu hm]
  simpa using h

/-- **Rigidity at the endpoint, in `C(𝕋ᵈ)` vocabulary**: a critical mean-zero continuous `v` with
`Φ_1(v) ≥ 0` vanishes, given the spectral inequality and its equality case. -/
theorem zero_of_value_nonneg {d : ℕ} (hd : 0 < d) (E : OnsetEndpointInputs d) (v : Space d)
    (hv : InCriticalSobolev ⇑v) (hm : MeanZero ⇑v) (h : 0 ≤ value 1 v) : v = 0 := by
  have hf : 0 ≤ functional (1 / 2 : ℝ) (toL2 d v) := by
    have := value_eq_functional hd one_pos v hv hm
    rw [show (1 : ℝ) / (2 * 1) = 1 / 2 by norm_num] at this
    rw [← this]; exact h
  have h0 := OnsetCompactness.zero_of_endpoint_nonneg hd E.inequality.toCoefficientEndpoint
    (E.rigidity.toDensityRigidity E.inequality)
    (OnsetContinuous.toL2_admissible hd v hv hm) hf
  have : (torusMeasure d).IsOpenPosMeasure := by
    change (Legacy.TorusEndpoint.torusMeasure d).IsOpenPosMeasure
    rw [Legacy.TorusEndpoint.torusMeasure_explicit]; infer_instance
  have hae : (⇑v : Torus d → ℝ) =ᵐ[torusMeasure d] 0 := by
    filter_upwards [toL2_ae v, Lp.coeFn_zero ℂ 2 (torusMeasure d)] with x hx h0x
    have : (toL2 d v) x = 0 := by rw [h0]; exact h0x
    rw [hx] at this
    exact_mod_cast this
  have := (Continuous.ae_eq_iff_eq (torusMeasure d) v.continuous continuous_zero).mp hae
  exact ContinuousMap.ext fun x => congrFun this x

/-- **Uniform Sobolev smallness of near-threshold optimizers**
(`eq:section5-onset-uniform-convergence`): for every `r ≥ 0` and `ε > 0`, all continuous global
maximizers at couplings `μ β_s` with `μ` close to `1` have `‖u‖_{H^r} < ε`.  The only conditional
input is `OnsetEndpointInputs d` (Corollary 5.8). -/
theorem optimizers_sobolev_small {d : ℕ} (hd : 12 ≤ d) (E : OnsetEndpointInputs d) {r : ℝ}
    (hr : 0 ≤ r) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ μ in 𝓝 (1 : ℝ), ∀ u : Space d, InCriticalSobolev ⇑u → MeanZero ⇑u →
      (∀ v : Torus d → ℝ, InCriticalSobolev v →
        dualFunctional (μ * spectralThreshold d) v ≤ dualFunctional (μ * spectralThreshold d) ⇑u) →
      InSobolev r ⇑u ∧ sobolevNorm r ⇑u < ε := by
  classical
  have hd0 : 0 < d := by omega
  obtain ⟨M, Eb, hM⟩ := uniform_density_bound hd
  obtain ⟨B, hB⟩ := uniform_sobolev_bound hd
  by_contra hn
  have hf : ∃ᶠ μ in 𝓝 (1 : ℝ), ∃ u : Space d, InCriticalSobolev ⇑u ∧ MeanZero ⇑u ∧
      (∀ v : Torus d → ℝ, InCriticalSobolev v →
        dualFunctional (μ * spectralThreshold d) v ≤ dualFunctional (μ * spectralThreshold d) ⇑u) ∧
      ¬(InSobolev r ⇑u ∧ sobolevNorm r ⇑u < ε) := by
    simpa only [Filter.Frequently, not_exists, not_and, not_forall, Classical.not_imp,
      not_not, exists_prop] using hn
  obtain ⟨μ, hμ, hbad⟩ := exists_seq_forall_of_frequently hf
  choose u hu hm hmax hbad' using hbad
  have hev : ∀ᶠ n in atTop, 0 < μ n ∧ _ ∧ _ :=
    hμ.eventually ((lt_mem_nhds one_pos).and (hM.and hB))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  have hμ' : Tendsto (fun n => μ (n + N)) atTop (𝓝 1) := hμ.comp (tendsto_add_atTop_nat N)
  have hpos : ∀ n, 0 < μ (n + N) := fun n => (hN (n + N) (Nat.le_add_left _ _)).1
  have hb' : ∀ n (m : ℕ), InSobolev (((m : ℝ) + 1) * d) ⇑(u (n + N)) ∧
      sobolevNorm (((m : ℝ) + 1) * d) ⇑(u (n + N)) ≤ B m := fun n m =>
    (hN (n + N) (Nat.le_add_left _ _)).2.2 (u (n + N)) (hu _) (hm _) (hmax _) m
  have hE' : ∀ n, criticalEnergy (toL2 d (u (n + N))) ≤ Eb := fun n =>
    ((hN (n + N) (Nat.le_add_left _ _)).2.1 (u (n + N)) (hu _) (hm _) (hmax _)).2
  obtain ⟨φ, hφ, v, hvm, -, hconv⟩ := sobolev_subsequence_limit hd0 B Eb (fun n => u (n + N))
    (fun n => hu _) (fun n => hm _) hE' hb'
  obtain ⟨hd1, hd2⟩ := hconv (d : ℝ) (Nat.cast_nonneg d)
  have hlim := limit_value_nonneg hd0 (fun n => μ (φ n + N)) (fun n => u (φ n + N)) v
    (hμ'.comp hφ.tendsto_atTop) (fun n => hu _) hd1 hd2
    (fun n => value_nonneg_of_maximizer hd0 (hpos (φ n)) (u (φ n + N)) (hu _) (hm _) (hmax _))
  have hv0 : v = 0 := zero_of_value_nonneg hd0 E v hlim.1 hvm hlim.2
  subst hv0
  obtain ⟨hr1, hr2⟩ := hconv r hr
  simp only [ContinuousMap.coe_zero, sub_zero] at hr1 hr2
  have hsmall := hr2.eventually (gt_mem_nhds hε)
  obtain ⟨n, hn⟩ := hsmall.exists
  exact hbad' (φ n + N) ⟨hr1 n, hn⟩

end BecknerOnofri.V2.Onset
