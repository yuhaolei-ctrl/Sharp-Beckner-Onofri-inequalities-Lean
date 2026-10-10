module

public import BecknerOnofri.V2.Reaudit.SobolevQuartic.Parameter
public import BecknerOnofri.V2.Reaudit.SobolevQuartic.Symmetry
public import BecknerOnofri.AnalyticEvenOrder
public import BecknerOnofri.LocalElevenCore.ReducedQuarticAnalytic

@[expose] public section

/-! # `lem:section5-quartic-reduction` (S054), native in `H^s`

Assembly of the three assertions of the lemma for the Sobolev graph `graph hd11`, **without** the
identification of the `H^s` graph with the sup-norm graph (`Branch.graph_toComplement` is not used,
not even imported):

1. `∫ v³ = 0` (`eq:section5-no-cubic-resonance`): reused finite-dimensional moment
   `QuadraticModes.assembly_third_moment`;
2. the quadratic term `w_2` (`quadraticTermNative`) with the explicit Fourier coefficients and
   `w(1,z) - w_2(z) = O(‖z‖³)` in `H^s` (`Slaving.lean`);
3. `Φ_{d,τ}(v + w(τ,v)) = δ S + Q_{4,d} + O(S³ + |δ| S²)` (`eq:section5-reduced-expansion`):

   `Θ(1,z) - Q_4(z) = O(‖z‖⁵)` (`Expansion.lean`, from the native `logZ_taylor` and
   `gibbs_slice_expansion`), improved to `O(‖z‖⁶)` by evenness (`Symmetry.lean`) and analyticity;
   `Θ(τ,z) - Θ(1,z) = O(|τ-1| ‖z‖⁴)` (`Parameter.lean`); and
   `‖z‖⁶ + |τ-1|‖z‖⁴ = O(S³ + |δ|S²)`. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter Asymptotics
open scoped ENNReal Topology

namespace BecknerOnofri.V2.Reaudit.SobolevQuartic
open BecknerOnofri.V2.Reaudit.Sobolev BecknerOnofri.HighDim ContinuousGibbs ContinuousFirstShell
  ContinuousComplement

variable {d : ℕ} {s : ℝ} [SobolevIndex d s]

/-! ## Analyticity of the slice functional -/

theorem mass_analytic {σ : ℝ} [SobolevIndex d σ] :
    AnalyticAt ℝ (fun z : Coordinates d => LocalReductionStatement.mass z) 0 := by
  have h : AnalyticAt ℝ (fun z : Coordinates d =>
      Hs.meanCLM d σ ((Hs.assemblyH d σ z) ^ 2) / 2) 0 :=
    (((Hs.meanCLM d σ).analyticAt _).comp
      (f := fun z : Coordinates d => (Hs.assemblyH d σ z) ^ 2)
      (((Hs.assemblyH d σ).analyticAt (0 : Coordinates d)).pow 2)).div_const
  refine h.congr (Eventually.of_forall fun z => ?_)
  have := pk_two_assemblyH (s := σ) z
  unfold pk at this
  show _ = LocalReductionStatement.mass z
  linarith

theorem logZ_analytic (u : Hs d s) : AnalyticAt ℝ (fun v : Hs d s => logZ v) u := by
  unfold logZ
  exact (analyticAt_log (Hs.partition_pos u)).comp (f := fun v : Hs d s => Hs.partition v)
    (Hs.partition_analytic u)

theorem Lfun_wS_analytic (hd11 : 11 ≤ d) :
    AnalyticAt ℝ (fun z : Coordinates d => Lfun z (wS (s := s) hd11 z)) 0 := by
  have hg : AnalyticAt ℝ (fun z : Coordinates d => graph (s := s) hd11 (1, z)) 0 :=
    (graph_analytic (s := s) hd11).comp (f := fun z : Coordinates d => ((1 : ℝ), z))
      (analyticAt_const.prod analyticAt_id)
  have hw : AnalyticAt ℝ (fun z : Coordinates d => wS (s := s) hd11 z) 0 :=
    ((HsC d s).subtypeL.analyticAt _).comp (f := fun z : Coordinates d => graph (s := s) hd11 (1, z)) hg
  have hv : AnalyticAt ℝ (fun z : Coordinates d => Hs.assemblyH d s z) 0 :=
    (Hs.assemblyH d s).analyticAt 0
  have hU : AnalyticAt ℝ (fun z : Coordinates d => Hs.assemblyH d s z + wS (s := s) hd11 z) 0 :=
    hv.add hw
  have hlog : AnalyticAt ℝ (fun z : Coordinates d => logZ (Hs.assemblyH d s z + wS (s := s) hd11 z)) 0 :=
    (logZ_analytic _).comp (f := fun z : Coordinates d => Hs.assemblyH d s z + wS (s := s) hd11 z) hU
  have hgib : AnalyticAt ℝ (fun z : Coordinates d =>
      Hs.gibbs (Hs.assemblyH d s z + wS (s := s) hd11 z)) 0 :=
    (Hs.gibbs_analytic _).comp (f := fun z : Coordinates d => Hs.assemblyH d s z + wS (s := s) hd11 z) hU
  have hm : AnalyticAt ℝ (fun z : Coordinates d => Hs.meanCLM d s (wS (s := s) hd11 z *
      Hs.gibbs (Hs.assemblyH d s z + wS (s := s) hd11 z))) 0 :=
    ((Hs.meanCLM d s).analyticAt _).comp (f := fun z : Coordinates d => wS (s := s) hd11 z *
      Hs.gibbs (Hs.assemblyH d s z + wS (s := s) hd11 z)) (hw.mul hgib)
  exact (hlog.sub (mass_analytic (σ := s))).sub (analyticAt_const.mul hm) |>.congr (Eventually.of_forall fun z => rfl)

theorem quartic_analytic (hd11 : 11 ≤ d) :
    AnalyticAt ℝ (fun z : Coordinates d => LocalReductionStatement.quartic z) 0 :=
  BecknerOnofri.HighDim.LocalEleven.ReducedQuarticExpansion.quarticValue_analytic hd11

theorem quartic_neg (z : Coordinates d) :
    LocalReductionStatement.quartic (-z) = LocalReductionStatement.quartic z := by
  simp [LocalReductionStatement.quartic]

/-! ## The sixth-order remainder at `τ = 1` -/

/-- `Θ(1, z) = Q_{4,d}(z) + O(‖z‖⁶)`: the fifth-order term vanishes since `Θ(1,·) - Q_4` is
analytic and even. -/
theorem theta_one_sixth (hd11 : 11 ≤ d) :
    (fun z : Coordinates d => Lfun z (wS (s := s) hd11 z) - LocalReductionStatement.quartic z)
      =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖ ^ 6) := by
  refine BecknerOnofri.analytic_even_fifth_order ((Lfun_wS_analytic hd11).sub (quartic_analytic hd11))
    (theta_one_quartic hd11) ?_
  filter_upwards [theta_one_even (s := s) hd11] with z hz
  simp only [quartic_neg, hz]

/-! ## The two-parameter remainder -/

theorem parameter_delta_bound :
    ∀ᶠ μ : ℝ in 𝓝 1, |μ - 1| ≤ 2 * |1 - 1 / μ| := by
  filter_upwards [Icc_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)
    (by norm_num : (1 : ℝ) < 2)] with μ hμ
  have hp : 0 < μ := by linarith [hμ.1]
  have he : μ - 1 = μ * (1 - 1 / μ) := by field_simp [hp.ne']
  rw [he, abs_mul, abs_of_pos hp]
  exact mul_le_mul_of_nonneg_right hμ.2 (abs_nonneg _)

theorem norm_sq_le_mass (z : Coordinates d) : ‖z‖ ^ 2 ≤ LocalReductionStatement.mass z := by
  have hs : 0 ≤ LocalReductionStatement.mass z := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hn : ‖z‖ ≤ Real.sqrt (LocalReductionStatement.mass z) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro i
    exact Real.le_sqrt_of_sq_le
      (Finset.single_le_sum (fun j _ => sq_nonneg ‖z j‖) (Finset.mem_univ i))
  nlinarith [Real.sq_sqrt hs, Real.sqrt_nonneg (LocalReductionStatement.mass z), norm_nonneg z]

/-- `‖z‖⁶ + |τ-1| ‖z‖⁴ = O(S³ + |δ| S²)`, `δ = 1 - 1/τ`, `S = Σ|z_j|²`. -/
theorem joint_remainder (d : ℕ) :
    (fun x : ℝ × Coordinates d => ‖x.2‖ ^ 6 + |x.1 - 1| * ‖x.2‖ ^ 4)
      =O[𝓝 (1, 0)] (fun x => (LocalReductionStatement.mass x.2) ^ 3 +
        |1 - 1 / x.1| * (LocalReductionStatement.mass x.2) ^ 2) := by
  apply IsBigO.of_bound 2
  have ht : Tendsto (Prod.fst : ℝ × Coordinates d → ℝ) (𝓝 (1, 0)) (𝓝 1) :=
    continuous_fst.continuousAt
  filter_upwards [ht.eventually parameter_delta_bound] with x hx
  have hS : 0 ≤ LocalReductionStatement.mass x.2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hnorm := norm_sq_le_mass x.2
  have h4 : ‖x.2‖ ^ 4 ≤ (LocalReductionStatement.mass x.2) ^ 2 := by
    simpa only [← pow_mul] using pow_le_pow_left₀ (sq_nonneg ‖x.2‖) hnorm 2
  have h6 : ‖x.2‖ ^ 6 ≤ (LocalReductionStatement.mass x.2) ^ 3 := by
    simpa only [← pow_mul] using pow_le_pow_left₀ (sq_nonneg ‖x.2‖) hnorm 3
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  have hm := mul_le_mul hx h4 (by positivity) (by positivity : 0 ≤ 2 * |1 - 1 / x.1|)
  nlinarith [pow_nonneg hS 3]

/-- **`eq:section5-reduced-expansion`, native**: `Θ(τ, z) = Q_{4,d}(z) + O(S³ + |δ| S²)`. -/
theorem theta_quartic_paper (hd11 : 11 ≤ d) :
    (fun x : ℝ × Coordinates d => Theta (s := s) hd11 x - LocalReductionStatement.quartic x.2)
      =O[𝓝 ((1 : ℝ), (0 : Coordinates d))] (fun x => (LocalReductionStatement.mass x.2) ^ 3 +
        |1 - 1 / x.1| * (LocalReductionStatement.mass x.2) ^ 2) := by
  have h6 : (fun x : ℝ × Coordinates d => Lfun x.2 (wS (s := s) hd11 x.2) -
      LocalReductionStatement.quartic x.2) =O[𝓝 ((1 : ℝ), (0 : Coordinates d))]
      (fun x => ‖x.2‖ ^ 6) := (theta_one_sixth (s := s) hd11).comp_tendsto (snd_tendsto (d := d))
  have h1 := theta_param_difference (s := s) hd11
  have a6 : (fun x : ℝ × Coordinates d => ‖x.2‖ ^ 6) =O[𝓝 ((1 : ℝ), (0 : Coordinates d))]
      (fun x => ‖x.2‖ ^ 6 + |x.1 - 1| * ‖x.2‖ ^ 4) := by
    apply IsBigO.of_bound 1
    filter_upwards with x
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
    have : 0 ≤ |x.1 - 1| * ‖x.2‖ ^ 4 := by positivity
    linarith
  have a1 : (fun x : ℝ × Coordinates d => |x.1 - 1| * ‖x.2‖ ^ 4) =O[𝓝 ((1 : ℝ), (0 : Coordinates d))]
      (fun x => ‖x.2‖ ^ 6 + |x.1 - 1| * ‖x.2‖ ^ 4) := by
    apply IsBigO.of_bound 1
    filter_upwards with x
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
    have : 0 ≤ ‖x.2‖ ^ 6 := by positivity
    linarith
  have h := ((h6.trans a6).add (h1.trans a1)).trans (joint_remainder d)
  refine h.congr_left fun x => ?_
  simp only [Theta, wS]
  ring

/-! ## The statement of `lem:section5-quartic-reduction` -/

open LocalReductionStatement in
/-- The three assertions of `lem:section5-quartic-reduction` for a complement graph
`ψ : ℝ × ℂ^d → K^⊥ ⊂ H^s` (verbatim the statement of `Sobolev.Section5QuarticReduction`):

1. `∫ v³ = 0`  (`eq:section5-no-cubic-resonance`);
2. the quadratic term of `w(1, v)` has the explicit Fourier coefficients
   `1/(2(|k|^d - 1)) \widehat{v²}(k)` on `K^⊥`-frequencies (`eq:section5-quadratic-slaving`), and
   `w(1, z) - w_2(z) = O(‖z‖³)` in `H^s` (`eq:section5-complement-Taylor-expansions`);
3. `Φ_{d,τ}(v + w(τ, v)) = δ S + Q_{4,d} + O(S³ + |δ| S²)`, `δ = 1 - 1/τ`, `S = Σ |z_j|²`
   (`eq:section5-reduced-expansion`). -/
def QuarticReductionNative (d : ℕ) (s : ℝ) [SobolevIndex d s]
    (ψ : ℝ × Coordinates d → HsC d s) : Prop :=
  (∀ z : Coordinates d, mean d ((assembly d z) ^ 3) = 0) ∧
  (∃ q : Coordinates d → HsC d s,
    QuadraticSlavingCoefficients (fun z => HsC.toComplement d s (q z)) ∧
    ((fun z : Coordinates d => ‖ψ (1, z) - q z‖) =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖ ^ 3))) ∧
  ((fun x : ℝ × Coordinates d =>
      (dualFunctional (x.1 * spectralThreshold d) (Hs.reconstructionH d s (x.2, ψ x)).val).toReal -
        (1 - 1 / x.1) * mass x.2 - quartic x.2)
    =O[𝓝 (1, (0 : Coordinates d))] (fun x => mass x.2 ^ 3 + |1 - 1 / x.1| * mass x.2 ^ 2))

open LocalReductionStatement in
/-- **S054, `lem:section5-quartic-reduction`, native in `H^s`** (`d ≥ 11`, `s > d/2`): all three
assertions for the Sobolev graph `graph hd11`, derived from the Sobolev-space expansions without
the sup-norm graph. -/
theorem section5_quartic_reduction_native (hd11 : 11 ≤ d) :
    QuarticReductionNative d s (graph (s := s) hd11) := by
  refine ⟨fun z => BecknerOnofri.HighDim.LocalEleven.QuadraticModes.assembly_third_moment z, ?_, ?_⟩
  · refine ⟨quadraticTermNative hd11, ?_, ?_⟩
    · classical
      intro z k
      rw [← coefficient_eq_fourierCoeff, ← coefficient_eq_fourierCoeff]
      exact quadraticTermNative_coeff (s := s) hd11 z k
    · exact (graph_one_sub_quadratic (s := s) hd11).norm_left
  · have h := theta_quartic_paper (s := s) hd11
    refine h.congr' ?_ (Eventually.of_forall fun _ => rfl)
    filter_upwards [dual_sub_eq_Theta (s := s) hd11] with x hx
    rw [← hx]

end BecknerOnofri.V2.Reaudit.SobolevQuartic
