module

public import BecknerOnofri.V2.Reaudit.SobolevQuartic.Uniform
public import BecknerOnofri.LocalElevenCore.ReducedParameterDerivative
public import BecknerOnofri.LocalElevenCore.GraphEnergy
public import BecknerOnofri.ParameterMeanValue

@[expose] public section

/-! # The parameter dependence of the reduced functional

The remainder bookkeeping of `eq:section5-reduced-expansion`: the manuscript's last paragraph
("varying `τ` changes the quartic coefficients by `O(|δ|)`") is implemented as follows.  With the
Euler form `Θ(τ, z) = L_z(w(τ, z))` (`Expansion.lean`) one has, natively in `H^s`:

* `Theta_eq_dual`: `Φ_{d,τ}(v + w(τ,v)) = Θ(τ, z) + (1 - 1/τ) S`  (the energy is eliminated with
  the Euler equation; the only reused ingredient is the finite-dimensional Fourier identity
  `GraphEnergy.graph_dualFunctional`);
* `Theta_hasDerivAt`: `∂_τ Θ(τ, z) = (2τ)^{-1} ∫ w ρ_{v+w}`;
* `integral_w_rho_isBigO`: `∫ w ρ_{v+w} = ∫ w (ρ_{v+w} - 1 - v) = O(‖z‖⁴)` uniformly in `τ` (here the
  uniform bound `graph_uniform` and the second order Gibbs expansion are used);
* `theta_param_difference`: `Θ(τ, z) - Θ(1, z) = O(|τ-1| ‖z‖⁴)`. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter Asymptotics
open scoped ENNReal Topology

namespace BecknerOnofri.V2.Reaudit.SobolevQuartic
open BecknerOnofri.V2.Reaudit.Sobolev BecknerOnofri.HighDim ContinuousGibbs ContinuousFirstShell
  ContinuousComplement

variable {d : ℕ} {s : ℝ} [SobolevIndex d s]

/-- The inclusion `H^s_{K^⊥} → C(𝕋^d)_{K^⊥}` intertwines the `H^s` complement equation with the
continuous projected equation (a compatibility statement; no graph is identified). -/
theorem toComplement_complementEq' (τ : ℝ) (z : Coordinates d) (w : HsC d s) :
    HsC.toComplement d s (complementEq d s τ z w) =
      projectedEquation (greenContinuous d) ((τ, z), HsC.toComplement d s w) := by
  unfold complementEq projectedEquation
  rw [map_sub, map_smul, Hs.toComplement_complMap]
  congr 2
  rw [Hs.greenH_val, Hs.val_sub, Hs.val_gibbs, Hs.val_one, Hs.reconstructionH_val]

/-! ## The dual functional equals `Θ + (1 - 1/τ) S` on the graph -/

theorem graphValue_eq_Theta (hd11 : 11 ≤ d) {σ : ℝ} (hσ : σ ≠ 0) (z : Coordinates d) :
    BecknerOnofri.HighDim.LocalEleven.ReducedEnergyGradient.graphValue σ
        (fun _ => HsC.toComplement d s (graph (s := s) hd11 (σ, z))) z =
      Theta (s := s) hd11 (σ, z) + (1 - 1 / σ) * LocalReductionStatement.mass z := by
  unfold BecknerOnofri.HighDim.LocalEleven.ReducedEnergyGradient.graphValue Theta Lfun logZ
  have hrec : reconstruction d (z, HsC.toComplement d s (graph (s := s) hd11 (σ, z))) =
      (Hs.reconstructionH d s (z, graph (s := s) hd11 (σ, z))).val :=
    (Hs.reconstructionH_val (z, graph (s := s) hd11 (σ, z))).symm
  rw [hrec]
  have hlog : logPartitionReal (Hs.reconstructionH d s (z, graph (s := s) hd11 (σ, z))).val =
      Real.log (Hs.partition (Hs.assemblyH d s z + ((graph (s := s) hd11 (σ, z) : HsC d s) : Hs d s))) := by
    unfold logPartitionReal
    rw [← Hs.partition_eq]
    rfl
  have hmean : mean d ((HsC.toComplement d s (graph (s := s) hd11 (σ, z)) : Space d) *
      normalized (Hs.reconstructionH d s (z, graph (s := s) hd11 (σ, z))).val) =
      Hs.meanCLM d s (((graph (s := s) hd11 (σ, z) : HsC d s) : Hs d s) *
        Hs.gibbs (Hs.assemblyH d s z + ((graph (s := s) hd11 (σ, z) : HsC d s) : Hs d s))) := by
    rw [Hs.meanCLM_apply, Hs.val_mul, Hs.val_gibbs]
    rfl
  rw [hlog, hmean, BecknerOnofri.HighDim.LocalEleven.GraphEnergy.assembly_square_mean]
  unfold LocalReductionStatement.mass
  field_simp
  ring

/-- **The reduced functional in the manuscript's variables**:
`Φ_{d,τ}(v + w(τ,v)) - (1 - 1/τ) S = Θ(τ, z)` near `(1, 0)`. -/
theorem dual_sub_eq_Theta (hd11 : 11 ≤ d) :
    ∀ᶠ x in 𝓝 ((1 : ℝ), (0 : Coordinates d)),
      (dualFunctional (x.1 * spectralThreshold d)
          (Hs.reconstructionH d s (x.2, graph (s := s) hd11 x)).val).toReal -
        (1 - 1 / x.1) * LocalReductionStatement.mass x.2 = Theta (s := s) hd11 x := by
  have hp : ∀ᶠ x : ℝ × Coordinates d in 𝓝 (1, 0), 0 < x.1 :=
    continuous_fst.continuousAt.preimage_mem_nhds (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [graph_solves (s := s) hd11, hp] with x hx hpos
  have he : projectedEquation (greenContinuous d)
      ((x.1, x.2), HsC.toComplement d s (graph (s := s) hd11 x)) = 0 := by
    rw [← toComplement_complementEq', hx, map_zero]
  have hrec : reconstruction d (x.2, HsC.toComplement d s (graph (s := s) hd11 x)) =
      (Hs.reconstructionH d s (x.2, graph (s := s) hd11 x)).val :=
    (Hs.reconstructionH_val (x.2, graph (s := s) hd11 x)).symm
  have hh := BecknerOnofri.HighDim.LocalEleven.GraphEnergy.graph_dualFunctional
    (SobolevIndex.hd d s) hpos x.2 (HsC.toComplement d s (graph (s := s) hd11 x)) he
  have h2 := graphValue_eq_Theta (s := s) hd11 hpos.ne' x.2
  have hv : BecknerOnofri.HighDim.LocalEleven.ReducedEnergyGradient.graphValue x.1
      (fun _ => HsC.toComplement d s (graph (s := s) hd11 (x.1, x.2))) x.2 =
      logPartitionReal (reconstruction d (x.2, HsC.toComplement d s (graph (s := s) hd11 x))) -
        mean d ((assembly d x.2) ^ 2) / (2 * x.1) -
        (1 / 2 : ℝ) * mean d ((HsC.toComplement d s (graph (s := s) hd11 x) : Space d) *
          normalized (reconstruction d (x.2, HsC.toComplement d s (graph (s := s) hd11 x)))) := rfl
  rw [hv, BecknerOnofri.HighDim.LocalEleven.GraphEnergy.assembly_square_mean] at h2
  rw [hrec] at hh h2
  rw [hh, EReal.toReal_coe]
  have h3 : Theta (s := s) hd11 x = Theta (s := s) hd11 (x.1, x.2) := rfl
  rw [h3]
  unfold LocalReductionStatement.mass at h2 ⊢
  have h4 : (2 * ∑ i : Fin d, ‖x.2 i‖ ^ 2) / (2 * x.1) = (∑ i : Fin d, ‖x.2 i‖ ^ 2) / x.1 := by
    field_simp
  rw [h4] at h2
  linarith [h2]

/-! ## The `τ`-derivative -/

theorem Theta_hasDerivAt (hd11 : 11 ≤ d) :
    ∀ᶠ x in 𝓝 ((1 : ℝ), (0 : Coordinates d)),
      HasDerivAt (fun σ => Theta (s := s) hd11 (σ, x.2))
        (Hs.meanCLM d s (wX (s := s) hd11 x * Hs.gibbs (UX (s := s) hd11 x)) / (2 * x.1)) x.1 := by
  have hp : ∀ᶠ x : ℝ × Coordinates d in 𝓝 (1, 0), 0 < x.1 :=
    continuous_fst.continuousAt.preimage_mem_nhds (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [(graph_solves (s := s) hd11).eventually_nhds,
    (graph_analytic (s := s) hd11).eventually_analyticAt, hp] with x hx ha hpos
  have ht : HasDerivAt (fun μ : ℝ => (μ, x.2)) (1, 0) x.1 :=
    (hasDerivAt_id x.1).prodMk (hasDerivAt_const x.1 x.2)
  have hψ : DifferentiableAt ℝ (fun μ => graph (s := s) hd11 (μ, x.2)) x.1 := by
    convert! ha.differentiableAt.comp x.1 ht.differentiableAt using 1
  have hψC : HasDerivAt (fun μ => HsC.toComplement d s (graph (s := s) hd11 (μ, x.2)))
      (HsC.toComplement d s (deriv (fun μ => graph (s := s) hd11 (μ, x.2)) x.1)) x.1 :=
    (HsC.toComplement d s).hasFDerivAt.comp_hasDerivAt x.1 hψ.hasDerivAt
  have hes : ∀ᶠ μ in 𝓝 x.1, projectedEquation (greenContinuous d)
      ((μ, x.2), HsC.toComplement d s (graph (s := s) hd11 (μ, x.2))) = 0 := by
    filter_upwards [ht.continuousAt.tendsto.eventually hx] with μ hμ
    rw [← toComplement_complementEq']
    simp only [hμ, map_zero]
  have hh := BecknerOnofri.HighDim.LocalEleven.ReducedEnergyGradient.hasDerivAt_parameter_graphValue
    (SobolevIndex.hd d s) hpos.ne' x.2 hψC hes
  have hlead : HasDerivAt (fun σ : ℝ => (1 - 1 / σ) * LocalReductionStatement.mass x.2)
      (LocalReductionStatement.mass x.2 / x.1 ^ 2) x.1 := by
    have h1 : HasDerivAt (fun σ : ℝ => (1 : ℝ) / σ) (-(x.1 ^ 2)⁻¹) x.1 := by
      simpa [one_div] using hasDerivAt_inv hpos.ne'
    have := ((hasDerivAt_const x.1 (1 : ℝ)).sub h1).mul_const (LocalReductionStatement.mass x.2)
    refine this.congr_deriv ?_
    ring
  have hsub := hh.sub hlead
  have heq : (fun σ => Theta (s := s) hd11 (σ, x.2)) =ᶠ[𝓝 x.1]
      (fun σ => BecknerOnofri.HighDim.LocalEleven.ReducedEnergyGradient.graphValue σ
        (fun _ => HsC.toComplement d s (graph (s := s) hd11 (σ, x.2))) x.2 -
          (1 - 1 / σ) * LocalReductionStatement.mass x.2) := by
    filter_upwards [Ioi_mem_nhds hpos] with σ hσ
    rw [graphValue_eq_Theta (s := s) hd11 (ne_of_gt hσ)]
    ring
  have hM : mean d ((HsC.toComplement d s (graph (s := s) hd11 (x.1, x.2)) : Space d) *
      normalized (reconstruction d (x.2, HsC.toComplement d s (graph (s := s) hd11 (x.1, x.2))))) =
      Hs.meanCLM d s (wX (s := s) hd11 x * Hs.gibbs (UX (s := s) hd11 x)) := by
    rw [Hs.meanCLM_apply, Hs.val_mul, Hs.val_gibbs]
    rfl
  refine (hsub.congr_of_eventuallyEq heq).congr_deriv ?_
  rw [BecknerOnofri.HighDim.LocalEleven.GraphEnergy.assembly_square_mean, hM]
  unfold LocalReductionStatement.mass
  field_simp
  ring

/-! ## The bound for `∫ w ρ_{v+w}` -/

theorem isBigO_snd_pow {m n : ℕ} (h : n ≤ m) :
    (fun x : ℝ × Coordinates d => ‖x.2‖ ^ m) =O[𝓝 ((1 : ℝ), (0 : Coordinates d))]
      (fun x => ‖x.2‖ ^ n) := by
  have hs : Tendsto (Prod.snd : ℝ × Coordinates d → Coordinates d) (𝓝 (1, 0)) (𝓝 0) :=
    continuous_snd.continuousAt
  exact (norm_pow_isBigO_of_le (E := Coordinates d) h).comp_tendsto hs

theorem wX_isBigO (hd11 : 11 ≤ d) :
    (fun x : ℝ × Coordinates d => wX (s := s) hd11 x) =O[𝓝 ((1 : ℝ), (0 : Coordinates d))]
      (fun x => ‖x.2‖ ^ 2) :=
  ((HsC d s).subtypeL.isBigO_comp _ (𝓝 (1, 0))).trans (graph_uniform hd11)

theorem snd_tendsto : Tendsto (Prod.snd : ℝ × Coordinates d → Coordinates d) (𝓝 (1, 0)) (𝓝 0) :=
  continuous_snd.continuousAt

theorem UX_isBigO (hd11 : 11 ≤ d) :
    (fun x : ℝ × Coordinates d => UX (s := s) hd11 x) =O[𝓝 ((1 : ℝ), (0 : Coordinates d))]
      (fun x => ‖x.2‖) := by
  have h1 := (((Hs.assemblyH d s).isBigO_id (𝓝 (0 : Coordinates d))).norm_right).comp_tendsto
    (snd_tendsto (d := d))
  have h2 := (wX_isBigO (s := s) hd11).trans (isBigO_snd_pow (d := d) (m := 2) (n := 1) (by norm_num))
  simp only [pow_one] at h2
  exact h1.add h2

theorem rho_sub_isBigO (hd11 : 11 ≤ d) :
    (fun x : ℝ × Coordinates d => Hs.gibbs (UX (s := s) hd11 x) - 1 - Hs.assemblyH d s x.2)
      =O[𝓝 ((1 : ℝ), (0 : Coordinates d))] (fun x => ‖x.2‖ ^ 2) := by
  have hU := UX_isBigO (s := s) hd11
  have hw := wX_isBigO (s := s) hd11
  have hU2 : (fun x : ℝ × Coordinates d => UX (s := s) hd11 x ^ 2)
      =O[𝓝 ((1 : ℝ), (0 : Coordinates d))] (fun x => ‖x.2‖ ^ 2) := hU.pow 2
  have hpk : (fun x : ℝ × Coordinates d => pk d s 2 (UX (s := s) hd11 x))
      =O[𝓝 ((1 : ℝ), (0 : Coordinates d))] (fun x => ‖x.2‖ ^ 2) := isBigO_meanCLM hU2
  have hpk1 : (fun x : ℝ × Coordinates d => pk d s 2 (UX (s := s) hd11 x) • (1 : Hs d s))
      =O[𝓝 ((1 : ℝ), (0 : Coordinates d))] (fun x => ‖x.2‖ ^ 2) := by
    have h1 := hpk.smul (isBigO_const_const (1 : Hs d s) (one_ne_zero' (ℝ))
      (𝓝 ((1 : ℝ), (0 : Coordinates d))))
    simpa using h1
  have hR : (fun x : ℝ × Coordinates d => gibbsRem3 (UX (s := s) hd11 x))
      =O[𝓝 ((1 : ℝ), (0 : Coordinates d))] (fun x => ‖x.2‖ ^ 2) := by
    have h := ((gibbs_second_order (d := d) (s := s)).comp_tendsto (UX_tendsto hd11)).trans
      (hU.norm_left.pow 3)
    exact (h.congr_left fun x => rfl).trans (isBigO_snd_pow (m := 3) (n := 2) (by norm_num))
  have := (hw.add ((hU2.sub hpk1).const_smul_left (1 / 2 : ℝ))).add hR
  refine this.congr_left fun x => ?_
  simp only [Pi.smul_apply]
  unfold gibbsRem3
  rw [UX_eq]
  module

/-- `∫ w ρ_{v+w} = ∫ w (ρ_{v+w} - 1 - v)` by the orthogonality relations. -/
theorem meanCLM_w_rho (hd11 : 11 ≤ d) (x : ℝ × Coordinates d) :
    Hs.meanCLM d s (wX (s := s) hd11 x * Hs.gibbs (UX (s := s) hd11 x)) =
      Hs.meanCLM d s (wX (s := s) hd11 x *
        (Hs.gibbs (UX (s := s) hd11 x) - 1 - Hs.assemblyH d s x.2)) := by
  have h1 : Hs.meanCLM d s (wX (s := s) hd11 x) = 0 := meanCLM_coe_complement _
  have h2 : Hs.meanCLM d s (wX (s := s) hd11 x * Hs.assemblyH d s x.2) = 0 := by
    rw [mul_comm]; exact meanCLM_assemblyH_mul x.2 _
  have : wX (s := s) hd11 x * (Hs.gibbs (UX (s := s) hd11 x) - 1 - Hs.assemblyH d s x.2) =
      wX (s := s) hd11 x * Hs.gibbs (UX (s := s) hd11 x) - wX (s := s) hd11 x -
        wX (s := s) hd11 x * Hs.assemblyH d s x.2 := by ring
  rw [this, map_sub, map_sub, h1, h2]
  ring

/-- **`∫ w ρ_{v+w} = O(‖z‖⁴)` uniformly in `τ`.** -/
theorem integral_w_rho_isBigO (hd11 : 11 ≤ d) :
    (fun x : ℝ × Coordinates d => Hs.meanCLM d s (wX (s := s) hd11 x * Hs.gibbs (UX (s := s) hd11 x)))
      =O[𝓝 ((1 : ℝ), (0 : Coordinates d))] (fun x => ‖x.2‖ ^ 4) := by
  have h := isBigO_meanCLM ((wX_isBigO (s := s) hd11).mul (rho_sub_isBigO (s := s) hd11))
  refine (h.congr_right fun x => by ring).congr_left fun x => ?_
  exact (meanCLM_w_rho hd11 x).symm

theorem Theta_derivative_isBigO (hd11 : 11 ≤ d) :
    (fun x : ℝ × Coordinates d =>
      Hs.meanCLM d s (wX (s := s) hd11 x * Hs.gibbs (UX (s := s) hd11 x)) / (2 * x.1))
      =O[𝓝 ((1 : ℝ), (0 : Coordinates d))] (fun x => ‖x.2‖ ^ 4) := by
  have hf : ContinuousAt (fun x : ℝ × Coordinates d => 1 / (2 * x.1)) (1, 0) :=
    continuousAt_const.div (continuousAt_const.mul continuous_fst.continuousAt) (by norm_num)
  have hh := (integral_w_rho_isBigO (s := s) hd11).mul hf.isBigO
  refine hh.congr' (Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
  · simp [div_eq_mul_inv]
  · simp

/-- **Parameter dependence**: `Θ(τ, z) - Θ(1, z) = O(|τ - 1| ‖z‖⁴)` near `(1, 0)`. -/
theorem theta_param_difference (hd11 : 11 ≤ d) :
    (fun x : ℝ × Coordinates d => Theta (s := s) hd11 x - Theta (s := s) hd11 (1, x.2))
      =O[𝓝 ((1 : ℝ), (0 : Coordinates d))] (fun x => |x.1 - 1| * ‖x.2‖ ^ 4) :=
  BecknerOnofri.parameter_difference_isBigO 4 (Theta_hasDerivAt hd11) (Theta_derivative_isBigO hd11)

end BecknerOnofri.V2.Reaudit.SobolevQuartic
