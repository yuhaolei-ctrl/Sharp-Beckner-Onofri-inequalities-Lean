module

public import BecknerOnofri.HeatL2Convergence
public import BecknerOnofri.HeatL1Contraction
public import Legacy.BecknerOnofri.BoundedDensityApproximation

@[expose] public section

/-! L1 heat approximation on the entire probability-density domain. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped Topology
namespace BecknerOnofri.HighDim.HeatApproximation
open Legacy.BecknerOnofri.TorusSobolev Legacy.BecknerOnofri.HeatDensityApproximation

lemma integral_norm_le_l2 {d : ℕ} (u : TorusL2 d) :
    (∫ x, ‖u x‖ ∂torusMeasure d) ≤ ‖u‖ := by
  have hu : AEStronglyMeasurable u (torusMeasure d) := Lp.aestronglyMeasurable u
  rw [integral_norm_eq_lintegral_enorm hu, ← eLpNorm_one_eq_lintegral_enorm hu]
  change (eLpNorm u 1 (torusMeasure d)).toReal ≤ (eLpNorm u 2 (torusMeasure d)).toReal
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top u)
    (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num : (1:ENNReal) ≤ 2))

theorem heat_l1_tendsto_of_memLp {d : ℕ} (ρ : Legacy.TorusEndpoint.ProbabilityDensity d)
    (hρ : MemLp ρ.value 2 (torusMeasure d))
    (t : ℕ → ℝ) (ht : ∀ n, 0 < t n) (ht0 : Tendsto t atTop (𝓝 0)) :
    Tendsto (fun n => l1distance (heatValue ρ (t n)) ρ.value) atTop (𝓝 0) := by
  have he (n : ℕ) : l1distance (heatValue ρ (t n)) ρ.value ≤
      ‖heatLp ρ (ht n)-Bridge.potentialLp ρ.value hρ‖ := by
    have h := integral_norm_le_l2 (heatLp ρ (ht n)-Bridge.potentialLp ρ.value hρ)
    convert! h using 1
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (heatLp ρ (ht n)) (Bridge.potentialLp ρ.value hρ),
      ContinuousFirstShell.toL2_ae ⟨heatValue ρ (t n),heatValue_continuous ρ (ht n)⟩,
      Bridge.potentialLp_ae ρ.value hρ] with x hx hy hz
    simp only [heatLp] at hx ⊢
    rw [hx,Pi.sub_apply,hy,hz,← Complex.ofReal_sub,Complex.norm_real]
    rfl
  apply squeeze_zero (fun n => integral_nonneg (fun x => norm_nonneg _)) he
  exact (tendsto_iff_norm_sub_tendsto_zero.mp (heatLp_tendsto ρ hρ t ht ht0))

theorem heat_l1_tendsto {d : ℕ} (ρ : Legacy.TorusEndpoint.ProbabilityDensity d)
    (t : ℕ → ℝ) (ht : ∀ n, 0 < t n) (ht0 : Tendsto t atTop (𝓝 0)) :
    Tendsto (fun n => l1distance (heatValue ρ (t n)) ρ.value) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨m,hm⟩ := ((Legacy.BecknerOnofri.BoundedDensityApproximation.density_L1_tendsto ρ).eventually
    (gt_mem_nhds (show (0:ℝ)<ε/3 by positivity))).exists
  let η := Legacy.BecknerOnofri.BoundedDensityApproximation.density ρ m
  have hη : MemLp η.value 2 (torusMeasure d) :=
    Legacy.BecknerOnofri.BoundedDensityApproximation.density_memLp ρ m
  have hsmall : l1distance η.value ρ.value < ε/3 := hm
  have hlim := heat_l1_tendsto_of_memLp η hη t ht ht0
  filter_upwards [hlim.eventually (gt_mem_nhds (show (0:ℝ)<ε/3 by positivity))] with n hn
  have hiρ : Integrable (heatValue ρ (t n)) (torusMeasure d) := heatValue_integrable ρ (ht n)
  have hiη : Integrable (heatValue η (t n)) (torusMeasure d) := heatValue_integrable η (ht n)
  have htriangle := (l1distance_triangle hiρ hiη ρ.integrable).trans
    (add_le_add (heat_l1_contraction ρ η (ht n))
      (l1distance_triangle hiη η.integrable ρ.integrable))
  rw [l1distance_symm ρ.value η.value] at htriangle
  have hnonneg : 0 ≤ l1distance (heatValue ρ (t n)) ρ.value := integral_nonneg (fun x => norm_nonneg _)
  rw [Real.dist_eq,sub_zero,abs_of_nonneg hnonneg]
  linarith

theorem heat_tendstoInMeasure {d : ℕ} (ρ : Legacy.TorusEndpoint.ProbabilityDensity d)
    (t : ℕ → ℝ) (ht : ∀ n, 0 < t n) (ht0 : Tendsto t atTop (𝓝 0)) :
    TendstoInMeasure (torusMeasure d) (fun n => heatValue ρ (t n)) atTop ρ.value := by
  apply tendstoInMeasure_of_tendsto_eLpNorm (p := 1) (by norm_num)
  have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp (heat_l1_tendsto ρ t ht ht0)
  have he (n : ℕ) : ENNReal.ofReal (l1distance (heatValue ρ (t n)) ρ.value) =
      eLpNorm (heatValue ρ (t n)-ρ.value) 1 (torusMeasure d) := by
    rw [eLpNorm_one_eq_lintegral_enorm
      (by exact ((heatValue_integrable ρ (ht n)).sub ρ.integrable).aestronglyMeasurable)]
    exact ofReal_integral_norm_eq_lintegral_enorm ((heatValue_integrable ρ (ht n)).sub ρ.integrable)
  simpa only [Function.comp_def,he,ENNReal.ofReal_zero] using! h

#print axioms heat_l1_tendsto
#print axioms heat_tendstoInMeasure
end BecknerOnofri.HighDim.HeatApproximation
