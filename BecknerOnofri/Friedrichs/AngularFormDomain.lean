import BecknerOnofri.Friedrichs.FormLift

/-! Actual sine-weighted smooth profiles belong to the spatial form closure,
with the function, derivative and singular-weight components identified in L2. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace BecknerOnofri.Friedrichs.SpatialForm
open Legacy.BecknerOnofri.JacobiAngular

lemma cutoff_potential_integrable (δ : ℝ) {h : ℝ → ℝ} (hc : Continuous h)
    (hi : IntegrableOn (fun t => (h t/Real.sin t)^2) (Ioo 0 Real.pi)) :
    IntegrableOn (fun t => (boundaryCutoff δ t*h t/Real.sin t)^2) (Ioo 0 Real.pi) := by
  apply hi.mono'
    (((boundaryCutoff_smooth δ).continuous.mul hc).measurable.div Real.measurable_sin |>.pow_const 2).aestronglyMeasurable
  apply ae_of_all
  intro t
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  have hχ := boundaryCutoff_mem δ t
  have hs : (boundaryCutoff δ t)^2≤1 := by nlinarith [hχ.1,hχ.2]
  calc
    _ = (boundaryCutoff δ t)^2*(h t/Real.sin t)^2 := by simp only [Pi.div_apply,Pi.mul_apply]; ring
    _ ≤ _ := mul_le_of_le_one_left (sq_nonneg _) hs

def angularLift {m : ℕ} (hm : 0<m) {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) : EnergySpace :=
  lift m (angular m f) (continuous_memLp (angular_smooth m hf).continuous)
    (continuous_memLp (contDiff_infty_iff_deriv.mp (angular_smooth m hf)).2.continuous)
    (potential_memLp (angular_smooth m hf).continuous m (angular_potential_integrable hm hf))

def cutoffLift {m : ℕ} (hm : 0<m) {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (δ : ℝ) : EnergySpace :=
  lift m (fun t => boundaryCutoff δ t*angular m f t)
    (continuous_memLp (angular_cutoff_smooth m hf δ).continuous)
    (continuous_memLp (contDiff_infty_iff_deriv.mp (angular_cutoff_smooth m hf δ)).2.continuous)
    (potential_memLp (angular_cutoff_smooth m hf δ).continuous m
      (cutoff_potential_integrable δ (angular_smooth m hf).continuous (angular_potential_integrable hm hf)))

lemma cutoffLift_mem_core {m : ℕ} (hm : 0<m) {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    {δ : ℝ} (hδ : 0<δ) : cutoffLift hm hf δ∈core m :=
  lift_mem_core m (angular_cutoff_smooth m hf δ) (angular_cutoff_compact m f hδ)
    (angular_cutoff_tsupport m f hδ) _ _ _

lemma angular_cutoff_energy_identity {m : ℕ} (hm : 0<m) {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (δ : ℝ) :
    spatialFormNormSq m (fun t => angular m f t-boundaryCutoff δ t*angular m f t) =
      ‖(cutoffLift hm hf δ).1-(angularLift hm hf).1‖^2+
      ‖(cutoffLift hm hf δ).2.1-(angularLift hm hf).2.1‖^2+
      ‖(cutoffLift hm hf δ).2.2-(angularLift hm hf).2.2‖^2 := by
  have he := formNorm_sub_identity m
    ((angular_smooth m hf).differentiable (by simp))
    ((angular_cutoff_smooth m hf δ).differentiable (by simp))
    (continuous_memLp (angular_smooth m hf).continuous)
    (continuous_memLp (angular_cutoff_smooth m hf δ).continuous)
    (continuous_memLp (contDiff_infty_iff_deriv.mp (angular_smooth m hf)).2.continuous)
    (continuous_memLp (contDiff_infty_iff_deriv.mp (angular_cutoff_smooth m hf δ)).2.continuous)
    (potential_memLp (angular_smooth m hf).continuous m (angular_potential_integrable hm hf))
    (potential_memLp (angular_cutoff_smooth m hf δ).continuous m
      (cutoff_potential_integrable δ (angular_smooth m hf).continuous (angular_potential_integrable hm hf)))
  change _ = ‖(angularLift hm hf).1-(cutoffLift hm hf δ).1‖^2+
    ‖(angularLift hm hf).2.1-(cutoffLift hm hf δ).2.1‖^2+
    ‖(angularLift hm hf).2.2-(cutoffLift hm hf δ).2.2‖^2 at he
  simpa only [Pi.sub_def,norm_sub_rev (angularLift hm hf).1,
    norm_sub_rev (angularLift hm hf).2.1,norm_sub_rev (angularLift hm hf).2.2] using he

theorem angular_mem_formClosure {m : ℕ} (hm : 0<m) {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) :
    angularLift hm hf∈formClosure m := by
  let δ (n : ℕ) : ℝ := 1/((n:ℝ)+1)
  have hδ (n : ℕ) : 0<δ n := by dsimp [δ]; positivity
  have hlim : Tendsto δ atTop (𝓝[>] (0:ℝ)) := tendsto_nhdsWithin_iff.mpr
    ⟨tendsto_one_div_add_atTop_nhds_zero_nat,Eventually.of_forall hδ⟩
  have ht := (angular_cutoff_form_tendsto_zero hm hf).comp hlim
  have hconv : Tendsto (fun n => cutoffLift hm hf (δ n)) atTop (𝓝 (angularLift hm hf)) := by
    apply energy_tendsto
    simpa only [Function.comp_def,angular_cutoff_energy_identity hm hf] using ht
  exact mem_closure_of_tendsto hconv (Eventually.of_forall (fun n => cutoffLift_mem_core hm hf (hδ n)))

#print axioms angular_mem_formClosure
end BecknerOnofri.Friedrichs.SpatialForm
