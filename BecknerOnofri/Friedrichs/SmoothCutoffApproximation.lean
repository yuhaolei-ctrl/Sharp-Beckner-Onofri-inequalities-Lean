import BecknerOnofri.Friedrichs.CutoffLimit
import Mathlib.Analysis.Calculus.MeanValue

/-! Actual convergence in the singular spatial Jacobi form norm. The proof
uses the endpoint cutoffs and dominated convergence on shrinking boundary
layers; it does not assume membership in a spectral form domain. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace BecknerOnofri.Friedrichs

def cutoffError (δ : ℝ) (h : ℝ → ℝ) (t : ℝ) : ℝ := (1-boundaryCutoff δ t)*h t

def spatialFormNormSq (m : ℕ) (f : ℝ → ℝ) : ℝ :=
  ∫ t in Ioo 0 Real.pi, (f t)^2+(deriv f t)^2+(m:ℝ)*((m:ℝ)-1)*(f t/Real.sin t)^2

lemma smooth_endpoint_bound {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    (h0 : h 0=0) (hπ : h Real.pi=0) :
    ∃ L : ℝ, 0≤L ∧ (∀ t∈Icc 0 Real.pi, |deriv h t|≤L) ∧
      ∀ t∈Ioo 0 Real.pi, |h t|≤L*t ∧ |h t|≤L*(Real.pi-t) := by
  have hd := (contDiff_infty_iff_deriv.mp hh).2.continuous
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s:=Icc 0 Real.pi) hd.continuousOn
  let L := max C 0
  have hL : 0≤L := le_max_right _ _
  have hb : ∀ t∈Icc 0 Real.pi, ‖deriv h t‖≤L := fun t ht => (hC t ht).trans (le_max_left _ _)
  refine ⟨L,hL,hb,?_⟩
  intro t ht
  constructor
  · have he := (convex_Icc (0:ℝ) Real.pi).norm_image_sub_le_of_norm_deriv_le
      (fun x _ => hh.differentiable (by simp) x) hb ⟨le_rfl,Real.pi_pos.le⟩
      ⟨ht.1.le,ht.2.le⟩
    simpa only [h0,sub_zero,Real.norm_eq_abs,abs_of_nonneg ht.1.le] using he
  · have he := (convex_Icc (0:ℝ) Real.pi).norm_image_sub_le_of_norm_deriv_le
      (fun x _ => hh.differentiable (by simp) x) hb ⟨Real.pi_pos.le,le_rfl⟩
      ⟨ht.1.le,ht.2.le⟩
    simpa only [hπ,sub_zero,Real.norm_eq_abs,abs_of_nonpos (sub_nonpos.mpr ht.2.le),neg_sub] using he

lemma cutoffError_smooth {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (δ : ℝ) :
    ContDiff ℝ ∞ (cutoffError δ h) := (contDiff_const.sub (boundaryCutoff_smooth δ)).mul hh

lemma cutoffError_deriv {h : ℝ → ℝ} (hh : Differentiable ℝ h) (δ t : ℝ) :
    deriv (cutoffError δ h) t =
      (1-boundaryCutoff δ t)*deriv h t-deriv (boundaryCutoff δ) t*h t := by
  have hχ := ((boundaryCutoff_smooth δ).differentiable (by simp) t).hasDerivAt
  have he := (((hasDerivAt_const t 1).sub hχ).mul (hh t).hasDerivAt).deriv
  change deriv (cutoffError δ h) t = _ at he
  rw [he]
  dsimp
  ring

lemma cutoffError_abs_le (δ : ℝ) (h : ℝ → ℝ) (t : ℝ) : |cutoffError δ h t|≤|h t| := by
  have hb := boundaryCutoff_mem δ t
  rw [cutoffError,abs_mul,abs_of_nonneg (by linarith [hb.2] : 0≤1-boundaryCutoff δ t)]
  exact mul_le_of_le_one_left (abs_nonneg _) (by linarith [hb.1])

lemma jacobi_coefficient_nonneg (m : ℕ) : 0≤(m:ℝ)*((m:ℝ)-1) := by
  cases m with
  | zero => norm_num
  | succ m => norm_num only [Nat.cast_add,Nat.cast_one,add_sub_cancel_right]; positivity

/-- The singular potential term is a genuine spatial integrability condition;
for Jacobi eigenfunctions it will be proved from their sine factor. -/
theorem spatial_cutoff_form_tendsto_zero (m : ℕ) {h : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) (h0 : h 0=0) (hπ : h Real.pi=0)
    (hpotential : IntegrableOn (fun t => (h t/Real.sin t)^2) (Ioo 0 Real.pi)) :
    Tendsto (fun δ : ℝ => spatialFormNormSq m (cutoffError δ h)) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨L,hL,hder,hvanish⟩ := smooth_endpoint_bound hh h0 hπ
  obtain ⟨C,hC,hχder⟩ := boundaryCutoff_deriv_bound
  let B := L+2*C*L
  have hB : 0≤B := by dsimp [B]; positivity
  let c : ℝ := (m:ℝ)*((m:ℝ)-1)
  have hc : 0≤c := jacobi_coefficient_nonneg m
  have hbder {δ t : ℝ} (hδ : 0<δ) (ht : t∈Ioo 0 Real.pi) :
      |deriv (cutoffError δ h) t|≤B := by
    rw [cutoffError_deriv (hh.differentiable (by simp))]
    have hχ := boundaryCutoff_mem δ t
    have hp := cutoff_derivative_times_vanishing_bound hC hL hδ ht (hχder δ hδ t)
      (hvanish t ht).1 (hvanish t ht).2
    calc
      _ ≤ |(1-boundaryCutoff δ t)*deriv h t|+|deriv (boundaryCutoff δ) t*h t| := abs_sub _ _
      _ ≤ L+2*C*L := by
        apply add_le_add _ hp
        rw [abs_mul,abs_of_nonneg (by linarith [hχ.2] : 0≤1-boundaryCutoff δ t)]
        exact (mul_le_of_le_one_left (abs_nonneg _) (by linarith [hχ.1])).trans
          (hder t ⟨ht.1.le,ht.2.le⟩)
  let F (δ t : ℝ) := (cutoffError δ h t)^2+(deriv (cutoffError δ h) t)^2+
    c*(cutoffError δ h t/Real.sin t)^2
  have hmeas : ∀ᶠ δ : ℝ in 𝓝[>] 0,
      AEStronglyMeasurable (F δ) (volume.restrict (Ioo 0 Real.pi)) := by
    apply Eventually.of_forall
    intro δ
    have he := (cutoffError_smooth hh δ).continuous
    have hed := (contDiff_infty_iff_deriv.mp (cutoffError_smooth hh δ)).2.continuous
    exact (((he.pow 2).measurable.add (hed.pow 2).measurable).add
      (measurable_const.mul ((he.measurable.div Real.measurable_sin).pow_const 2))).aestronglyMeasurable
  have hbound : ∀ᶠ δ : ℝ in 𝓝[>] 0, ∀ᵐ t ∂volume.restrict (Ioo 0 Real.pi),
      ‖F δ t‖≤(h t)^2+B^2+c*(h t/Real.sin t)^2 := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have he : (cutoffError δ h t)^2≤(h t)^2 := sq_le_sq.mpr (cutoffError_abs_le δ h t)
    have hd : (deriv (cutoffError δ h) t)^2≤B^2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hB).mpr (hbder hδ ht)
    have hp : (cutoffError δ h t/Real.sin t)^2≤(h t/Real.sin t)^2 := by
      rw [div_pow,div_pow]
      exact div_le_div_of_nonneg_right he (sq_nonneg _)
    rw [Real.norm_eq_abs,abs_of_nonneg (by dsimp [F]; positivity)]
    exact add_le_add (add_le_add he hd) (mul_le_mul_of_nonneg_left hp hc)
  have hi : IntegrableOn (fun t => (h t)^2+B^2+c*(h t/Real.sin t)^2) (Ioo 0 Real.pi) :=
    (((hh.continuous.pow 2).integrableOn_Icc.mono_set Ioo_subset_Icc_self).add
      ((continuous_const : Continuous (fun _ : ℝ => B^2)).integrableOn_Icc.mono_set Ioo_subset_Icc_self)).add
        (hpotential.const_mul c)
  have hlim : ∀ᵐ t ∂volume.restrict (Ioo 0 Real.pi),
      Tendsto (fun δ : ℝ => F δ t) (𝓝[>] 0) (𝓝 (0:ℝ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    apply tendsto_const_nhds.congr'
    filter_upwards [boundaryCutoff_eventually_one ht] with δ hδ
    simp [F,cutoffError_deriv (hh.differentiable (by simp)),cutoffError,hδ.1,hδ.2]
  simpa only [integral_zero,F,c,spatialFormNormSq] using tendsto_integral_filter_of_dominated_convergence
    (fun t => (h t)^2+B^2+c*(h t/Real.sin t)^2) hmeas hbound hi hlim

#print axioms spatial_cutoff_form_tendsto_zero
end BecknerOnofri.Friedrichs
