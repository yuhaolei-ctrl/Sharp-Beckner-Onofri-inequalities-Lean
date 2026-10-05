module

public import BecknerOnofri.Friedrichs.SmoothCutoffApproximation
public import Legacy.BecknerOnofri.JacobiAngular

@[expose] public section

/-! Sine-weighted smooth cosine profiles have actual compactly supported
spatial approximants in the singular Jacobi form norm. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace BecknerOnofri.Friedrichs
open Legacy.BecknerOnofri.JacobiAngular

lemma angular_smooth (m : ℕ) {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (angular m f) :=
  (Real.contDiff_sin.pow m).mul (hf.comp Real.contDiff_cos)

lemma angular_div_sin {m : ℕ} (hm : 0<m) (f : ℝ → ℝ) {t : ℝ}
    (ht : t∈Ioo 0 Real.pi) :
    angular m f t/Real.sin t=Real.sin t^(m-1)*f (Real.cos t) := by
  have hs := (Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2).ne'
  have he : m=(m-1)+1 := by omega
  rw [angular,he,pow_succ]
  field_simp
  simp [mul_comm]

lemma angular_potential_integrable {m : ℕ} (hm : 0<m) {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) :
    IntegrableOn (fun t => (angular m f t/Real.sin t)^2) (Ioo 0 Real.pi) := by
  have hi : IntegrableOn (fun t => (Real.sin t^(m-1)*f (Real.cos t))^2)
      (Ioo 0 Real.pi) volume := (((Real.continuous_sin.pow (m-1)).mul (hf.continuous.comp Real.continuous_cos )).pow 2).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  rw [angular_div_sin hm f ht]

lemma angular_cutoff_smooth (m : ℕ) {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (δ : ℝ) :
    ContDiff ℝ ∞ (fun t => boundaryCutoff δ t*angular m f t) :=
  (boundaryCutoff_smooth δ).mul (angular_smooth m hf)

lemma angular_cutoff_compact (m : ℕ) (f : ℝ → ℝ) {δ : ℝ} (hδ : 0<δ) :
    HasCompactSupport (fun t => boundaryCutoff δ t*angular m f t) :=
  (boundaryCutoff_compact hδ).mul_right

lemma angular_cutoff_tsupport (m : ℕ) (f : ℝ → ℝ) {δ : ℝ} (hδ : 0<δ) :
    tsupport (fun t => boundaryCutoff δ t*angular m f t) ⊆ Ioo 0 Real.pi := by
  have hs : Function.support (fun t => boundaryCutoff δ t*angular m f t) ⊆ Icc δ (Real.pi-δ) := by
    intro t ht
    apply boundaryCutoff_support hδ
    intro hh
    exact ht (by simp [hh])
  have hcl : tsupport (fun t => boundaryCutoff δ t*angular m f t) ⊆ Icc δ (Real.pi-δ) :=
    closure_minimal hs isClosed_Icc
  intro t ht
  have hh := hcl ht
  exact ⟨lt_of_lt_of_le hδ hh.1,by linarith [hh.2]⟩

theorem angular_cutoff_form_tendsto_zero {m : ℕ} (hm : 0<m) {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) :
    Tendsto (fun δ : ℝ => spatialFormNormSq m
      (fun t => angular m f t-boundaryCutoff δ t*angular m f t)) (𝓝[>] 0) (𝓝 0) := by
  have h0 : angular m f 0=0 := by simp [angular,Nat.ne_of_gt hm]
  have hπ : angular m f Real.pi=0 := by simp [angular,Nat.ne_of_gt hm]
  have he (δ : ℝ) : (fun t => angular m f t-boundaryCutoff δ t*angular m f t) =
      cutoffError δ (angular m f) := by funext t; dsimp [cutoffError]; ring
  simp_rw [he]
  exact spatial_cutoff_form_tendsto_zero m (angular_smooth m hf) h0 hπ
    (angular_potential_integrable hm hf)

#print axioms angular_cutoff_form_tendsto_zero
end BecknerOnofri.Friedrichs
