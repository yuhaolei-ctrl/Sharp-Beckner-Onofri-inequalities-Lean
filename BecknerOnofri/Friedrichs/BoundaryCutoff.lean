module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Tactic

@[expose] public section

/-! Concrete smooth endpoint cutoffs for the spatial Friedrichs form.
These are the manuscript's cutoffs, not an assumed approximation family. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace BecknerOnofri.Friedrichs

lemma transition_deriv_zero_left {x : ℝ} (hx : x<0) : deriv Real.smoothTransition x=0 := by
  have he : Real.smoothTransition =ᶠ[𝓝 x] (fun _ => (0:ℝ)) := by
    filter_upwards [eventually_lt_nhds hx] with y hy
    exact Real.smoothTransition.zero_of_nonpos hy.le
  rw [he.deriv_eq,deriv_const]

lemma transition_deriv_zero_right {x : ℝ} (hx : 1<x) : deriv Real.smoothTransition x=0 := by
  have he : Real.smoothTransition =ᶠ[𝓝 x] (fun _ => (1:ℝ)) := by
    filter_upwards [eventually_gt_nhds hx] with y hy
    exact Real.smoothTransition.one_of_one_le hy.le
  rw [he.deriv_eq,deriv_const]

lemma transition_deriv_bound : ∃ C : ℝ, 0≤C ∧ ∀ x, |deriv Real.smoothTransition x|≤C := by
  have hc : Continuous (deriv Real.smoothTransition) :=
    ((contDiff_infty_iff_deriv.mp
      (Real.smoothTransition.contDiff : ContDiff ℝ ∞ Real.smoothTransition)).2).continuous
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s:=Icc (0:ℝ) 1) hc.continuousOn
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro x
  by_cases h0 : 0≤x
  · by_cases h1 : x≤1
    · exact (hC x ⟨h0,h1⟩).trans (le_max_left _ _)
    · rw [transition_deriv_zero_right (lt_of_not_ge h1),abs_zero]
      exact le_max_right _ _
  · rw [transition_deriv_zero_left (lt_of_not_ge h0),abs_zero]
    exact le_max_right _ _

def boundaryCutoff (δ t : ℝ) : ℝ :=
  Real.smoothTransition (t/δ-1)*Real.smoothTransition ((Real.pi-t)/δ-1)

lemma boundaryCutoff_smooth (δ : ℝ) : ContDiff ℝ ∞ (boundaryCutoff δ) :=
  (Real.smoothTransition.contDiff.comp ((contDiff_id.div_const δ).sub contDiff_const)).mul
    (Real.smoothTransition.contDiff.comp (((contDiff_const.sub contDiff_id).div_const δ).sub contDiff_const))

lemma boundaryCutoff_mem (δ t : ℝ) : boundaryCutoff δ t ∈ Icc (0:ℝ) 1 :=
  ⟨mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _),
    mul_le_one₀ (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _)
      (Real.smoothTransition.le_one _)⟩

lemma boundaryCutoff_zero_left {δ t : ℝ} (hδ : 0<δ) (ht : t≤δ) : boundaryCutoff δ t=0 := by
  rw [boundaryCutoff,Real.smoothTransition.zero_of_nonpos (by
    have h : t/δ≤1 := (div_le_one hδ).mpr ht
    linarith),zero_mul]

lemma boundaryCutoff_zero_right {δ t : ℝ} (hδ : 0<δ) (ht : Real.pi-δ≤t) : boundaryCutoff δ t=0 := by
  rw [boundaryCutoff,Real.smoothTransition.zero_of_nonpos (x:=(Real.pi-t)/δ-1) (by
    have h : (Real.pi-t)/δ≤1 := (div_le_one hδ).mpr (by linarith)
    linarith),mul_zero]

lemma boundaryCutoff_one {δ t : ℝ} (hδ : 0<δ) (ht : t∈Icc (2*δ) (Real.pi-2*δ)) :
    boundaryCutoff δ t=1 := by
  have hl : 1≤t/δ-1 := by
    have h : 2≤t/δ := (le_div_iff₀ hδ).mpr ht.1
    linarith
  have hr : 1≤(Real.pi-t)/δ-1 := by
    have h : 2≤(Real.pi-t)/δ := (le_div_iff₀ hδ).mpr (by linarith [ht.2])
    linarith
  simp only [boundaryCutoff,Real.smoothTransition.one_of_one_le hl,
    Real.smoothTransition.one_of_one_le hr,one_mul]

lemma boundaryCutoff_support {δ : ℝ} (hδ : 0<δ) :
    Function.support (boundaryCutoff δ) ⊆ Icc δ (Real.pi-δ) := by
  intro t ht
  constructor
  · by_contra hh
    exact ht (boundaryCutoff_zero_left hδ (le_of_not_ge hh))
  · by_contra hh
    exact ht (boundaryCutoff_zero_right hδ (le_of_not_ge hh))

lemma boundaryCutoff_compact {δ : ℝ} (hδ : 0<δ) : HasCompactSupport (boundaryCutoff δ) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc (boundaryCutoff_support hδ)

lemma boundaryCutoff_deriv {δ : ℝ} (hδ : 0<δ) (t : ℝ) :
    deriv (boundaryCutoff δ) t =
      deriv Real.smoothTransition (t/δ-1)/δ*Real.smoothTransition ((Real.pi-t)/δ-1) -
      Real.smoothTransition (t/δ-1)*deriv Real.smoothTransition ((Real.pi-t)/δ-1)/δ := by
  have hτ := (Real.smoothTransition.contDiff : ContDiff ℝ ∞ Real.smoothTransition).differentiable (by simp)
  have hl := (hτ (t/δ-1)).hasDerivAt.comp t (((hasDerivAt_id t).div_const δ).sub_const 1)
  have hr := (hτ ((Real.pi-t)/δ-1)).hasDerivAt.comp t
    ((((hasDerivAt_const t Real.pi).sub (hasDerivAt_id t)).div_const δ).sub_const 1)
  have hh := (hl.mul hr).deriv
  change deriv (boundaryCutoff δ) t = _ at hh
  rw [hh]
  dsimp
  ring

lemma boundaryCutoff_deriv_bound : ∃ C : ℝ, 0≤C ∧ ∀ δ : ℝ, 0<δ →
    ∀ t : ℝ, |deriv (boundaryCutoff δ) t|≤C/δ := by
  obtain ⟨C,hC,hbound⟩ := transition_deriv_bound
  refine ⟨2*C,by positivity,?_⟩
  intro δ hδ t
  rw [boundaryCutoff_deriv hδ]
  calc
    _ ≤ |deriv Real.smoothTransition (t/δ-1)/δ*Real.smoothTransition ((Real.pi-t)/δ-1)| +
      |Real.smoothTransition (t/δ-1)*deriv Real.smoothTransition ((Real.pi-t)/δ-1)/δ| := abs_sub _ _
    _ ≤ C/δ+C/δ := by
      simp only [abs_mul,abs_div,abs_of_pos hδ,abs_of_nonneg (Real.smoothTransition.nonneg _)]
      apply add_le_add
      · calc
          _ ≤ C/δ*1 := by
            exact mul_le_mul (div_le_div_of_nonneg_right (hbound _) hδ.le)
              (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _)
              (div_nonneg hC hδ.le)
          _ = _ := mul_one _
      · calc
          _ ≤ 1*C/δ := by
            exact div_le_div_of_nonneg_right
              (mul_le_mul (Real.smoothTransition.le_one _) (hbound _) (abs_nonneg _) (by norm_num)) hδ.le
          _ = _ := by rw [one_mul]
    _ = _ := by ring

#print axioms boundaryCutoff_deriv_bound
end BecknerOnofri.Friedrichs
