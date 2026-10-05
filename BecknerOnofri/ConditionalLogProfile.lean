import BecknerOnofri.ConditionalProfileDefinitions
import BecknerOnofri.ConditionalExpectations
import BecknerOnofri.LogMarginalConvexity
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Actual conditional densities inherit the increasing convex logarithmic
cosine profile by integration of the original exponential profile. -/

noncomputable section
open MeasureTheory Set Function

namespace BecknerOnofri.HighDim.ConditionalEntropy
open EntropyShearer

theorem cosineVector_continuous (d : ℕ) : Continuous (@cosineVector d) := by
  unfold cosineVector
  fun_prop

theorem cosineVector_mem {d : ℕ} (x : Torus d) : cosineVector x ∈ cosineCube d := by
  have h (j : Fin d) : |cosineVector x j| ≤ 1 := by
    calc
      _ ≤ ‖fourier 1 (x j)‖ := Complex.abs_re_le_norm _
      _ = 1 := by simp [fourier_apply]
  exact ⟨fun j => (abs_le.mp (h j)).1, fun j => (abs_le.mp (h j)).2⟩

theorem cosineCube_update {d : ℕ} {v : Fin d → ℝ} (hv : v ∈ cosineCube d)
    (i : Fin d) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    Function.update v i t ∈ cosineCube d := by
  constructor <;> intro j <;> by_cases hj : j = i
  · subst j; simpa using ht.1
  · simpa only [Function.update_of_ne hj] using hv.1 j
  · subst j; simpa using ht.2
  · simpa only [Function.update_of_ne hj] using hv.2 j

theorem cosineVector_update {d : ℕ} (x : Torus d) (i : Fin d) (z : UnitAddCircle) :
    cosineVector (Function.update x i z) = Function.update (cosineVector x) i (fourier 1 z).re := by
  funext j
  by_cases hj : j = i
  · subst j; simp [cosineVector]
  · simp [cosineVector, Function.update_of_ne hj]

theorem conditional_log_profile {d : ℕ} (V : (Fin d → ℝ) → ℝ)
    (hc : ContinuousOn V (cosineCube d))
    (hconv : ∀ v ∈ cosineCube d, ∀ i : Fin d,
      ConvexOn ℝ (Icc (-1 : ℝ) 1) (fun t => V (Function.update v i t)))
    (hmono : ∀ v ∈ cosineCube d, ∀ i : Fin d,
      MonotoneOn (fun t => V (Function.update v i t)) (Icc (-1 : ℝ) 1))
    (f : Torus d → ℝ) (hrep : ∀ x, f x = Real.exp (V (cosineVector x)))
    (i : Fin d) (x : Torus d) :
    ∃ F : ℝ → ℝ, ContinuousOn F (Icc (-1 : ℝ) 1) ∧
      ConvexOn ℝ (Icc (-1 : ℝ) 1) F ∧ MonotoneOn F (Icc (-1 : ℝ) 1) ∧
      ∀ z : UnitAddCircle, conditionalDensity f i x z = Real.exp (F (fourier 1 z).re) := by
  let S := suffixCoordinates d (i.val + 1)
  let μ : Measure (S → UnitAddCircle) := Measure.pi (fun _ => AddCircle.haarAddCircle)
  let W : ℝ → (S → UnitAddCircle) → ℝ := fun t y =>
    V (Function.update (cosineVector (updateFinset x S y)) i t)
  let Z : ℝ → ℝ := fun t => ∫ y, Real.exp (W t y) ∂μ
  let b := prefixDensity f i.val x
  have hf : Continuous f := by
    have h := hc.comp_continuous (cosineVector_continuous d) (fun y => cosineVector_mem y)
    have he : f = fun y => Real.exp (V (cosineVector y)) := funext hrep
    rw [he]
    exact Real.continuous_exp.comp h
  have hp : PositiveBounded f := positiveBounded_of_continuous_pos hf (fun y => by
    rw [hrep]; exact Real.exp_pos _)
  have hb : 0 < b := (prefix_positive hp _).pos x
  have hmap : Continuous (fun p : ℝ × (S → UnitAddCircle) =>
      Function.update (cosineVector (updateFinset x S p.2)) i p.1) := by
    apply continuous_pi
    intro j
    by_cases hj : j = i
    · subst j; simp only [Function.update_self]; fun_prop
    · simp only [Function.update_of_ne hj, cosineVector, updateFinset]
      split_ifs <;> fun_prop
  have hmaps : MapsTo (fun p : ℝ × (S → UnitAddCircle) =>
      Function.update (cosineVector (updateFinset x S p.2)) i p.1)
      (Icc (-1 : ℝ) 1 ×ˢ univ) (cosineCube d) := by
    intro p hp
    exact cosineCube_update (cosineVector_mem _) i hp.1
  have hW : ContinuousOn W.uncurry (Icc (-1 : ℝ) 1 ×ˢ univ) :=
    hc.comp hmap.continuousOn hmaps
  have hWy (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) : Continuous (W t) := by
    exact hW.comp_continuous (continuous_const.prodMk continuous_id) (fun y => ⟨ht, mem_univ y⟩)
  have hI (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) : Integrable (fun y => Real.exp (W t y)) μ :=
    (Real.continuous_exp.comp (hWy t ht)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hZpos (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) : 0 < Z t := integral_exp_pos (hI t ht)
  have hZc : ContinuousOn Z (Icc (-1 : ℝ) 1) := by
    exact continuousOn_integral_of_compact_support (μ := μ) isCompact_univ
      (Real.continuous_exp.comp_continuousOn hW) (by simp)
  have hlogc : ContinuousOn (fun t => Real.log (Z t)) (Icc (-1 : ℝ) 1) :=
    hZc.log (fun t ht => (hZpos t ht).ne')
  have hlogconv : ConvexOn ℝ (Icc (-1 : ℝ) 1) (fun t => Real.log (Z t)) :=
    log_integral_exp_convex μ (convex_Icc _ _) W
      (fun y => hconv _ (cosineVector_mem _) i) hI
  have hlogmono : MonotoneOn (fun t => Real.log (Z t)) (Icc (-1 : ℝ) 1) :=
    log_integral_exp_monotone μ W (fun y => hmono _ (cosineVector_mem _) i) hI
  refine ⟨fun t => Real.log (Z t) - Real.log b, hlogc.sub continuousOn_const, ?_, ?_, ?_⟩
  · refine ⟨hlogconv.1, ?_⟩
    intro s hs t ht a c ha hc hac
    have h := hlogconv.2 hs ht ha hc hac
    simp only [smul_eq_mul] at h ⊢
    nlinarith [congrArg (fun r : ℝ => r * Real.log b) hac]
  · intro s hs t ht hst
    exact sub_le_sub_right (hlogmono hs ht hst) _
  · intro z
    have hz : (fourier 1 z).re ∈ Icc (-1 : ℝ) 1 := by
      have h := cosineVector_mem (fun _ : Fin d => z)
      exact ⟨h.1 i, h.2 i⟩
    rw [Real.exp_sub, Real.exp_log (hZpos _ hz), Real.exp_log hb]
    unfold conditionalDensity
    congr 1
    unfold prefixDensity Z W
    apply integral_congr_ae
    filter_upwards [] with y
    rw [hrep]
    congr 2
    have hi : i ∉ S := by simp [S]
    have he : updateFinset (Function.update x i z) S y =
        Function.update (updateFinset x S y) i z := by
      funext j
      by_cases hj : j = i
      · subst j; simp [updateFinset, hi]
      · simp [updateFinset, hj, Function.update_of_ne hj]
    rw [he, cosineVector_update]

#print axioms conditional_log_profile
end BecknerOnofri.HighDim.ConditionalEntropy
