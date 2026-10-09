module

public import BecknerOnofri.ConditionalLogProfile
public import BecknerOnofri.CosineShapeCalculus
public import BecknerOnofri.ConditionalMomentBounds
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section

/-!
# The conditional logarithmic profile is differentiable and increasing (work package G10, part (c))

Source: the proof of Proposition 5.12(i), `eq:section5-channel-conditional-monotonicity`:
the numerator defining the conditional density `p_i(· | x_{<i})` is
`∫ e^{V(C_1,…,C_i, cos 2π x_{i+1},…)} ∏_{j>i} dx_j` (a function of the cosine `C_i` of `x_i`,
with `x_{<i}` fixed); "regarding `log p_i` as a function of `C_i`, differentiation under the numerator
integral gives `∂_{C_i} log p_i = E[∂_i V(C) | x_1,…,x_i] ≥ 0`".

We prove exactly this: `condNumer` is the numerator, `condNumer_hasDerivAt` differentiates under
the integral sign on `C_i ∈ (-1,1)` (dominated convergence, with the uniform bounds furnished by
compactness of the closed cosine cube), `condLogProfile_hasDerivAt` identifies the derivative of the
logarithm with the conditional expectation of `∂_iV`, and `conditional_log_profile_mono` concludes
that `log p_i` is a continuous nondecreasing function of `C_i` on `[-1,1]`.

The hypothesis is the closed-cube smoothness `V ∈ C^∞([-1,1]^d)` and `∂_i V ≥ 0` on the cube.  The
second-derivative condition is not used.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Function Filter Topology
open scoped ContDiff
namespace BecknerOnofri.V2.Channel
open BecknerOnofri.HighDim BecknerOnofri.HighDim.ConditionalEntropy BecknerOnofri.HighDim.EntropyShearer

variable {d : ℕ}

/-- The future coordinates `x_{i+1},…,x_{d-1}`, as an index set. -/
abbrev futureCoords (d : ℕ) (i : Fin d) : Finset (Fin d) := suffixCoordinates d (i.val + 1)

/-- Haar measure on the future coordinates. -/
abbrev futureMeasure (d : ℕ) (i : Fin d) : Measure (futureCoords d i → UnitAddCircle) :=
  Measure.pi (fun _ => AddCircle.haarAddCircle)

/-- The cosine point `(C_1,…,C_{i-1}; C_i = t; cos 2π x_{i+1},…)` with `x_{<i}` taken from `x`
and the future coordinates equal to `y`. -/
def condPoint (i : Fin d) (x : Torus d) (t : ℝ) (y : futureCoords d i → UnitAddCircle) :
    Fin d → ℝ :=
  update (cosineVector (updateFinset x (futureCoords d i) y)) i t

/-- The numerator of the conditional density of `x_i` given `x_{<i}`, as a function of the
cosine value `t` of `x_i`. -/
def condNumer (V : (Fin d → ℝ) → ℝ) (i : Fin d) (x : Torus d) (t : ℝ) : ℝ :=
  ∫ y, Real.exp (V (condPoint i x t y)) ∂futureMeasure d i

theorem condPoint_mem (i : Fin d) (x : Torus d) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1)
    (y : futureCoords d i → UnitAddCircle) : condPoint i x t y ∈ cosineCube d :=
  cosineCube_update (cosineVector_mem _) i ht

theorem continuous_condPoint (i : Fin d) (x : Torus d) :
    Continuous (fun p : ℝ × (futureCoords d i → UnitAddCircle) => condPoint i x p.1 p.2) := by
  apply continuous_pi
  intro j
  by_cases hj : j = i
  · subst j; simp only [condPoint, Function.update_self]; fun_prop
  · simp only [condPoint, Function.update_of_ne hj, cosineVector, updateFinset]
    split_ifs <;> fun_prop

/-- Derivative of the profile along coordinate `i` at an interior point. -/
theorem hasDerivAt_coordinate {V : (Fin d → ℝ) → ℝ} (hV : ContDiffOn ℝ ∞ V (cosineCube d))
    (i : Fin d) {v : Fin d → ℝ} (hv : v ∈ cosineCube d) {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun s => V (update v i s)) (cosinePartial i V (update v i t)) t := by
  have hmem : update v i t ∈ cosineCube d := cosineCube_update hv i (Ioo_subset_Icc_self ht)
  have h := CosineShape.hasDerivWithinAt_coordinate_of_contDiffOn hV i hmem
  simp only [update_idem, update_self] at h
  exact h.hasDerivAt (Icc_mem_nhds ht.1 ht.2)

theorem continuous_condPoint_section (i : Fin d) (x : Torus d) (s : ℝ) :
    Continuous (fun y : futureCoords d i → UnitAddCircle => condPoint i x s y) :=
  (continuous_condPoint i x).comp (Continuous.prodMk continuous_const continuous_id)

theorem continuous_exp_profile {V : (Fin d → ℝ) → ℝ} (hc : ContinuousOn V (cosineCube d))
    (i : Fin d) (x : Torus d) {s : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1) :
    Continuous (fun y : futureCoords d i → UnitAddCircle => Real.exp (V (condPoint i x s y))) :=
  Real.continuous_exp.comp
    (hc.comp_continuous (continuous_condPoint_section i x s) (fun y => condPoint_mem i x hs y))

theorem integrable_exp_profile {V : (Fin d → ℝ) → ℝ} (hc : ContinuousOn V (cosineCube d))
    (i : Fin d) (x : Torus d) {s : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1) :
    Integrable (fun y : futureCoords d i → UnitAddCircle => Real.exp (V (condPoint i x s y)))
      (futureMeasure d i) :=
  (continuous_exp_profile hc i x hs).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem condNumer_pos {V : (Fin d → ℝ) → ℝ} (hc : ContinuousOn V (cosineCube d))
    (i : Fin d) (x : Torus d) {s : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1) : 0 < condNumer V i x s :=
  integral_exp_pos (integrable_exp_profile hc i x hs)

theorem condNumer_continuousOn {V : (Fin d → ℝ) → ℝ} (hc : ContinuousOn V (cosineCube d))
    (i : Fin d) (x : Torus d) : ContinuousOn (condNumer V i x) (Icc (-1 : ℝ) 1) := by
  have hmaps : MapsTo (fun p : ℝ × (futureCoords d i → UnitAddCircle) => condPoint i x p.1 p.2)
      (Icc (-1 : ℝ) 1 ×ˢ univ) (cosineCube d) := fun p hp => condPoint_mem i x hp.1 p.2
  have hW : ContinuousOn (fun p : ℝ × (futureCoords d i → UnitAddCircle) =>
      Real.exp (V (condPoint i x p.1 p.2))) (Icc (-1 : ℝ) 1 ×ˢ univ) :=
    Real.continuous_exp.comp_continuousOn (hc.comp (continuous_condPoint i x).continuousOn hmaps)
  exact continuousOn_integral_of_compact_support (μ := futureMeasure d i) isCompact_univ hW
    (by simp)

/-- **Differentiation under the numerator integral** (`eq:section5-channel-conditional-monotonicity`):
for `C_i = t ∈ (-1,1)`,
`d/dt ∫ e^{V(C_{<i}, t, C_{>i})} dy = ∫ e^{V} ∂_iV dy`. -/
theorem condNumer_hasDerivAt {V : (Fin d → ℝ) → ℝ} (hV : ContDiffOn ℝ ∞ V (cosineCube d))
    (i : Fin d) (x : Torus d) {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (condNumer V i x)
      (∫ y, Real.exp (V (condPoint i x t y)) * cosinePartial i V (condPoint i x t y)
        ∂futureMeasure d i) t := by
  have hc := hV.continuousOn
  obtain ⟨MV, hMV⟩ := (isCompact_Icc : IsCompact (cosineCube d)).exists_bound_of_continuousOn hc
  have hDc : ContinuousOn (cosinePartial i V) (cosineCube d) :=
    (CosineShape.contDiffOn_cosinePartial hV i).continuousOn
  obtain ⟨MD, hMD⟩ := (isCompact_Icc : IsCompact (cosineCube d)).exists_bound_of_continuousOn hDc
  have hTmem : ∀ s ∈ Ioo (-1 : ℝ) 1, s ∈ Icc (-1 : ℝ) 1 := fun s hs => Ioo_subset_Icc_self hs
  have hF'cont : Continuous (fun y : futureCoords d i → UnitAddCircle =>
      Real.exp (V (condPoint i x t y)) * cosinePartial i V (condPoint i x t y)) :=
    (continuous_exp_profile hc i x (hTmem t ht)).mul
      (hDc.comp_continuous (continuous_condPoint_section i x t)
        (fun y => condPoint_mem i x (hTmem t ht) y))
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℝ) (μ := futureMeasure d i)
    (F := fun s y => Real.exp (V (condPoint i x s y)))
    (F' := fun s y => Real.exp (V (condPoint i x s y)) * cosinePartial i V (condPoint i x s y))
    (x₀ := t) (s := Ioo (-1 : ℝ) 1) (bound := fun _ => Real.exp MV * MD)
    (Ioo_mem_nhds ht.1 ht.2)
    (Filter.eventually_of_mem (Ioo_mem_nhds ht.1 ht.2) (fun s hs =>
      (continuous_exp_profile hc i x (hTmem s hs)).aestronglyMeasurable))
    (integrable_exp_profile hc i x (hTmem t ht))
    hF'cont.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun y s hs => by
      have hp := condPoint_mem i x (hTmem s hs) y
      rw [norm_mul]
      apply mul_le_mul _ (hMD _ hp) (norm_nonneg _) (Real.exp_pos _).le
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hMV _ hp))))
    (integrable_const _)
    (Filter.Eventually.of_forall (fun y s hs => by
      have hv : cosineVector (updateFinset x (futureCoords d i) y) ∈ cosineCube d :=
        cosineVector_mem _
      exact (hasDerivAt_coordinate hV i hv hs).exp))
  exact key.2

/-- `∂_{C_i} log p_i = E[∂_iV(C) | x_1,…,x_i]`: the derivative of the logarithm of the numerator is
the integral of `∂_iV` against the normalized conditional law of the future coordinates. -/
theorem condLogProfile_hasDerivAt {V : (Fin d → ℝ) → ℝ} (hV : ContDiffOn ℝ ∞ V (cosineCube d))
    (i : Fin d) (x : Torus d) {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun s => Real.log (condNumer V i x s))
      (∫ y, cosinePartial i V (condPoint i x t y) *
        (Real.exp (V (condPoint i x t y)) / condNumer V i x t) ∂futureMeasure d i) t := by
  have hpos := condNumer_pos hV.continuousOn i x (Ioo_subset_Icc_self ht)
  have h := (condNumer_hasDerivAt hV i x ht).log hpos.ne'
  convert h using 1
  rw [← integral_div]
  apply integral_congr_ae
  filter_upwards [] with y
  ring

/-- `log p_i` is nondecreasing in the cosine variable `C_i ∈ [-1,1]` (differentiation under the
integral and `∂_iV ≥ 0`). -/
theorem condLogProfile_mono {V : (Fin d → ℝ) → ℝ} (hV : ContDiffOn ℝ ∞ V (cosineCube d))
    (h1 : ∀ v ∈ cosineCube d, ∀ i : Fin d, 0 ≤ cosinePartial i V v)
    (i : Fin d) (x : Torus d) :
    MonotoneOn (fun s => Real.log (condNumer V i x s)) (Icc (-1 : ℝ) 1) := by
  have hc := hV.continuousOn
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
  · exact (condNumer_continuousOn hc i x).log (fun s hs => (condNumer_pos hc i x hs).ne')
  · rw [interior_Icc]
    exact fun s hs => (condLogProfile_hasDerivAt hV i x hs).differentiableAt.differentiableWithinAt
  · intro s hs
    rw [interior_Icc] at hs
    rw [(condLogProfile_hasDerivAt hV i x hs).deriv]
    apply integral_nonneg
    intro y
    have hp := condPoint_mem i x (Ioo_subset_Icc_self hs) y
    exact mul_nonneg (h1 _ hp i) (div_nonneg (Real.exp_pos _).le
      (condNumer_pos hc i x (Ioo_subset_Icc_self hs)).le)

/-- The actual conditional density of `x_i` given `x_{<i}` is `exp` of a continuous nondecreasing
function of the cosine `C_i`, namely `log (numerator) - log (normalizer)`. -/
theorem conditional_log_profile_mono {V : (Fin d → ℝ) → ℝ} (hV : ContDiffOn ℝ ∞ V (cosineCube d))
    (h1 : ∀ v ∈ cosineCube d, ∀ i : Fin d, 0 ≤ cosinePartial i V v)
    (f : Torus d → ℝ) (hrep : ∀ x, f x = Real.exp (V (cosineVector x)))
    (i : Fin d) (x : Torus d) :
    ∃ F : ℝ → ℝ, ContinuousOn F (Icc (-1 : ℝ) 1) ∧ MonotoneOn F (Icc (-1 : ℝ) 1) ∧
      ∀ z : UnitAddCircle, conditionalDensity f i x z = Real.exp (F (fourier 1 z).re) := by
  have hc := hV.continuousOn
  have hf : Continuous f := by
    have h := hc.comp_continuous (cosineVector_continuous d) (fun y => cosineVector_mem y)
    have he : f = fun y => Real.exp (V (cosineVector y)) := funext hrep
    rw [he]
    exact Real.continuous_exp.comp h
  have hp : PositiveBounded f := positiveBounded_of_continuous_pos hf (fun y => by
    rw [hrep]; exact Real.exp_pos _)
  have hb : 0 < prefixDensity f i.val x := (prefix_positive hp _).pos x
  refine ⟨fun t => Real.log (condNumer V i x t) - Real.log (prefixDensity f i.val x),
    (condNumer_continuousOn hc i x).log (fun s hs => (condNumer_pos hc i x hs).ne') |>.sub
      continuousOn_const,
    fun s hs t ht hst => sub_le_sub_right (condLogProfile_mono hV h1 i x hs ht hst) _, ?_⟩
  intro z
  have hz : (fourier 1 z).re ∈ Icc (-1 : ℝ) 1 := by
    have h := cosineVector_mem (fun _ : Fin d => z)
    exact ⟨h.1 i, h.2 i⟩
  rw [Real.exp_sub, Real.exp_log (condNumer_pos hc i x hz), Real.exp_log hb]
  unfold conditionalDensity
  congr 1
  unfold prefixDensity condNumer condPoint
  apply integral_congr_ae
  filter_upwards [] with y
  rw [hrep]
  congr 2
  have hi : i ∉ futureCoords d i := by simp [futureCoords]
  have he : updateFinset (update x i z) (futureCoords d i) y =
      update (updateFinset x (futureCoords d i) y) i z := by
    funext j
    by_cases hj : j = i
    · subst j; simp [updateFinset, hi]
    · simp [updateFinset, hj, Function.update_of_ne hj]
  rw [he, cosineVector_update]

end BecknerOnofri.V2.Channel
