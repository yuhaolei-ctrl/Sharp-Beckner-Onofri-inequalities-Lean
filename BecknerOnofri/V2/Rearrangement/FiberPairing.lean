module

public import BecknerOnofri.V2.Rearrangement.HeatCircle
public import BecknerOnofri.V2.Rearrangement.CoordinateSplit
public import BecknerOnofri.CircleRearrangementTrustedBridge
public import BecknerOnofri.CoordinateRearrangementDefinitions
public import Legacy.BecknerOnofri.TorusHeatPolarization

@[expose] public section

/-! # One coordinate step increases the heat pairing (written route, Lemma 2.9)

Manuscript: for `r_{i-1}` and its fiberwise rearrangement `r_i` in coordinate `i`, for every
`t > 0`,
`∬ r_{i-1}(x) r_{i-1}(y) ∏_j p_t(x_j-y_j) ≤ ∬ r_i(x) r_i(y) ∏_j p_t(x_j-y_j)`
(`eq:coordinate-heat-comparison`).  The proof: fix the coordinates `x_j, y_j`, `j ≠ i`, apply
`Lemma 2.8` (`BecknerOnofri.Circle.circle_rearrangement`) to the two fibers in the variables
`x_i, y_i` with the circle kernel `p_t`, multiply by `∏_{j≠i} p_t(x_j-y_j) ≥ 0`, and integrate over
the remaining variables.  Here the "integrate over the remaining variables" is the Fubini step
`fiberMap₂_measurePreserving`.  The hypotheses are exactly: `r, s` integrable, a.e. nonnegative,
and `AECanonicalStep i r s`; no boundedness, no smoothness. -/

noncomputable section
open MeasureTheory Set
open Legacy.TorusEndpoint Legacy.BecknerOnofri.CoordinatePolarization
  BecknerOnofri.HighDim.CoordinateRearrangementStatement

namespace BecknerOnofri.V2.Rearrangement

/-- The product of the circle heat kernel over all coordinates except `i`. -/
def kernelRest {d : ℕ} (τ : ℝ) (i : Fin d) (x y : Torus d) : ℝ :=
  ∏ j ∈ Finset.univ.erase i, circleHeat τ (x j - y j)

theorem kernelRest_nonneg {d : ℕ} {τ : ℝ} (hτ : 0 < τ) (i : Fin d) (x y : Torus d) :
    0 ≤ kernelRest τ i x y :=
  Finset.prod_nonneg (fun _ _ => circleHeat_nonneg hτ _)

/-- The torus heat kernel is the product of the circle heat kernels. -/
theorem heatKernel_eq_prod_circleHeat {d : ℕ} {τ : ℝ} (hτ : 0 < τ) (x : Torus d) :
    Legacy.BecknerOnofri.HeatDensityApproximation.heatKernel τ x = ∏ j, circleHeat τ (x j) :=
  heatKernel_product hτ x

/-- Splitting the heat kernel along coordinate `i`. -/
theorem heatKernel_update_sub {d : ℕ} {τ : ℝ} (hτ : 0 < τ) (i : Fin d) (x y : Torus d)
    (a b : UnitAddCircle) :
    Legacy.BecknerOnofri.HeatDensityApproximation.heatKernel τ (Function.update x i a - Function.update y i b) =
      circleHeat τ (a - b) * kernelRest τ i x y := by
  rw [heatKernel_eq_prod_circleHeat hτ, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  congr 1
  · simp
  · unfold kernelRest
    apply Finset.prod_congr rfl
    intro j hj
    have : j ≠ i := Finset.ne_of_mem_erase hj
    simp [this]

section Step
open Legacy.BecknerOnofri.HeatDensityApproximation (heatKernel heatKernel_continuous)

variable {d : ℕ}

theorem heatPairing_integrable {τ : ℝ} (hτ : 0 < τ) {f : Torus d → ℝ}
    (hf : Integrable f (torusMeasure d)) :
    Integrable (fun p : Torus d × Torus d => heatKernel τ (p.1 - p.2) * f p.1 * f p.2)
      ((torusMeasure d).prod (torusMeasure d)) := by
  have h := hf.mul_prod hf
  obtain ⟨C, hC⟩ : ∃ C, ∀ x : Torus d, ‖heatKernel τ x‖ ≤ C := by
    obtain ⟨z, -, hz⟩ := isCompact_univ.exists_isMaxOn (f := fun x : Torus d => ‖heatKernel τ x‖)
      univ_nonempty (heatKernel_continuous hτ).norm.continuousOn
    exact ⟨_, fun x => hz (mem_univ x)⟩
  have hm : AEStronglyMeasurable (fun p : Torus d × Torus d => heatKernel τ (p.1 - p.2))
      ((torusMeasure d).prod (torusMeasure d)) :=
    ((heatKernel_continuous hτ).comp (continuous_fst.sub continuous_snd)).aestronglyMeasurable
  have := h.bdd_mul hm (Filter.Eventually.of_forall fun p => hC _)
  refine this.congr (Filter.Eventually.of_forall fun p => ?_)
  simp only [mul_assoc]

/-- The integrand of the double pairing, pulled back to `((x,y),(z,w))`. -/
def pulled (τ : ℝ) (i : Fin d) (f : Torus d → ℝ) (q : (Torus d × Torus d) × (Torus 1 × Torus 1)) : ℝ :=
  heatKernel τ ((fiberMap₂ i q).1 - (fiberMap₂ i q).2) * f (fiberMap₂ i q).1 * f (fiberMap₂ i q).2

/-- The fiber integral at `(x, y)`. -/
def inner (τ : ℝ) (i : Fin d) (f : Torus d → ℝ) (xy : Torus d × Torus d) : ℝ :=
  ∫ zw, pulled τ i f (xy, zw) ∂((torusMeasure 1).prod (torusMeasure 1))

theorem pulled_eq {τ : ℝ} (hτ : 0 < τ) (i : Fin d) (f : Torus d → ℝ)
    (x y : Torus d) (z w : Torus 1) :
    pulled τ i f ((x, y), (z, w)) =
      kernelRest τ i x y *
        (circleHeat τ (z 0 - w 0) * f (fiberMap i (x, z)) * f (fiberMap i (y, w))) := by
  unfold pulled fiberMap₂ fiberMap
  simp only
  rw [heatKernel_update_sub hτ]
  ring

theorem inner_eq {τ : ℝ} (hτ : 0 < τ) (i : Fin d) (f : Torus d → ℝ) (xy : Torus d × Torus d) :
    inner τ i f xy = kernelRest τ i xy.1 xy.2 *
      Circle.interaction (circleHeat τ) (circleFiber i f xy.1) (circleFiber i f xy.2) := by
  unfold inner Circle.interaction
  rw [← integral_const_mul]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun zw => ?_
  obtain ⟨x, y⟩ := xy
  obtain ⟨z, w⟩ := zw
  exact pulled_eq hτ i f x y z w

theorem pulled_integrable {τ : ℝ} (hτ : 0 < τ) (i : Fin d) {f : Torus d → ℝ}
    (hf : Integrable f (torusMeasure d)) :
    Integrable (pulled τ i f)
      (((torusMeasure d).prod (torusMeasure d)).prod ((torusMeasure 1).prod (torusMeasure 1))) :=
  (fiberMap₂_measurePreserving i).integrable_comp_of_integrable (heatPairing_integrable hτ hf)

/-- Pairing with the torus heat kernel as an iterated integral over the coordinates other than `i`
and the fibers in coordinate `i`. -/
theorem pairing_eq_inner {τ : ℝ} (hτ : 0 < τ) (i : Fin d) {f : Torus d → ℝ}
    (hf : Integrable f (torusMeasure d)) :
    pairing (fun x y => heatKernel τ (x - y)) f =
      ∫ xy, inner τ i f xy ∂((torusMeasure d).prod (torusMeasure d)) := by
  have hH := heatPairing_integrable hτ hf
  have hΦ := fiberMap₂_measurePreserving (d := d) i
  have hP := pulled_integrable hτ i hf
  have hmeas : AEStronglyMeasurable (fun p : Torus d × Torus d =>
      heatKernel τ (p.1 - p.2) * f p.1 * f p.2)
      (Measure.map (fiberMap₂ i) (((torusMeasure d).prod (torusMeasure d)).prod
        ((torusMeasure 1).prod (torusMeasure 1)))) := by
    rw [hΦ.map_eq]; exact hH.1
  unfold pairing pairingIntegrand
  calc ∫ p, heatKernel τ (p.1 - p.2) * f p.1 * f p.2 ∂((torusMeasure d).prod (torusMeasure d))
      = ∫ p, heatKernel τ (p.1 - p.2) * f p.1 * f p.2
          ∂(Measure.map (fiberMap₂ i) (((torusMeasure d).prod (torusMeasure d)).prod
            ((torusMeasure 1).prod (torusMeasure 1)))) := by rw [hΦ.map_eq]
    _ = ∫ q, pulled τ i f q ∂(((torusMeasure d).prod (torusMeasure d)).prod
            ((torusMeasure 1).prod (torusMeasure 1))) :=
        integral_map hΦ.measurable.aemeasurable hmeas
    _ = _ := integral_prod _ hP

theorem inner_integrable {τ : ℝ} (hτ : 0 < τ) (i : Fin d) {f : Torus d → ℝ}
    (hf : Integrable f (torusMeasure d)) :
    Integrable (inner τ i f) ((torusMeasure d).prod (torusMeasure d)) :=
  (pulled_integrable hτ i hf).integral_prod_left

end Step

section Mono
open Legacy.BecknerOnofri.HeatDensityApproximation (heatKernel heatKernel_continuous)

theorem interaction_congr {q : UnitAddCircle → ℝ} {f f' g g' : Torus 1 → ℝ}
    (hf : f =ᵐ[torusMeasure 1] f') (hg : g =ᵐ[torusMeasure 1] g') :
    Circle.interaction q f g = Circle.interaction q f' g' := by
  unfold Circle.interaction
  apply integral_congr_ae
  have h1 := (Measure.quasiMeasurePreserving_fst (μ := torusMeasure 1) (ν := torusMeasure 1)).ae hf
  have h2 := (Measure.quasiMeasurePreserving_snd (μ := torusMeasure 1) (ν := torusMeasure 1)).ae hg
  filter_upwards [h1, h2] with p h1 h2
  rw [h1, h2]

/-- Lemma 2.8 for the circle heat kernel, in the form used per fiber pair. -/
theorem interaction_le_of_rearr {τ : ℝ} (hτ : 0 < τ) {f g f' g' : Torus 1 → ℝ}
    (hf : Integrable f (torusMeasure 1)) (hg : Integrable g (torusMeasure 1))
    (hf0 : ∀ᵐ x ∂torusMeasure 1, 0 ≤ f x) (hg0 : ∀ᵐ x ∂torusMeasure 1, 0 ≤ g x)
    (hf' : Circle.realRearrange f =ᵐ[torusMeasure 1] f')
    (hg' : Circle.realRearrange g =ᵐ[torusMeasure 1] g') :
    Circle.interaction (circleHeat τ) f g ≤ Circle.interaction (circleHeat τ) f' g' := by
  obtain ⟨C, hC⟩ := circleHeat_bounded hτ
  obtain ⟨-, -, -, -, -, -, -, -, h, -⟩ := Circle.circle_rearrangement f g hf hg hf0 hg0
    (circleHeat τ) (C := C) (circleHeat_nonneg hτ) hC
    (fun x y hxy => circleHeat_radial_antitone hτ hxy)
  exact h.trans_eq (interaction_congr hf' hg')

variable {d : ℕ}

/-- **One coordinate step increases every heat pairing** (`eq:coordinate-heat-comparison`). -/
theorem heat_pairing_step_le {τ : ℝ} (hτ : 0 < τ) (i : Fin d) {r s : Torus d → ℝ}
    (hr : Integrable r (torusMeasure d)) (hs : Integrable s (torusMeasure d))
    (hr0 : ∀ᵐ x ∂torusMeasure d, 0 ≤ r x)
    (hstep : AECanonicalStep i r s) :
    pairing (fun x y => heatKernel τ (x - y)) r ≤ pairing (fun x y => heatKernel τ (x - y)) s := by
  rw [pairing_eq_inner hτ i hr, pairing_eq_inner hτ i hs]
  refine integral_mono_ae (inner_integrable hτ i hr) (inner_integrable hτ i hs) ?_
  have hF := fiberMap_measurePreserving (d := d) i
  have hrF : Integrable (fun p => r (fiberMap i p)) ((torusMeasure d).prod (torusMeasure 1)) :=
    hF.integrable_comp_of_integrable hr
  have hI : ∀ᵐ x ∂torusMeasure d, Integrable (circleFiber i r x) (torusMeasure 1) :=
    hrF.prod_right_ae
  have hN : ∀ᵐ x ∂torusMeasure d, ∀ᵐ z ∂torusMeasure 1, 0 ≤ circleFiber i r x z :=
    Measure.ae_ae_of_ae_prod (hF.quasiMeasurePreserving.ae hr0)
  have hA : ∀ᵐ x ∂torusMeasure d, Integrable (circleFiber i r x) (torusMeasure 1) ∧
      (∀ᵐ z ∂torusMeasure 1, 0 ≤ circleFiber i r x z) ∧
      Circle.realRearrange (circleFiber i r x) =ᵐ[torusMeasure 1] circleFiber i s x := by
    filter_upwards [hI, hN, hstep] with x h1 h2 h3 using ⟨h1, h2, h3⟩
  have h1 := (Measure.quasiMeasurePreserving_fst (μ := torusMeasure d) (ν := torusMeasure d)).ae hA
  have h2 := (Measure.quasiMeasurePreserving_snd (μ := torusMeasure d) (ν := torusMeasure d)).ae hA
  filter_upwards [h1, h2] with p ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩
  rw [inner_eq hτ i r p, inner_eq hτ i s p]
  exact mul_le_mul_of_nonneg_left (interaction_le_of_rearr hτ a1 b1 a2 b2 a3 b3)
    (kernelRest_nonneg hτ i _ _)

end Mono

end BecknerOnofri.V2.Rearrangement
