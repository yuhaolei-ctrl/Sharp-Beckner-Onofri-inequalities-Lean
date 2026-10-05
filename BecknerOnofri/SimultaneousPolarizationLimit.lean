module

public import BecknerOnofri.PolarizationOrbitL1
public import BecknerOnofri.BilinearPairingL1Limit

@[expose] public section

/-! One common reflection sequence for both functions, and passage of the
bounded-kernel comparison to actual L1 limits. -/
noncomputable section
open MeasureTheory Filter Legacy.TorusEndpoint
open scoped Topology
namespace BecknerOnofri.PolarizationL1
open Legacy.BecknerOnofri.CoordinatePolarization

def iterate {d : ℕ} (s : ℕ → Fin d × ℝ) (f : Torus d → ℝ) : ℕ → Torus d → ℝ
  | 0 => f
  | n+1 => polarize (s n).1 (s n).2 (iterate s f n)

theorem iterate_orbit {d : ℕ} (s : ℕ → Fin d × ℝ) (f : Torus d → ℝ) (n : ℕ) :
    Orbit f (iterate s f n) := by
  induction n with
  | zero => exact Orbit.refl
  | succ n ih => exact Orbit.step ih (s n).1 (s n).2

theorem iterate_integrable {d : ℕ} (s : ℕ → Fin d × ℝ) {f : Torus d → ℝ}
    (hf : Integrable f (torusMeasure d)) (n : ℕ) :
    Integrable (iterate s f n) (torusMeasure d) :=
  ((iterate_orbit s f n).identDistrib hf.aestronglyMeasurable).integrable_iff.mpr hf

theorem iterate_mono_ae {d : ℕ} (s : ℕ → Fin d × ℝ) {f g : Torus d → ℝ}
    (h : f≤ᵐ[torusMeasure d] g) (n : ℕ) :
    iterate s f n≤ᵐ[torusMeasure d] iterate s g n := by
  induction n with
  | zero => exact h
  | succ n ih => exact polarize_mono_ae (s n).1 (s n).2 ih

theorem iterate_l1_contraction {d : ℕ} (s : ℕ → Fin d × ℝ) {f g : Torus d → ℝ}
    (hf : Integrable f (torusMeasure d)) (hg : Integrable g (torusMeasure d)) (n : ℕ) :
    (∫ x,|iterate s f n x-iterate s g n x| ∂torusMeasure d)≤
      ∫ x,|f x-g x| ∂torusMeasure d := by
  induction n with
  | zero => exact le_refl _
  | succ n ih => exact (polarize_l1_contraction (s n).1 (s n).2 _ _
      (iterate_integrable s hf n) (iterate_integrable s hg n)).trans ih

open BilinearPolarization

theorem iterate_pairing_le {d : ℕ} (s : ℕ → Fin d × ℝ)
    (K : Torus d → Torus d → ℝ) (hm : Measurable (Function.uncurry K))
    {C : ℝ} (hC : ∀ x y,‖K x y‖≤C)
    (hK : ∀ n x y,K (reflection (s n).1 (s n).2 x) (reflection (s n).1 (s n).2 y)=K x y)
    (hmono : ∀ n,∀ x∈halfTorus (s n).1 (s n).2,∀ y∈halfTorus (s n).1 (s n).2,
      K x (reflection (s n).1 (s n).2 y)≤K x y)
    {f g : Torus d → ℝ} (hf : Integrable f (torusMeasure d)) (hg : Integrable g (torusMeasure d))
    (n : ℕ) : pairing K f g≤pairing K (iterate s f n) (iterate s g n) := by
  induction n with
  | zero => exact le_refl _
  | succ n ih => exact ih.trans (pairing_polarize_le_bounded (s n).1 (s n).2 K hm hC
      (hK n) (hmono n) (iterate_integrable s hf n) (iterate_integrable s hg n))

/-- A simultaneous L1 polarization limit inherits the two-function inequality.
No canonical-rearrangement existence is presupposed in this auxiliary lemma. -/
theorem limit_pairing_le {d : ℕ} (s : ℕ → Fin d × ℝ)
    (K : Torus d → Torus d → ℝ) (hm : Measurable (Function.uncurry K))
    {C : ℝ} (hC : ∀ x y,‖K x y‖≤C)
    (hK : ∀ n x y,K (reflection (s n).1 (s n).2 x) (reflection (s n).1 (s n).2 y)=K x y)
    (hmono : ∀ n,∀ x∈halfTorus (s n).1 (s n).2,∀ y∈halfTorus (s n).1 (s n).2,
      K x (reflection (s n).1 (s n).2 y)≤K x y)
    {f g f₀ g₀ : Torus d → ℝ}
    (hf : Integrable f (torusMeasure d)) (hg : Integrable g (torusMeasure d))
    (hf₀ : Integrable f₀ (torusMeasure d)) (hg₀ : Integrable g₀ (torusMeasure d))
    (hfL : Tendsto (fun n => ∫ x,‖iterate s f n x-f₀ x‖ ∂torusMeasure d) atTop (𝓝 0))
    (hgL : Tendsto (fun n => ∫ x,‖iterate s g n x-g₀ x‖ ∂torusMeasure d) atTop (𝓝 0)) :
    pairing K f g≤pairing K f₀ g₀ := by
  have ht := pairing_l1_limit atTop K hm hC (iterate s f) (iterate s g) f₀ g₀
    (iterate_integrable s hf) (iterate_integrable s hg) hf₀ hg₀ hfL hgL
  exact le_of_tendsto_of_tendsto tendsto_const_nhds ht
    (Filter.Eventually.of_forall (iterate_pairing_le s K hm hC hK hmono hf hg))

#print axioms iterate_l1_contraction
#print axioms iterate_mono_ae
#print axioms limit_pairing_le
end BecknerOnofri.PolarizationL1
