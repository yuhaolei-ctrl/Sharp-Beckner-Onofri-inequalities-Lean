import BecknerOnofri.LipschitzUniformDensity
import BecknerOnofri.PolarizationUniformL1
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-! Nonnegative Lipschitz approximation in the actual normalized Haar L1
metric, for arbitrary nonnegative integrable torus functions. -/
noncomputable section
open MeasureTheory Set Filter Legacy.TorusEndpoint
open scoped Topology NNReal BoundedContinuousFunction
namespace BecknerOnofri.RearrangementApproximation

theorem exists_lipschitz_l1_approx {d : ℕ} {f : Torus d → ℝ}
    (hf : Integrable f (torusMeasure d)) {ε : ℝ} (hε : 0<ε) :
    ∃ g : Torus d →ᵇ ℝ,(∃ K : ℝ≥0,LipschitzWith K g) ∧
      (∫ x,‖f x-g x‖ ∂torusMeasure d)≤ε := by
  obtain ⟨u,hu,hui⟩ := hf.exists_boundedContinuous_integral_sub_le (half_pos hε)
  obtain ⟨v,⟨K,hK⟩,hv⟩ := exists_lipschitz_uniform_approx u.toContinuousMap (half_pos hε)
  let g : Torus d →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact v
  have hgi : Integrable g (torusMeasure d) := g.integrable _
  have huv : (∫ x,‖u x-g x‖ ∂torusMeasure d)≤ε/2 := by
    have h := integral_mono ((hui.sub hgi).norm) (integrable_const (ε/2)) (fun x => (hv x).le)
    simpa using h
  refine ⟨g,⟨K,hK⟩,?_⟩
  calc
    _ ≤ ∫ x,(‖f x-u x‖+‖u x-g x‖) ∂torusMeasure d :=
      integral_mono ((hf.sub hgi).norm) (((hf.sub hui).norm).add ((hui.sub hgi).norm))
        (fun x => norm_sub_le_norm_sub_add_norm_sub (f x) (u x) (g x))
    _ = (∫ x,‖f x-u x‖ ∂torusMeasure d)+(∫ x,‖u x-g x‖ ∂torusMeasure d) :=
      integral_add ((hf.sub hui).norm) ((hui.sub hgi).norm)
    _ ≤ ε := by linarith

theorem exists_nonnegative_lipschitz_l1_approx {d : ℕ} {f : Torus d → ℝ}
    (hf : Integrable f (torusMeasure d)) (hf0 : ∀ᵐ x ∂torusMeasure d,0≤f x)
    {ε : ℝ} (hε : 0<ε) :
    ∃ g : Torus d →ᵇ ℝ,(∃ K : ℝ≥0,LipschitzWith K g) ∧ (∀ x,0≤g x) ∧
      (∫ x,‖f x-g x‖ ∂torusMeasure d)≤ε := by
  obtain ⟨u,⟨K,hK⟩,hu⟩ := exists_lipschitz_l1_approx hf hε
  let g : Torus d →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
    ⟨fun x => max (u x) 0,u.continuous.max continuous_const⟩
  have hL : LipschitzWith (max K 0) g := hK.max (LipschitzWith.const 0)
  refine ⟨g,⟨max K 0,hL⟩,fun x => le_max_right _ _,le_trans ?_ hu⟩
  apply integral_mono_ae ((hf.sub (g.integrable _)).norm) ((hf.sub (u.integrable _)).norm)
  filter_upwards [hf0] with x hx
  change ‖f x-max (u x) 0‖≤‖f x-u x‖
  by_cases hu0 : 0≤u x
  · rw [max_eq_left hu0]
  · rw [max_eq_right (le_of_not_ge hu0),sub_zero,Real.norm_eq_abs,abs_of_nonneg hx,
      Real.norm_eq_abs,abs_of_nonneg (by linarith)]
    linarith

#print axioms exists_lipschitz_l1_approx
#print axioms exists_nonnegative_lipschitz_l1_approx
end BecknerOnofri.RearrangementApproximation
