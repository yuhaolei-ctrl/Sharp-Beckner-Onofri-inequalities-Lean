import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! Distinct active affine supporting lines preclude differentiability. -/
noncomputable section
open Filter
open scoped Topology
namespace BecknerOnofri
lemma not_differentiable_of_two_supports {f : ℝ → ℝ} {a s : ℝ}
    (hs : s ≠ 0) (hf : f a = 0)
    (h0 : ∀ᶠ x in 𝓝 a, 0 ≤ f x)
    (hline : ∀ᶠ x in 𝓝 a, (x-a)*s ≤ f x) : ¬ DifferentiableAt ℝ f a := by
  intro hd
  have hm : IsLocalMin f a := by
    change ∀ᶠ x in 𝓝 a, f a ≤ f x
    simpa only [hf] using h0
  have hz := hm.hasDerivAt_eq_zero hd.hasDerivAt
  have hm' : IsLocalMin (fun x => f x-(x-a)*s) a := by
    change ∀ᶠ x in 𝓝 a, f a-(a-a)*s ≤ f x-(x-a)*s
    filter_upwards [hline] with x hx
    rw [hf, sub_self, zero_mul, sub_zero]
    linarith
  have hh := hm'.hasDerivAt_eq_zero
    (hd.hasDerivAt.sub (((hasDerivAt_id a).sub_const a).mul_const s))
  simp only [one_mul, hz, zero_sub, neg_eq_zero] at hh
  exact hs hh
end BecknerOnofri
