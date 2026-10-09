module

public import BecknerOnofri.V2.FiniteState.AffineCurvature
public import BecknerOnofri.SpinEntropyConvexity

@[expose] public section

/-!
# Corollary 5.18 re-derived from the affine-residual curvature (Lemma 5.17)

Compiled (sorry-free).  The proof is the proof of `Spin.fixed_mean_entropy_convexity` with the
single curvature input replaced by `fixed_mean_curvature_affine`, so that no theorem whose
dependency trace contains `Spin.fixed_mean_curvature` is used.  The generic ingredients
(`functional_segment_derivative`, `entropy_segment_second_derivative`, `second_order_support`,
`entropy_bregman_identity`, `slope_at_zero_eq_gradient`, `feasible_segment`, `segment_positive`)
are reused unchanged.  The target `q` may have zero coordinates; positivity is assumed only for `p`.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open Set
namespace BecknerOnofri.V2.FiniteState
open BecknerOnofri.HighDim.Spin

theorem fixed_mean_entropy_convexity_affine {p q : Count → ℝ}
    (hp : Feasible p) (hpos : ∀ j, 0 < p j) (hq : Feasible q) (hmean : mean p = mean q) :
    functional p + (∑ j : Count, gradient p j * (q j - p j)) +
      relativeEntropy q p / 5 ≤ functional q := by
  let v := q - p
  let f : ℝ → ℝ := fun t => functional (p + t • v) - relativeEntropy (p + t • v) reference / 5
  let f' : ℝ → ℝ := fun t => functionalSlope p v t - entropySlope p v t / 5
  let f'' : ℝ → ℝ := fun t => functionalHessian p v t - entropyHessian p v t / 5
  have hv : (∑ j : Count, v j) = 0 := by
    simp [v, Finset.sum_sub_distrib, hp.2.1, hq.2.1]
  have hvx : mean v = 0 := by simp [v, mean_sub, hmean]
  have hcont : Continuous f := (functional_segment_continuous p v).sub
    ((relativeEntropy_reference_continuous.comp (by fun_prop)).div_const 5)
  have hd (t : ℝ) (ht : ∀ j, 0 < p j + t * v j) : HasDerivAt f (f' t) t :=
    (functional_segment_derivative p v t ht).sub ((entropy_segment_derivative p v t ht).div_const 5)
  have hdd (t : ℝ) (ht : ∀ j, 0 < p j + t * v j) : HasDerivAt f' (f'' t) t :=
    (functional_segment_second_derivative p v t ht).sub
      ((entropy_segment_second_derivative p v t ht).div_const 5)
  have hb (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) : 0 ≤ f'' t := by
    have hr := feasible_segment hp hq ⟨ht.1.le, ht.2.le⟩
    have hrpos : ∀ j, 0 < (p + t • v) j := segment_positive hpos hq ht.1.le ht.2
    have hc := fixed_mean_curvature_affine hr hrpos hv hvx      -- <-- the v2 curvature theorem
    change quadratic v ≤ (9 / 10) * entropyHessian p v t at hc
    dsimp [f'', functionalHessian]
    linarith
  have h := second_order_support hcont.continuousOn (hd 0 (by simpa using hpos))
    (fun t ht => hd t (segment_positive hpos hq ht.1.le ht.2))
    (fun t ht => hdd t (segment_positive hpos hq ht.1.le ht.2)) hb
  have he : p + (1 : ℝ) • v = q := by dsimp [v]; module
  simp only [f, f', zero_smul, add_zero, he, zero_div] at h
  have hB := entropy_bregman_identity hpos hp.2.1 hq.2.1
  have hG := slope_at_zero_eq_gradient p v hpos
  change functionalSlope p v 0 = (∑ j : Count, gradient p j * (q j - p j)) at hG
  change relativeEntropy q reference - relativeEntropy p reference - entropySlope p v 0 =
    relativeEntropy q p at hB
  linarith

end BecknerOnofri.V2.FiniteState
