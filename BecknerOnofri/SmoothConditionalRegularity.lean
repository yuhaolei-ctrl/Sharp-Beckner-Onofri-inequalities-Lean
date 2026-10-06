module

public import BecknerOnofri.CompactCubeHaarIntegral
public import BecknerOnofri.ConditionalEntropyDefinitions
public import BecknerOnofri.UniformFourierHessian

@[expose] public section

/-! Conditional-circle smoothness directly from smoothness of the raw torus
function, without a Fourier decay representation as an extra hypothesis. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Function
open scoped ContDiff
namespace BecknerOnofri.HighDim.ConditionalEntropy

/-- Integration of future coordinates preserves the actual smooth circle lift. -/
theorem smooth_prefix_section {d : ℕ} (f : Torus d → ℝ) (hs : SmoothOnTorus f)
    (i : Fin d) (x : Torus d) :
    ContDiff ℝ ∞ (fun t : ℝ => prefixDensity f (i.val+1) (Function.update x i (t : UnitAddCircle))) := by
  classical
  let S := suffixCoordinates d (i.val+1)
  let xr : Fin d → ℝ := fun j => AddCircle.equivIoc 1 0 (x j)
  have hxr (j : Fin d) : (xr j : UnitAddCircle)=x j := AddCircle.coe_equivIoc
  let L : ℝ × (S → ℝ) → Fin d → ℝ := fun p j =>
    if hj : j∈S then p.2 ⟨j,hj⟩ else if j=i then p.1 else xr j
  have hL : ContDiff ℝ ∞ L := by
    apply contDiff_pi.mpr
    intro j
    dsimp only [L]
    split_ifs <;> fun_prop
  let F : ℝ × (S → ℝ) → ℝ := fun p => f (fun j => (L p j : UnitAddCircle))
  have hF : ContDiff ℝ ∞ F := hs.comp hL
  let G : ℝ → (S → UnitAddCircle) → ℝ := fun t y =>
    f (updateFinset (Function.update x i (t : UnitAddCircle)) S y)
  have hG (t : ℝ) : Continuous (G t) := by
    apply (UniformFourier.smooth_continuous hs).comp
    apply continuous_pi
    intro j
    simp only [updateFinset]
    split_ifs <;> fun_prop
  have he (t : ℝ) (y : S → ℝ) : F (t,y)=G t (fun j => (y j : UnitAddCircle)) := by
    apply congrArg f
    funext j
    simp only [L,updateFinset,Function.update_apply]
    split_ifs <;> simp_all only [hxr]
  exact CompactParameter.haar_parameter_contDiff G hG F hF he

/-- The conditional density itself is smooth even without positivity;
the denominator is constant in the free circle coordinate. -/
theorem smooth_conditional_density {d : ℕ} (f : Torus d → ℝ) (hs : SmoothOnTorus f)
    (i : Fin d) (x : Torus d) :
    ContDiff ℝ ∞ (fun t : ℝ => conditionalDensity f i x (t : UnitAddCircle)) :=
  (smooth_prefix_section f hs i x).div_const (prefixDensity f i.val x)

#print axioms smooth_prefix_section
#print axioms smooth_conditional_density
end BecknerOnofri.HighDim.ConditionalEntropy
