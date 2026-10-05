import BecknerOnofri.SimultaneousSteinerSelection
import BecknerOnofri.SimultaneousOrbitComparison
import BecknerOnofri.CircleSteinerUniqueness

/-! Canonical symmetric decreasing rearrangement for Lipschitz circle
functions, obtained by the manuscript's simultaneous polarization route. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Legacy.TorusEndpoint
open scoped Topology NNReal BoundedContinuousFunction
namespace BecknerOnofri.PolarizationL1
open Legacy.BecknerOnofri CoordinatePolarization BilinearPolarization

def rearrangeLipschitz (f : Torus 1 → ℝ) {K : ℝ≥0} (hf : LipschitzWith K f) :
    Torus 1 →ᵇ ℝ := Classical.choose (exists_steiner_orbit_limit f hf)

theorem rearrangeLipschitz_spec (f : Torus 1 → ℝ) {K : ℝ≥0} (hf : LipschitzWith K f) :
    rearrangeLipschitz f hf∈closure (boundedOrbit f) ∧
      LipschitzWith K (rearrangeLipschitz f hf) ∧
      IdentDistrib (rearrangeLipschitz f hf) f (torusMeasure 1) (torusMeasure 1) ∧
      SteinerSelection.Steiner (rearrangeLipschitz f hf) :=
  Classical.choose_spec (exists_steiner_orbit_limit f hf)

theorem rearrangeLipschitz_pair_closure (f g : Torus 1 → ℝ) {K L : ℝ≥0}
    (hf : LipschitzWith K f) (hg : LipschitzWith L g) :
    (rearrangeLipschitz f hf,rearrangeLipschitz g hg)∈closure (boundedPairOrbit f g) := by
  obtain ⟨p,hp,_,_,hfD,hgD,hfP,hgP⟩ := exists_pair_fixed_orbit_limit f g hf hg
  have hfS := SteinerSelection.steiner_of_origin_invariant p.1.continuous hfP
  have hgS := SteinerSelection.steiner_of_origin_invariant p.2.continuous hgP
  have h1 : p.1=rearrangeLipschitz f hf := by
    apply DFunLike.coe_injective
    exact steiner_eq_of_identDistrib p.1.continuous (rearrangeLipschitz f hf).continuous
      hfS (rearrangeLipschitz_spec f hf).2.2.2
      (hfD.trans (rearrangeLipschitz_spec f hf).2.2.1.symm)
  have h2 : p.2=rearrangeLipschitz g hg := by
    apply DFunLike.coe_injective
    exact steiner_eq_of_identDistrib p.2.continuous (rearrangeLipschitz g hg).continuous
      hgS (rearrangeLipschitz_spec g hg).2.2.2
      (hgD.trans (rearrangeLipschitz_spec g hg).2.2.1.symm)
  simpa only [← h1,← h2,Prod.mk.eta] using hp

theorem rearrangeLipschitz_mono (f g : Torus 1 → ℝ) {K L : ℝ≥0}
    (hf : LipschitzWith K f) (hg : LipschitzWith L g) (hfg : ∀ x,f x≤g x) :
    ∀ x,rearrangeLipschitz f hf x≤rearrangeLipschitz g hg x :=
  pair_closure_mono (rearrangeLipschitz_pair_closure f g hf hg) hfg

theorem rearrangeLipschitz_l1_contraction (f g : Torus 1 → ℝ) {K L : ℝ≥0}
    (hf : LipschitzWith K f) (hg : LipschitzWith L g) :
    (∫ x,‖rearrangeLipschitz f hf x-rearrangeLipschitz g hg x‖ ∂torusMeasure 1)≤
      ∫ x,‖f x-g x‖ ∂torusMeasure 1 :=
  pair_closure_l1_contraction
    (hf.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (hg.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (rearrangeLipschitz_pair_closure f g hf hg)

/-- The kernel is an actual bounded measurable function on the circle.
Monotonicity in the actual circle norm includes evenness. -/
theorem rearrangeLipschitz_circle_pairing (q : UnitAddCircle → ℝ) (hm : Measurable q)
    {C : ℝ} (hC : ∀ z,‖q z‖≤C) (hq : ∀ x y,‖x‖≤‖y‖ → q y≤q x)
    (f g : Torus 1 → ℝ) {K L : ℝ≥0}
    (hf : LipschitzWith K f) (hg : LipschitzWith L g) :
    pairing (fun x y : Torus 1 => q (x 0-y 0)) f g≤
      pairing (fun x y : Torus 1 => q (x 0-y 0)) (rearrangeLipschitz f hf) (rearrangeLipschitz g hg) := by
  have hqm : Measurable (Function.uncurry (fun x y : Torus 1 => q (x 0-y 0))) := by
    have hs : Continuous (fun p : Torus 1 × Torus 1 => p.1 0-p.2 0) := by fun_prop
    exact hm.comp hs.measurable
  apply pair_closure_pairing_le (fun x y : Torus 1 => q (x 0-y 0)) hqm
    (fun x y => hC (x 0-y 0)) ?_ ?_
    (hf.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (hg.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (rearrangeLipschitz_pair_closure f g hf hg)
  · intro i a x y
    have hi : i=0 := Subsingleton.elim _ _
    subst i
    have he : ‖reflection 0 a x 0-reflection 0 a y 0‖=‖x 0-y 0‖ := by
      simpa only [reflection,ite_true,dist_eq_norm] using circleReflection_dist a (x 0) (y 0)
    exact le_antisymm (hq _ _ he.ge) (hq _ _ he.le)
  · intro i a x hx y hy
    have hi : i=0 := Subsingleton.elim _ _
    subst i
    apply hq
    simpa only [reflection,ite_true,dist_eq_norm] using circle_dist_half a hx hy

#print axioms rearrangeLipschitz_mono
#print axioms rearrangeLipschitz_l1_contraction
#print axioms rearrangeLipschitz_circle_pairing
end BecknerOnofri.PolarizationL1
