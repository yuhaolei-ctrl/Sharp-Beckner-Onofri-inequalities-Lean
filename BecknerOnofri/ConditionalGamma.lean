module

public import BecknerOnofri.ConditionalLogProfile
public import BecknerOnofri.ConditionalFourierRegularity
public import BecknerOnofri.CircleGammaProfile

@[expose] public section

/-! The circle gamma estimate applied to the actual normalized conditional
circle, with its profile and regularity derived from the joint density. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped ContDiff
namespace BecknerOnofri.HighDim.ConditionalEntropy
open EntropyShearer Legacy.TorusEndpoint Legacy.BecknerOnofri.RadialWiener

theorem conditional_gamma {d : ℕ} (V : (Fin d → ℝ) → ℝ)
    (hc : ContinuousOn V (cosineCube d))
    (hconv : ∀ v ∈ cosineCube d, ∀ i : Fin d,
      ConvexOn ℝ (Icc (-1 : ℝ) 1) (fun t => V (Function.update v i t)))
    (hmono : ∀ v ∈ cosineCube d, ∀ i : Fin d,
      MonotoneOn (fun t => V (Function.update v i t)) (Icc (-1 : ℝ) 1))
    (f : Torus d → ℝ) (hrep : ∀ x, f x = Real.exp (V (cosineVector x)))
    (a : Frequency d → ℂ) (ha : ∀ m : ℕ, RadialSummable a m)
    (he : ∀ x, (f x : ℂ) = absoluteFourierSeries a x)
    (i : Fin d) (x : Torus d) :
    2 * Spin.binaryCost (conditionalCosineMoment f i 1 x) +
      CircleScalar.gamma (conditionalCosineMoment f i 1 x) +
      (21/1000) * (conditionalCosineMoment f i 2 x)^2 +
      (67/100) * (∑' n : ℕ, (conditionalCosineMoment f i (n+3) x)^2 / (n+3 : ℝ)) ≤
        conditionalEntropy f i x := by
  obtain ⟨F, hcF, hF, hmF, hprofile⟩ := conditional_log_profile V hc hconv hmono f hrep i x
  let p : Torus 1 → ℝ := fun z => conditionalDensity f i x (z 0)
  have hp : Continuous p := by
    have hcos : Continuous (fun z : Torus 1 => (fourier 1 (z 0)).re) := by fun_prop
    have hcirc : Continuous (fun z : Torus 1 => F (fourier 1 (z 0)).re) :=
      hcF.comp_continuous hcos (fun z => ⟨(cosineVector_mem z).1 0, (cosineVector_mem z).2 0⟩)
    have heq : p = fun z => Real.exp (F (fourier 1 (z 0)).re) := funext (fun z => hprofile (z 0))
    rw [heq]
    exact Real.continuous_exp.comp hcirc
  have hf : Continuous f := by
    have h := hc.comp_continuous (cosineVector_continuous d) (fun y => cosineVector_mem y)
    have heq : f = fun y => Real.exp (V (cosineVector y)) := funext hrep
    rw [heq]
    exact Real.continuous_exp.comp h
  have hfpos : PositiveBounded f := positiveBounded_of_continuous_pos hf
    (fun y => by rw [hrep]; exact Real.exp_pos _)
  have hmass : (∫ z, p z ∂torusMeasure 1) = 1 := by
    rw [CirclePoisson.integral_torus_circle]
    exact conditional_density_mass hfpos i x
  have hreg : ContDiff ℝ 3 (fun t : ℝ => p (fun _ => (t : UnitAddCircle))) :=
    (conditional_density_contDiff a ha f he i x).of_le (WithTop.coe_le_coe.mpr (le_top : (3 : ℕ∞) ≤ ⊤))
  have hmom (n : ℕ) : CirclePoisson.moment p n = conditionalCosineMoment f i n x :=
    CirclePoisson.moment_eq_cosine_integral p hp n
  have h := CirclePoisson.gamma_entropy_of_convex_profile p hp hmass hreg F hcF hF hmF
    (fun z => hprofile (z 0))
  simpa only [hmom, CirclePoisson.integral_torus_circle, p, conditionalEntropy] using h

#print axioms conditional_gamma
end BecknerOnofri.HighDim.ConditionalEntropy
