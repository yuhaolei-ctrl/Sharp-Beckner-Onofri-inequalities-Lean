module

public import BecknerOnofri.GeneralEuler.Regularity
public import BecknerOnofri.GeneralEuler.SpectralIntertwining
public import BecknerOnofri.GeneralEuler.UnitProfiles
public import Legacy.BecknerOnofri.NormalizedExponentialPartials
public import Legacy.BecknerOnofri.BoundedL2Multiplier

@[expose] public section

/-! The genuine bounded positive square-root Gibbs weight on the angular cube,
and the exact normalized Bell formula for its differentiated density. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
open Legacy.BecknerOnofri
namespace BecknerOnofri.GeneralEuler.WeightedEquation
open Legacy.TorusEndpoint TorusSobolev SubcriticalAttainment SubcriticalEuler
open WienerFourier SmoothFourier SteinerSelection FiniteDifferences
open AngularMixedTerms AngularMixedL2 JacobiTensor JacobiTensorSpectrum
open BoundedL2Multiplier MixedExponentialDerivatives

def rhoAngular {d : ℕ} (u : TorusL2 d) (x : Fin d → ℝ) : ℝ := BecknerOnofri.GeneralEuler.UnitProfiles.density u (angularCube x)
def sqrtDensity {d : ℕ} (u : TorusL2 d) (x : Fin d → ℝ) : ℝ := Real.sqrt (rhoAngular u x)

theorem angularCube_continuous (d : ℕ) : Continuous (@angularCube d) := by
  apply continuous_pi
  intro i
  exact (continuous_const.add (Real.continuous_cos.comp (continuous_apply i))).div_const 2

theorem angularWeight_nonnegative {d : ℕ} (is : List (Fin d)) {x : Fin d → ℝ}
    (hx : ∀ i, x i ∈ Ioo 0 Real.pi) : 0 ≤ weight is x := by
  unfold weight
  exact Finset.prod_nonneg (fun i _ => pow_nonneg (Real.sin_pos_of_pos_of_lt_pi (hx i).1 (hx i).2).le _)

variable {d : ℕ} (hd : 0 < d) {b Ab A : ℝ}
  (hR : RoughExponentialBound d b Ab) (hA : 0 < A) {u : TorusL2 d}
  (hu : SubcriticalAttainment.Admissible u)
  (hE : Regularity.Data A u)
  (hStR : Steiner (smoothGibbsValue u))

include hd hR hA hu hE hStR

theorem rhoAngular_pos (x : Fin d → ℝ) : 0 < rhoAngular u x :=
  BecknerOnofri.GeneralEuler.UnitProfiles.density_pos hd hR hA hu hE hStR (angularCube_mem x)

theorem rhoAngular_continuous : Continuous (rhoAngular u) :=
  (BecknerOnofri.GeneralEuler.UnitProfiles.density_contDiffOn hd hR hA hu hE hStR).continuousOn.comp_continuous
    (angularCube_continuous d) angularCube_mem

theorem sqrtDensity_continuous : Continuous (sqrtDensity u) :=
  (rhoAngular_continuous hd hR hA hu hE hStR).sqrt

theorem sqrtDensity_pos (x : Fin d → ℝ) : 0 < sqrtDensity u x :=
  Real.sqrt_pos.mpr (rhoAngular_pos hd hR hA hu hE hStR x)

theorem sqrtDensity_bounded : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Fin d → ℝ, ‖sqrtDensity u x‖ ≤ C := by
  have hc := (BecknerOnofri.GeneralEuler.UnitProfiles.density_contDiffOn hd hR hA hu hE hStR).continuousOn.sqrt
  obtain ⟨C,hC⟩ := (isCompact_Icc : IsCompact (FiniteDifferences.closedCube d)).exists_bound_of_continuousOn hc
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  exact (hC _ (angularCube_mem x)).trans (le_max_left _ _)

def sqrtDensityWeight : BoundedL2Multiplier.Weight (JacobiTensor.measure d) where
  value := sqrtDensity u
  measurable := (sqrtDensity_continuous hd hR hA hu hE hStR).aestronglyMeasurable
  bound := (sqrtDensity_bounded hd hR hA hu hE hStR).choose
  nonneg_bound := (sqrtDensity_bounded hd hR hA hu hE hStR).choose_spec.1
  bounded := ae_of_all _ (sqrtDensity_bounded hd hR hA hu hE hStR).choose_spec.2

@[simp] theorem sqrtDensityWeight_value : (sqrtDensityWeight hd hR hA hu hE hStR).value = sqrtDensity u := rfl

theorem sqrtDensity_sq (x : Fin d → ℝ) : (sqrtDensity u x)^2 = rhoAngular u x :=
  Real.sq_sqrt (rhoAngular_pos hd hR hA hu hE hStR x).le

theorem normalized_gibbs_mixed (hStU : Steiner (fun x => (representative u x).re))
    (is : List (Fin d)) (his : is ≠ []) {y : Fin d → ℝ} (hy : y ∈ closedCube d) :
    mixedPartial is (BecknerOnofri.GeneralEuler.UnitProfiles.density u) y =
      BecknerOnofri.GeneralEuler.UnitProfiles.density u y *
        (mixedPartial is (BecknerOnofri.GeneralEuler.UnitProfiles.potential u) y +
          evalTerms (BecknerOnofri.GeneralEuler.UnitProfiles.potential u) (remainderTerms is) y) := by
  have hcont := BecknerOnofri.GeneralEuler.UnitProfiles.potential_contDiffOn hd hR hA hu hE hStU
  have he : EqOn (BecknerOnofri.GeneralEuler.UnitProfiles.density u)
      (fun y => (partition u)⁻¹ * Real.exp (BecknerOnofri.GeneralEuler.UnitProfiles.potential u y)) (closedCube d) := by
    intro y hy
    rw [BecknerOnofri.GeneralEuler.UnitProfiles.density_eq_exp hd hR hA hu hE hStU hStR hy]
    ring
  rw [NormalizedExponentialPartials.mixedPartial_congr is he hy,
    NormalizedExponentialPartials.mixedPartial_const_mul is _ hcont.exp hy,
    mixedPartial_exp_formula hcont is his hy,he hy]
  ring

#print axioms sqrtDensityWeight
#print axioms normalized_gibbs_mixed
end BecknerOnofri.GeneralEuler.WeightedEquation
