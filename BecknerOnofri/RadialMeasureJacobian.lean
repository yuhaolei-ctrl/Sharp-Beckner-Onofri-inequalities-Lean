import BecknerOnofri.ArcsineProductBins
import Legacy.BecknerOnofri.TorusLogIntegrability
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Tactic

/-! The actual inverse-sine change of variables and its radial Jacobian bound. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace BecknerOnofri.HighDim.RadialMeasure

def squareRadius {d : ℕ} (y : Fin d → ℝ) : ℝ := ∑ i, (y i)^2

def unitBall (d : ℕ) : Set (Fin d → ℝ) := {y | squareRadius y < 1}

def inverseSine {d : ℕ} (y : Fin d → ℝ) : Fin d → ℝ :=
  fun i => Real.arcsin (y i) / Real.pi

def sineMap {d : ℕ} (x : Fin d → ℝ) : Fin d → ℝ :=
  fun i => Real.sin (Real.pi*x i)

def sineDerivative {d : ℕ} (y : Fin d → ℝ) :
    (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) :=
  ContinuousLinearMap.pi fun i =>
    ((1 / (Real.pi * Real.sqrt (1-(y i)^2))) •
      ContinuousLinearMap.id ℝ ℝ).comp (ContinuousLinearMap.proj i)

theorem squareRadius_nonneg {d : ℕ} (y : Fin d → ℝ) : 0 ≤ squareRadius y :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem coordinate_square_le {d : ℕ} (y : Fin d → ℝ) (i : Fin d) :
    (y i)^2 ≤ squareRadius y :=
  Finset.single_le_sum (fun j _ => sq_nonneg (y j)) (Finset.mem_univ i)

theorem coordinate_mem {d : ℕ} {y : Fin d → ℝ} (hy : y ∈ unitBall d) (i : Fin d) :
    y i ∈ Ioo (-1 : ℝ) 1 := by
  have h := coordinate_square_le y i
  have hs : squareRadius y < 1 := hy
  constructor <;> nlinarith [sq_nonneg (y i + 1),sq_nonneg (y i - 1)]

theorem unitBall_measurable (d : ℕ) : MeasurableSet (unitBall d) := by
  apply (isOpen_lt (by unfold squareRadius; fun_prop) continuous_const).measurableSet

theorem one_sub_sum_le_prod {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i ∧ a i ≤ 1) :
    1 - ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1-a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.mem_insert, forall_eq_or_imp] at ha
    have hs := Finset.sum_nonneg (fun j hj => (ha.2 j hj).1)
    have hh := mul_le_mul_of_nonneg_left (ih ha.2) (sub_nonneg.mpr ha.1.2)
    simpa only [Finset.sum_insert hi, Finset.prod_insert hi] using
      (show 1 - (a i + ∑ j ∈ s, a j) ≤ (1-a i)*(∏ j ∈ s, (1-a j)) by
        nlinarith [mul_nonneg ha.1.1 hs])

theorem product_radial_bound {d : ℕ} {y : Fin d → ℝ} (hy : y ∈ unitBall d) :
    1 - squareRadius y ≤ ∏ i, (1-(y i)^2) := by
  apply one_sub_sum_le_prod
  intro i _
  exact ⟨sq_nonneg _, (coordinate_square_le y i).trans hy.le⟩

theorem sine_inverse {d : ℕ} {y : Fin d → ℝ} (hy : y ∈ unitBall d) :
    sineMap (inverseSine y) = y := by
  ext i
  simp only [sineMap,inverseSine,mul_div_cancel₀ _ Real.pi_ne_zero]
  exact Real.sin_arcsin (coordinate_mem hy i).1.le (coordinate_mem hy i).2.le

theorem inverseSine_injOn (d : ℕ) : InjOn (@inverseSine d) (unitBall d) := by
  intro x hx y hy he
  have := congrArg (@sineMap d) he
  simpa [sine_inverse hx,sine_inverse hy] using this

theorem inverseSine_hasFDerivAt {d : ℕ} {y : Fin d → ℝ} (hy : y ∈ unitBall d) :
    HasFDerivAt inverseSine (sineDerivative y) y := by
  unfold inverseSine sineDerivative
  rw [hasFDerivAt_pi]
  intro i
  have h := (Real.hasDerivAt_arcsin (ne_of_gt (coordinate_mem hy i).1)
    (ne_of_lt (coordinate_mem hy i).2)).div_const Real.pi
  have he : (1 / Real.sqrt (1-(y i)^2)) / Real.pi =
      1 / (Real.pi * Real.sqrt (1-(y i)^2)) := by ring
  rw [he] at h
  have hh : HasFDerivAt (fun a : ℝ => Real.arcsin a / Real.pi)
      ((1 / (Real.pi * Real.sqrt (1-(y i)^2))) • ContinuousLinearMap.id ℝ ℝ) (y i) := by
    apply hasFDerivAt_iff_hasDerivAt.mpr
    simpa using h
  exact HasFDerivAt.comp (f := fun x : Fin d → ℝ => x i) y hh (hasFDerivAt_apply (𝕜 := ℝ) i y)

theorem sineDerivative_det {d : ℕ} (y : Fin d → ℝ) :
    (sineDerivative y).det = ∏ i, (1 / (Real.pi * Real.sqrt (1-(y i)^2))) := by
  unfold sineDerivative
  rw [ContinuousLinearMap.det_pi]
  simp [ContinuousLinearMap.det, LinearMap.det_smul]

theorem jacobian_radial_bound {d : ℕ} {y : Fin d → ℝ} (hy : y ∈ unitBall d) :
    |(sineDerivative y).det| ≤ 1 / (Real.pi^d * Real.sqrt (1-squareRadius y)) := by
  have hn : ∀ i : Fin d, 0 ≤ 1-(y i)^2 := by
    intro i
    exact sub_nonneg.mpr ((coordinate_square_le y i).trans hy.le)
  rw [sineDerivative_det,abs_of_nonneg (Finset.prod_nonneg fun i _ => by positivity)]
  simp only [one_div,Finset.prod_inv_distrib,Finset.prod_mul_distrib,
    Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  rw [← Real.sqrt_prod Finset.univ (fun i _ => hn i)]
  have hp : 0 < 1-squareRadius y := sub_pos.mpr hy
  apply inv_anti₀ (by positivity : 0 < Real.pi^d * Real.sqrt (1-squareRadius y))
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (product_radial_bound hy)) (by positivity)

open Legacy.BecknerOnofri.TorusLogIntegrability in
theorem inverseSine_mem_cell {d : ℕ} {y : Fin d → ℝ} (hy : y ∈ unitBall d) :
    inverseSine y ∈ centeredCell d := by
  intro i _
  dsimp [inverseSine]
  constructor
  · apply (lt_div_iff₀ Real.pi_pos).mpr
    have h := Real.neg_pi_div_two_lt_arcsin.mpr (coordinate_mem hy i).1
    linarith
  · apply (div_le_iff₀ Real.pi_pos).mpr
    have h := Real.arcsin_le_pi_div_two (y i)
    linarith

open Legacy.BecknerOnofri.TorusLogIntegrability in
theorem inverse_sine {d : ℕ} {x : Fin d → ℝ} (hx : x ∈ centeredCell d) :
    inverseSine (sineMap x) = x := by
  ext i
  have hi := hx i (mem_univ i)
  dsimp [inverseSine,sineMap]
  rw [Real.arcsin_sin (by nlinarith [Real.pi_pos,hi.1]) (by nlinarith [Real.pi_pos,hi.2])]
  exact mul_div_cancel_left₀ _ Real.pi_ne_zero

open Legacy.BecknerOnofri.TorusLogIntegrability in
theorem inverseSine_image (d : ℕ) :
    inverseSine '' unitBall d = centeredCell d ∩ {x | squareRadius (sineMap x) < 1} := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact ⟨inverseSine_mem_cell hy,by simpa [sine_inverse hy] using (show squareRadius y < 1 from hy)⟩
  · rintro ⟨hx,hS⟩
    exact ⟨sineMap x,hS,inverse_sine hx⟩

open Legacy.BecknerOnofri.TorusLogIntegrability in
/-- Haar sine-square integrals are bounded by the actual radial Jacobian integral. -/
theorem haar_radial_le_ball {d : ℕ} (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ x in {x : Torus d | ArcsineProductBins.radialSum x < 1},
      F (ArcsineProductBins.radialSum x) ∂torusMeasure d) ≤
    ∫⁻ y in unitBall d,
      ENNReal.ofReal (1 / (Real.pi^d * Real.sqrt (1-squareRadius y))) * F (squareRadius y) := by
  have hm : MeasurableSet {x : Torus d | ArcsineProductBins.radialSum x < 1} :=
    (isOpen_lt (ArcsineProductBins.radialSum_continuous d) continuous_const).measurableSet
  have ht := (quotientPoint_measurePreserving d).restrict_preimage hm
  have he : quotientPoint ⁻¹' {x : Torus d | ArcsineProductBins.radialSum x < 1} =
      {x : Fin d → ℝ | squareRadius (sineMap x) < 1} := by
    ext x
    change ArcsineProductBins.radialSum (fun i => (x i : UnitAddCircle)) < 1 ↔ _
    rw [ArcsineProductBins.radialSum_coe]
    rfl
  have hcomp := ht.lintegral_comp (hF.comp (ArcsineProductBins.radialSum_continuous d).measurable)
  rw [Measure.restrict_restrict (by rw [he]; exact
    (isOpen_lt (by unfold squareRadius sineMap; fun_prop) continuous_const).measurableSet),he,
    Set.inter_comm,← inverseSine_image] at hcomp
  change (∫⁻ x in {x : Legacy.TorusEndpoint.Torus d | ArcsineProductBins.radialSum x < 1},
    (F ∘ ArcsineProductBins.radialSum) x ∂Legacy.TorusEndpoint.torusMeasure d) ≤ _
  rw [← hcomp]
  have hchange := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume
    (unitBall_measurable d) (fun y hy => (inverseSine_hasFDerivAt hy).hasFDerivWithinAt)
    (inverseSine_injOn d) (fun x => F (ArcsineProductBins.radialSum (quotientPoint x)))
  dsimp only [Function.comp_apply]
  rw [hchange]
  apply setLIntegral_mono' (unitBall_measurable d)
  intro y hy
  have hs : ArcsineProductBins.radialSum (quotientPoint (inverseSine y)) = squareRadius y := by
    change ArcsineProductBins.radialSum (fun i => ((inverseSine y) i : UnitAddCircle)) = _
    rw [ArcsineProductBins.radialSum_coe]
    change squareRadius (sineMap (inverseSine y)) = _
    rw [sine_inverse hy]
  rw [hs]
  exact mul_le_mul_right' (ENNReal.ofReal_le_ofReal (jacobian_radial_bound hy)) _

#print axioms haar_radial_le_ball

#print axioms inverseSine_hasFDerivAt
#print axioms jacobian_radial_bound

#print axioms product_radial_bound
end BecknerOnofri.HighDim.RadialMeasure
