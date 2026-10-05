module

public import BecknerOnofri.FirstShellOrbits
public import BecknerOnofri.ContinuousVariations

@[expose] public section

/-! Actual spatial translation tangents on the implicit graph, and their
independence whenever every first-shell mode is nonzero. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped Topology BigOperators ComplexConjugate
namespace BecknerOnofri.HighDim.GraphTranslationTangents
open ContinuousGibbs ContinuousFirstShell ContinuousComplement ContinuousSymmetry
open GreenLocalBranch ReducedEquation

def axisTranslation {d : ℕ} (j : Fin d) (t : ℝ) : Torus d :=
  fun i => if i=j then (t : UnitAddCircle) else 0

def angularDirection {d : ℕ} (z : Coordinates d) (j : Fin d) : Coordinates d :=
  Pi.single j ((2*Real.pi*Complex.I)*z j)

theorem phase_axisTranslation {d : ℕ} (j i : Fin d) (t : ℝ) (z : Coordinates d) :
    phaseCoordinates (-axisTranslation j t) z i =
      if i=j then fourier (1:ℤ) (t : UnitAddCircle)*z i else z i := by
  classical
  rw [phaseCoordinates_apply, UnitAddTorus.mFourier_neg, mFourier_axisFrequency]
  by_cases hij : i=j
  · simp only [axisTranslation, Pi.neg_apply, if_pos hij]
    rw [fourier_apply, zsmul_neg, fourier_neg']
    simp
  · simp [axisTranslation, hij]

@[simp] theorem phase_axisTranslation_zero {d : ℕ} (j : Fin d) (z : Coordinates d) :
    phaseCoordinates (-axisTranslation j 0) z = z := by
  ext i
  rw [phase_axisTranslation]
  split_ifs <;> simp

theorem hasDerivAt_phase_axisTranslation {d : ℕ} (j : Fin d) (z : Coordinates d) :
    HasDerivAt (fun t : ℝ => phaseCoordinates (-axisTranslation j t) z) (angularDirection z j) 0 := by
  classical
  apply hasDerivAt_pi.mpr
  intro i
  by_cases hij : i=j
  · subst i
    have hh := (hasDerivAt_fourier (1:ℝ) (1:ℤ) (0:ℝ)).mul_const (z j)
    simpa only [phase_axisTranslation, if_pos rfl, ite_true, angularDirection, Pi.single_eq_same,
      AddCircle.coe_zero, fourier_eval_zero, Complex.ofReal_one, Int.cast_one, mul_one, div_one] using hh
  · simpa only [phase_axisTranslation, if_neg hij, angularDirection, Pi.single_eq_of_ne hij] using
      (hasDerivAt_const (x := (0:ℝ)) (c := z i))

/-- The actual C(Tᵈ) derivative of the graph potential in a phase direction. -/
def tangent {d : ℕ} (hd : 12 ≤ d) (x : ℝ × Coordinates d) (j : Fin d) : Space d :=
  fderiv ℝ (potential hd) x (0,angularDirection x.2 j)

theorem coordinates_tangent {d : ℕ} (hd : 12 ≤ d) {x : ℝ × Coordinates d}
    (hx : DifferentiableAt ℝ (potential hd) x) (j : Fin d) :
    coordinates d (tangent hd x j) = angularDirection x.2 j := by
  have hc := (coordinates d).hasFDerivAt.comp x hx.hasFDerivAt
  have hs : HasFDerivAt (fun y => coordinates d (potential hd y))
      (ContinuousLinearMap.snd ℝ ℝ (Coordinates d)) x := by
    convert! (ContinuousLinearMap.snd ℝ ℝ (Coordinates d)).hasFDerivAt (x := x) using 1
    funext y
    exact coordinates_reconstruction _
  have he := hc.unique hs
  exact congrArg (fun L : ℝ × Coordinates d →L[ℝ] Coordinates d => L (0,angularDirection x.2 j)) he

theorem tangent_eq_coordinateDerivative {d : ℕ} (hd : 12 ≤ d) :
    ∀ᶠ x in 𝓝 (1,(0 : Coordinates d)), ∀ j : Fin d, ∀ y : Torus d,
      tangent hd x j y = coordinateDerivative (potential hd x) j y := by
  filter_upwards [(potential_analytic hd).eventually_analyticAt, potential_translation hd]
    with x ha ht j y
  have hp : HasDerivAt (fun t : ℝ => (x.1,phaseCoordinates (-axisTranslation j t) x.2))
      (0,angularDirection x.2 j) 0 :=
    (hasDerivAt_const (x := (0:ℝ)) (c := x.1)).prodMk (hasDerivAt_phase_axisTranslation j x.2)
  have hbase : (x.1,phaseCoordinates (-axisTranslation j 0) x.2) = x := by simp
  have hu := ha.differentiableAt.hasFDerivAt.comp_hasDerivAt_of_eq (0:ℝ) hp hbase.symm
  have he := (ContinuousMap.evalCLM ℝ y).hasFDerivAt.comp_hasDerivAt (0:ℝ) hu
  have hdv : HasDerivAt
      (fun t : ℝ => potential hd x (y + axisTranslation j t)) (tangent hd x j y) 0 := by
    apply he.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall (fun t => by
      have hh := congrArg (fun u : Space d => u y) (ht (-axisTranslation j t))
      simpa only [Function.comp_apply, ContinuousMap.evalCLM_apply, translation_apply,
        sub_neg_eq_add] using hh.symm)
  exact hdv.deriv.symm

/-- Actual almost-everywhere translation tangent independence. -/
theorem tangentIndependent {d : ℕ} (hd : 12 ≤ d) :
    ∀ᶠ x in 𝓝 (1,(0 : Coordinates d)), (∀ j : Fin d, x.2 j ≠ 0) →
      ∀ a : Fin d → ℝ, tangentCombination (potential hd x) a =ᵐ[torusMeasure d] (fun _ => 0) → a = 0 := by
  haveI : (torusMeasure d).IsOpenPosMeasure := by unfold torusMeasure; infer_instance
  filter_upwards [(potential_analytic hd).eventually_analyticAt, tangent_eq_coordinateDerivative hd]
    with x ha ht hfull a hzero
  let v : Space d := ∑ j : Fin d, a j • tangent hd x j
  have hae : (fun y => v y) =ᵐ[torusMeasure d] (fun _ => 0) := by
    filter_upwards [hzero] with y hy
    simpa only [v, ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul,
      ht, tangentCombination] using hy
  have hv : v = 0 := ContinuousMap.ext (congrFun
    (Measure.eq_of_ae_eq hae v.continuous continuous_const))
  funext i
  have hc := congrArg (fun u : Space d => coordinates d u i) hv
  have hcoords (j : Fin d) : coordinates d (tangent hd x j) = angularDirection x.2 j :=
    coordinates_tangent hd ha.differentiableAt j
  simp only [v, map_sum, map_smul, hcoords, Finset.sum_apply, Pi.smul_apply,
    angularDirection, map_zero, Pi.zero_apply] at hc
  have hs : (∑ j : Fin d, a j • (Pi.single j ((2*Real.pi*Complex.I)*x.2 j) : Coordinates d) i) =
      a i • ((2*Real.pi*Complex.I)*x.2 i) := by
    classical
    rw [Finset.sum_eq_single i]
    · rw [Pi.single_eq_same]
    · intro j _ hji
      rw [Pi.single_eq_of_ne (Ne.symm hji), smul_zero]
    · simp
  rw [hs, Complex.real_smul] at hc
  have hfreq : ((2*Real.pi*Complex.I)*x.2 i : ℂ) ≠ 0 := by
    apply mul_ne_zero _ (hfull i)
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  exact Complex.ofReal_eq_zero.mp ((mul_eq_zero.mp hc).resolve_right hfreq)

#print axioms tangent_eq_coordinateDerivative
#print axioms tangentIndependent
end BecknerOnofri.HighDim.GraphTranslationTangents
