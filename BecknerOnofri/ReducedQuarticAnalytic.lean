module

public import BecknerOnofri.ReducedQuarticExpansion
public import BecknerOnofri.ReducedSymmetry
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

@[expose] public section

/-! Analyticity of the genuine reduced graph expression and its quartic term. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology
namespace BecknerOnofri.HighDim.ReducedQuarticExpansion
open ContinuousGibbs ContinuousFirstShell ContinuousComplement GreenLocalBranch ReducedEquation
open QuadraticModes QuadraticSlaving SlavedMoments ContinuousSymmetry

theorem mean_analytic_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {d : ℕ} {f : E → Space d} {x : E} (hf : AnalyticAt ℝ f x) :
    AnalyticAt ℝ (fun y => mean d (f y)) x :=
  ((mean d).analyticAt (f x)).comp (f := f) hf

theorem U_analytic {d : ℕ} (hd : 12 ≤ d) : AnalyticAt ℝ (U hd) 0 := by
  exact (potential_analytic hd).comp (analyticAt_const.prod analyticAt_id)

theorem W_analytic {d : ℕ} (hd : 12 ≤ d) : AnalyticAt ℝ (W hd) 0 := by
  have hh : AnalyticAt ℝ (fun z : Coordinates d => correction hd (1,z)) 0 :=
    (correction_analytic hd).comp (analyticAt_const.prod analyticAt_id)
  exact ((complement d).subtypeL.analyticAt _).comp hh

theorem centeredLogPartition_analytic {d : ℕ} (u : Space d) :
    AnalyticAt ℝ centeredLogPartition u := by
  have hc : AnalyticAt ℝ (fun v : Space d => partition (center d v)) u :=
    (partition_analytic (center d u)).comp (f := fun v : Space d => center d v) ((center d).analyticAt u)
  change AnalyticAt ℝ (fun v : Space d => Real.log (partition (center d v))) u
  exact (analyticAt_log (partition_pos (center d u))).comp
    (f := fun v : Space d => partition (center d v)) hc

theorem graphExpression_analytic {d : ℕ} (hd : 12 ≤ d) :
    AnalyticAt ℝ (graphExpression hd) 0 := by
  have hlog := (centeredLogPartition_analytic (U hd 0)).comp (U_analytic hd)
  have hv := mean_analytic_comp (((assembly d).analyticAt (0 : Coordinates d)).pow 2)
  have hn := (normalized_analytic (U hd 0)).comp (U_analytic hd)
  have hw := mean_analytic_comp ((W_analytic hd).mul hn)
  exact (hlog.sub (hv.div_const (c := 2))).sub (hw.div_const (c := 2))

theorem quadraticCorrection_analytic {d : ℕ} (hd : 12 ≤ d) :
    AnalyticAt ℝ (fun z => (quadraticCorrection hd z : Space d)) (0 : Coordinates d) := by
  have hq : AnalyticAt ℝ (fun z : Coordinates d => quadraticTerm (assembly d z)) 0 := by
    have h := (((center d).analyticAt ((assembly d (0 : Coordinates d))^2)).comp
      (f := fun z : Coordinates d => assembly d z^2)
      (((assembly d).analyticAt (0 : Coordinates d)).pow 2)).const_smul (c := (1/2:ℝ))
    convert! h using 1
    funext z
    exact quadraticTerm_of_mean_zero (mean_assembly z)
  have hr := ((inverseGreen hd).analyticAt (quadraticTerm (assembly d (0 : Coordinates d)))).comp
    (f := fun z : Coordinates d => quadraticTerm (assembly d z)) hq
  exact ((complement d).subtypeL.analyticAt _).comp hr

theorem quarticValue_analytic {d : ℕ} (hd : 12 ≤ d) :
    AnalyticAt ℝ (@quarticValue d) (0 : Coordinates d) := by
  have hv := (assembly d).analyticAt (0 : Coordinates d)
  have h4 := mean_analytic_comp (hv.pow 4)
  have h2 := mean_analytic_comp (hv.pow 2)
  have hs := mean_analytic_comp ((hv.pow 2).mul (quadraticCorrection_analytic hd))
  have hh := ((h4.div_const (c := 24)).sub ((h2.pow 2).div_const (c := 8))).add (hs.div_const (c := 4))
  convert! hh using 1
  funext z
  have hq := actual_quartic_coefficients hd z
  rw [← pairing_quadraticCorrection hd z] at hq
  exact hq.symm

theorem translation_mul {d : ℕ} (a : Torus d) (f g : Space d) :
    translation a (f*g) = translation a f * translation a g := rfl

theorem translation_pow {d : ℕ} (a : Torus d) (f : Space d) (n : ℕ) :
    translation a (f^n) = (translation a f)^n := rfl

theorem centeredLogPartition_translation {d : ℕ} (a : Torus d) (u : Space d) :
    centeredLogPartition (translation a u) = centeredLogPartition u := by
  simp only [centeredLogPartition, center_translation, partition_translation]

theorem graphExpression_translation {d : ℕ} (hd : 12 ≤ d) :
    ∀ᶠ z in 𝓝 (0 : Coordinates d), ∀ a : Torus d,
      graphExpression hd (phaseCoordinates a z) = graphExpression hd z := by
  have ht : Tendsto (fun z : Coordinates d => ((1:ℝ),z)) (𝓝 0) (𝓝 (1,0)) :=
    (continuous_const.prodMk continuous_id).continuousAt
  filter_upwards [ht.eventually (correction_translation hd),
    ht.eventually (potential_translation hd)] with z hw hu
  intro a
  have huw : U hd (phaseCoordinates a z) = translation a (U hd z) := hu a
  have hww : W hd (phaseCoordinates a z) = translation a (W hd z) :=
    congrArg (fun w : complement d => (w : Space d)) (hw a)
  have hv : V d (phaseCoordinates a z) = translation a (V d z) := (translation_assembly a z).symm
  unfold graphExpression
  rw [huw, hww, hv, centeredLogPartition_translation, normalized_translation,
    ← translation_pow, mean_translation, ← translation_mul, mean_translation]

#print axioms graphExpression_analytic
#print axioms quarticValue_analytic
#print axioms graphExpression_translation
end BecknerOnofri.HighDim.ReducedQuarticExpansion
