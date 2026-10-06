module

public import BecknerOnofri.Paper2.PhysicalFractionalDefinitions
public import BecknerOnofri.Friedrichs.MixedFractionalPaper

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped ContDiff BigOperators
namespace BecknerOnofri.Paper2.Physical
open Friedrichs.MixedSpatial HighDim.SmoothEulerStatement

lemma coordinateDerivative_smul {d : ℕ} (c : ℝ) (U : (Fin d → ℝ) → ℝ) (i : Fin d)
    {z : Fin d → ℝ} (hz : z ∈ cosineCube d) :
    coordinateDerivative i (fun z => c*U z) z = c*coordinateDerivative i U z := by
  unfold coordinateDerivative
  have he := fderivWithin_const_smul_field (f := U) c (GeneralEuler.CubeAffine.uniqueDiff d z hz)
  convert! congrArg (fun L : (Fin d → ℝ) →L[ℝ] ℝ => L (Pi.single i 1)) he using 1

lemma mixedPartial_congr {d : ℕ} (is : List (Fin d)) {U V : (Fin d → ℝ) → ℝ}
    (h : EqOn U V (cosineCube d)) : EqOn (mixedPartial is U) (mixedPartial is V) (cosineCube d) := by
  induction is generalizing U V with
  | nil => exact h
  | cons i is ih =>
    apply ih
    intro z hz
    exact congrArg (fun L : (Fin d → ℝ) →L[ℝ] ℝ => L (Pi.single i 1)) (fderivWithin_congr' h hz)

lemma mixedPartial_smul {d : ℕ} (is : List (Fin d)) (c : ℝ) (U : (Fin d → ℝ) → ℝ)
    {z : Fin d → ℝ} (hz : z ∈ cosineCube d) :
    mixedPartial is (fun z => c*U z) z = c*mixedPartial is U z := by
  induction is generalizing U with
  | nil => rfl
  | cons i is ih =>
    change mixedPartial is (coordinateDerivative i (fun z => c*U z)) z = _
    rw [mixedPartial_congr is (fun y hy => coordinateDerivative_smul c U i hy) hz]
    exact ih (coordinateDerivative i U)

lemma fourierCoeff_smul {d : ℕ} (c : ℝ) (f : HighDim.Torus d → ℝ) (k : HighDim.Frequency d) :
    HighDim.fourierCoeff (fun x => c*f x) k = (c:ℂ) * HighDim.fourierCoeff f k := by
  unfold HighDim.fourierCoeff
  simp_rw [Complex.ofReal_mul, ← mul_assoc, mul_comm _ (c:ℂ), mul_assoc]
  rw [integral_const_mul]

lemma physical_multiplier (s : ℝ) {d : ℕ} (k : HighDim.Frequency d) :
    (scale^2)^s * HighDim.frequencyLength k^(2*s) =
      (scale*HighDim.frequencyLength k)^(2*s) := by
  have hc : (scale^2)^s = scale^(2*s) := by
    rw [Real.rpow_mul scale_pos.le,Real.rpow_two]
  rw [hc,Real.mul_rpow scale_pos.le (by unfold HighDim.frequencyLength; positivity)]

theorem fractional_intertwining (d : ℕ) : FractionalIntertwining d := by
  intro U hU α hα s hs
  obtain ⟨Us,hUs,hrep,hFourier,f,g,hf,hg,hG⟩ :=
    Friedrichs.MixedSpatial.fractional_intertwining d U hU α hα s hs
  let c : ℝ := (scale^2)^s
  refine ⟨fun z => c*Us z, contDiffOn_const.mul hUs, ?_, ?_,
    coordinateLpEquiv α f, c • coordinateLpEquiv α g, ?_, ?_, ?_⟩
  · intro x
    simp only [torusPower,hrep,scale,c]
  · intro k
    unfold torusPower
    rw [fourierCoeff_smul,hFourier]
    rw [← mul_assoc,← Complex.ofReal_mul, physical_multiplier]
  · exact (coordinateLpEquiv_ae α f).trans (up_ae hf)
  · filter_upwards [Lp.coeFn_smul c (coordinateLpEquiv α g),
      coordinateLpEquiv_ae α g, up_ae hg] with x hc hx hgx
    rw [hc]
    simp only [Pi.smul_apply,smul_eq_mul,hx,hgx,up]
    rw [mixedPartial_smul _ _ _ (show (fun i => Real.cos (scale*x i)) ∈ cosineCube d from
      ⟨fun i => Real.neg_one_le_cos _, fun i => Real.cos_le_one _⟩)]
    ring
  · exact (spectralPowerGraph_transport α s f g).mpr hG

#print axioms fractional_intertwining
end BecknerOnofri.Paper2.Physical
