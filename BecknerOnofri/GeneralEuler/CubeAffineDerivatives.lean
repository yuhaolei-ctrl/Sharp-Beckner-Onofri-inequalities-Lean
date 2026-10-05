module

public import BecknerOnofri.SmoothEulerStatementDefinitions
public import Legacy.BecknerOnofri.CubeProfileMonotone
public import Legacy.BecknerOnofri.NormalizedExponentialPartials
public import Mathlib.Analysis.Calculus.FDeriv.Equiv

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
open scoped ContDiff Pointwise
namespace BecknerOnofri.GeneralEuler.CubeAffine
open HighDim.SmoothEulerStatement
open Legacy.BecknerOnofri

lemma uniqueDiff (d : ℕ) : UniqueDiffOn ℝ (cosineCube d) := by
  have hh := UniqueDiffOn.univ_pi (fun _ : Fin d =>
    uniqueDiffOn_Icc (by norm_num : (-1:ℝ)<1))
  have he : cosineCube d=Set.pi Set.univ (fun _ : Fin d => Icc (-1:ℝ) 1) := by
    ext x
    simp only [cosineCube,Set.mem_Icc,Set.mem_pi,Set.mem_univ,forall_const]
    exact ⟨fun h i => ⟨h.1 i,h.2 i⟩,fun h => ⟨fun i => (h i).1,fun i => (h i).2⟩⟩
  rw [he]
  exact hh

lemma affine_image (d : ℕ) : (-1 : Fin d → ℝ) +ᵥ ((2:ℝ) • FiniteDifferences.closedCube d) =
    cosineCube d := by
  ext z
  constructor
  · rintro ⟨w,⟨y,hy,rfl⟩,rfl⟩
    constructor <;> intro i
    · change -1≤-1+2*y i
      have h0 : 0≤y i := hy.1 i
      linarith
    · change -1+2*y i≤1
      have h1 : y i≤1 := hy.2 i
      linarith
  · intro hz
    refine ⟨(2:ℝ) • (fun i => (z i+1)/2),⟨(fun i => (z i+1)/2),?_,rfl⟩,?_⟩
    · constructor <;> intro i
      · change 0≤(z i+1)/2
        have h0 : -1≤z i := hz.1 i
        linarith
      · change (z i+1)/2≤1
        have h1 : z i≤1 := hz.2 i
        linarith
    · ext i
      change -1+2*((z i+1)/2)=z i
      ring

lemma coordinate_affine {d : ℕ} (U : (Fin d → ℝ) → ℝ) (i : Fin d)
    {y : Fin d → ℝ} (hy : y∈FiniteDifferences.closedCube d) :
    FiniteDifferences.coordinateDerivative i (fun y => U (CubeProfileMonotone.fromUnitCube y)) y =
      2*coordinateDerivative i U (CubeProfileMonotone.fromUnitCube y) := by
  have hf : (fun y => U (CubeProfileMonotone.fromUnitCube y)) =
      (fun y : Fin d → ℝ => (fun z => U ((-1 : Fin d → ℝ)+z)) ((2:ℝ) • y)) := by
    funext y
    congr 1
    ext j
    dsimp [CubeProfileMonotone.fromUnitCube]
    ring
  rw [FiniteDifferences.coordinateDerivative,hf,
    fderivWithin_comp_smul (𝕜:=ℝ) (f:=fun z : Fin d → ℝ => U (-1+z)) (2:ℝ)
      (FiniteDifferences.uniqueDiffOn_closedCube d y hy),
    fderivWithin_comp_add_left,affine_image]
  change 2*(fderivWithin ℝ U (cosineCube d) (-1+(2:ℝ) • y) (Pi.single i 1)) = _
  have hp : (-1+(2:ℝ) • y)=CubeProfileMonotone.fromUnitCube y := by
    ext j
    change -1+2*y j=2*y j-1
    ring
  rw [hp]
  rfl

lemma contDiff_coordinate {d : ℕ} {U : (Fin d → ℝ) → ℝ}
    (hU : ContDiffOn ℝ ∞ U (cosineCube d)) (i : Fin d) :
    ContDiffOn ℝ ∞ (coordinateDerivative i U) (cosineCube d) :=
  (hU.fderivWithin (uniqueDiff d) (m:=∞) (by simp)).clm_apply contDiffOn_const

lemma mixed_affine {d : ℕ} {U : (Fin d → ℝ) → ℝ}
    (hU : ContDiffOn ℝ ∞ U (cosineCube d)) (is : List (Fin d))
    {y : Fin d → ℝ} (hy : y∈FiniteDifferences.closedCube d) :
    FiniteDifferences.mixedPartial is (fun y => U (CubeProfileMonotone.fromUnitCube y)) y =
      2^is.length*mixedPartial is U (CubeProfileMonotone.fromUnitCube y) := by
  induction is generalizing U with
  | nil => simp [mixedPartial]
  | cons i is ih =>
    rw [FiniteDifferences.mixedPartial_cons]
    have he : EqOn (FiniteDifferences.coordinateDerivative i (fun y => U (CubeProfileMonotone.fromUnitCube y)))
        (fun y => 2*(coordinateDerivative i U (CubeProfileMonotone.fromUnitCube y)))
        (FiniteDifferences.closedCube d) := fun _ hz => coordinate_affine U i hz
    rw [NormalizedExponentialPartials.mixedPartial_congr is he hy,
      NormalizedExponentialPartials.mixedPartial_const_mul is 2
        (CubeProfileMonotone.unit_profile_contDiffOn (contDiff_coordinate hU i)) hy,
      ih (contDiff_coordinate hU i)]
    simp only [mixedPartial,List.length_cons,pow_succ]
    ring

#print axioms mixed_affine
end BecknerOnofri.GeneralEuler.CubeAffine
