module

public import BecknerOnofri.BranchDefinitions
public import BecknerOnofri.PolarizationMetricGeometry
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

@[expose] public section

/-! Smooth periodic lifts yield Lipschitz functions in the actual torus
metric. Nearest representatives avoid discontinuities of a fixed chart. -/
noncomputable section
open Set
open scoped NNReal
namespace BecknerOnofri.HighDim

def nearestLift {d : ℕ} (x : Torus d) : Fin d → ℝ :=
  fun i => AddCircle.equivIoc 1 (-(1/2 : ℝ)) (x i)

lemma nearestLift_bounds {d : ℕ} (x : Torus d) (i : Fin d) :
    -(1/2 : ℝ) < nearestLift x i ∧ nearestLift x i ≤ 1/2 := by
  have h := (AddCircle.equivIoc 1 (-(1/2 : ℝ)) (x i)).property
  exact ⟨h.1,by dsimp [nearestLift]; linarith [h.2]⟩

lemma nearestLift_coe {d : ℕ} (x : Torus d) :
    (fun i => (nearestLift x i : UnitAddCircle))=x := by
  funext i
  exact AddCircle.coe_equivIoc

lemma nearestLift_norm_coord {d : ℕ} (x : Torus d) (i : Fin d) :
    ‖nearestLift x i‖=‖x i‖ := by
  have h := nearestLift_bounds x i
  have hc := congrFun (nearestLift_coe x) i
  rw [Real.norm_eq_abs,← hc]
  exact (PolarizationL1.circle_norm_small (abs_le.mpr ⟨h.1.le,h.2⟩)).symm

lemma nearestLift_norm {d : ℕ} (x : Torus d) : ‖nearestLift x‖=‖x‖ := by
  simp only [Pi.norm_def]
  congr 1
  apply Finset.sup_congr rfl
  intro i _
  exact Subtype.ext (nearestLift_norm_coord x i)

lemma nearestLift_norm_le {d : ℕ} (x : Torus d) : ‖nearestLift x‖≤1/2 := by
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤1/2)).mpr
  intro i
  rw [Real.norm_eq_abs]
  exact abs_le.mpr ⟨(nearestLift_bounds x i).1.le,(nearestLift_bounds x i).2⟩

/-- No Lipschitz premise is added to smooth torus data. -/
theorem SmoothOnTorus.exists_lipschitz {d : ℕ} {f : Torus d → ℝ} (hf : SmoothOnTorus f) :
    ∃ K : ℝ≥0, LipschitzWith K f := by
  let F : (Fin d → ℝ) → ℝ := fun x => f (fun i => (x i : UnitAddCircle))
  have hF : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) F := hf
  obtain ⟨K,hK⟩ := hF.contDiffOn.exists_lipschitzOnWith (by simp)
    (convex_closedBall (0 : Fin d → ℝ) 1) (isCompact_closedBall 0 1)
  refine ⟨K,LipschitzWith.of_dist_le_mul (fun x y => ?_)⟩
  let X := nearestLift x
  let Z := nearestLift (y-x)
  have hX : X∈Metric.closedBall (0 : Fin d → ℝ) 1 := by
    rw [Metric.mem_closedBall,dist_zero_right]
    exact (nearestLift_norm_le x).trans (by norm_num)
  have hY : X+Z∈Metric.closedBall (0 : Fin d → ℝ) 1 := by
    rw [Metric.mem_closedBall,dist_zero_right]
    calc
      ‖X+Z‖ ≤ ‖X‖+‖Z‖ := norm_add_le _ _
      _ ≤ 1 := by linarith [nearestLift_norm_le x,nearestLift_norm_le (y-x)]
  have hFX : F X=f x := congrArg f (nearestLift_coe x)
  have hFY : F (X+Z)=f y := by
    apply congrArg f
    funext i
    change ((X i+Z i : ℝ) : UnitAddCircle)=y i
    rw [AddCircle.coe_add,show (X i : UnitAddCircle)=x i from congrFun (nearestLift_coe x) i,
      show (Z i : UnitAddCircle)=(y-x) i from congrFun (nearestLift_coe (y-x)) i]
    simp
  have hdist : dist X (X+Z)=dist x y := by
    rw [dist_eq_norm,show X-(X+Z) = -Z by abel,norm_neg]
    change ‖nearestLift (y-x)‖=dist x y
    rw [nearestLift_norm,← dist_eq_norm,dist_comm]
  simpa only [hFX,hFY,hdist] using hK.dist_le_mul X hX (X+Z) hY

#print axioms SmoothOnTorus.exists_lipschitz
end BecknerOnofri.HighDim
