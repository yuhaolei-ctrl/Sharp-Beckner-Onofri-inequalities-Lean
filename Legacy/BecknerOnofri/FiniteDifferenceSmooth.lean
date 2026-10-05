import Legacy.BecknerOnofri.FiniteDifferenceCalculus
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.TangentCone.Pi
import Mathlib.Analysis.Calculus.TangentCone.Real

/-! The coordinate derivative family is built from Mathlib's actual Fréchet derivative. -/
noncomputable section
open Finset Set Filter
open scoped BigOperators Topology ContDiff
namespace Legacy.BecknerOnofri.FiniteDifferences

theorem uniqueDiffOn_closedCube (d : ℕ) : UniqueDiffOn ℝ (closedCube d) := by
  have hh := UniqueDiffOn.univ_pi (fun _ : Fin d => uniqueDiffOn_Icc_zero_one)
  have he : closedCube d = Set.pi Set.univ (fun _ : Fin d => Icc (0 : ℝ) 1) := by
    ext x
    simp only [closedCube, Set.mem_Icc, Set.mem_pi, Set.mem_univ, forall_const]
    exact ⟨fun h i => ⟨h.1 i, h.2 i⟩, fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩⟩
  rw [he]
  exact hh

def coordinateDerivative {d : ℕ} (i : Fin d) (f : Space d → ℝ) (x : Space d) : ℝ :=
  fderivWithin ℝ f (closedCube d) x (basis i)

def mixedPartial {d : ℕ} : List (Fin d) → (Space d → ℝ) → Space d → ℝ
  | [], f => f
  | i :: is, f => mixedPartial is (coordinateDerivative i f)

@[simp] theorem mixedPartial_nil {d : ℕ} (f : Space d → ℝ) :
    mixedPartial [] f = f := rfl
@[simp] theorem mixedPartial_cons {d : ℕ} (i : Fin d) (is : List (Fin d)) (f : Space d → ℝ) :
    mixedPartial (i :: is) f = mixedPartial is (coordinateDerivative i f) := rfl

theorem mixedPartial_append_single {d : ℕ} (is : List (Fin d)) (i : Fin d)
    (f : Space d → ℝ) : mixedPartial (is ++ [i]) f = coordinateDerivative i (mixedPartial is f) := by
  induction is generalizing f with
  | nil => rfl
  | cons j js ih => exact ih (coordinateDerivative j f)

theorem contDiffOn_coordinateDerivative {d : ℕ} {f : Space d → ℝ}
    (hf : ContDiffOn ℝ ∞ f (closedCube d)) (i : Fin d) :
    ContDiffOn ℝ ∞ (coordinateDerivative i f) (closedCube d) := by
  have hd := hf.fderivWithin (uniqueDiffOn_closedCube d) (m := ∞) (by simp)
  exact hd.clm_apply contDiffOn_const

theorem contDiffOn_mixedPartial {d : ℕ} {f : Space d → ℝ}
    (hf : ContDiffOn ℝ ∞ f (closedCube d)) (is : List (Fin d)) :
    ContDiffOn ℝ ∞ (mixedPartial is f) (closedCube d) := by
  induction is generalizing f with
  | nil => exact hf
  | cons i is ih => exact ih (contDiffOn_coordinateDerivative hf i)

theorem hasDerivWithinAt_coordinate_of_contDiffOn {d : ℕ} {f : Space d → ℝ}
    (hf : ContDiffOn ℝ ∞ f (closedCube d)) (i : Fin d) {x : Space d}
    (hx : x ∈ closedCube d) :
    HasDerivWithinAt (fun t => f (Function.update x i t))
      (coordinateDerivative i f x) (Icc (0 : ℝ) 1) (x i) := by
  have hd := (hf.differentiableOn (by simp) x hx).hasFDerivWithinAt
  have hm : MapsTo (Function.update x i) (Icc (0 : ℝ) 1) (closedCube d) := by
    intro t ht
    constructor <;> intro k <;> by_cases hk : k = i
    · subst k; simpa using ht.1
    · simpa [Function.update_of_ne hk] using hx.1 k
    · subst k; simpa using ht.2
    · simpa [Function.update_of_ne hk] using hx.2 k
  have hc := hd.comp_hasDerivWithinAt_of_eq (x i)
    (hasDerivAt_update x i (x i)).hasDerivWithinAt hm (Function.update_eq_self i x).symm
  exact hc

/-- This is a proved instance of the derivative conditions, not a jet assumption. -/
theorem coordinateJet_of_contDiffOn {d : ℕ} {f : Space d → ℝ}
    (hf : ContDiffOn ℝ ∞ f (closedCube d)) : IsCoordinateJet (fun is => mixedPartial is f) := by
  constructor
  · intro is; exact (contDiffOn_mixedPartial hf is).continuousOn
  · intro is i x hx
    rw [mixedPartial_append_single]
    exact hasDerivWithinAt_coordinate_of_contDiffOn (contDiffOn_mixedPartial hf is) i hx

#print axioms coordinateJet_of_contDiffOn

end Legacy.BecknerOnofri.FiniteDifferences
