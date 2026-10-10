module

public import Legacy.BecknerOnofri.FiniteDifferenceSmooth
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Convex.Topology

@[expose] public section

/-! # S014: iterated coordinate derivatives on the closed cube do not depend on the order

The repository's `mixedPartial is f` is the iterated `fderivWithin` along the list `is` of
coordinate directions in the closed cube.  The manuscript's `∂^α f` for a multi-index `α` is
order independent; here we prove that on the closed cube (including its boundary) the order of the
directions does not matter, from the symmetry of the second derivative within a set
(`ContDiffWithinAt.isSymmSndFDerivWithinAt`) at points of the closure of the interior.

We also prove that `mixedPartial` is linear in the function on the cube.
-/

noncomputable section
open Set Finset
open scoped ContDiff
namespace BecknerOnofri.V2.Reaudit.HeatKernel
open Legacy.BecknerOnofri.FiniteDifferences

variable {d : ℕ}

theorem closedCube_subset_closure_interior (d : ℕ) :
    closedCube d ⊆ closure (interior (closedCube d)) := by
  have hconv : Convex ℝ (closedCube d) := convex_Icc _ _
  have hne : (interior (closedCube d)).Nonempty := by
    refine ⟨fun _ => (1 : ℝ) / 2, ?_⟩
    have he : closedCube d = Set.pi Set.univ (fun _ : Fin d => Icc (0 : ℝ) 1) := by
      ext x
      simp only [closedCube, Set.mem_Icc, Set.mem_pi, Set.mem_univ, forall_const]
      exact ⟨fun h i => ⟨h.1 i, h.2 i⟩, fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩⟩
    rw [he, interior_pi_set Set.finite_univ]
    intro i _
    rw [interior_Icc]
    exact ⟨by norm_num, by norm_num⟩
  rw [hconv.closure_interior_eq_closure_of_nonempty_interior hne]
  exact subset_closure

/-- Symmetry of mixed second derivatives at every point of the closed cube. -/
theorem coordinateDerivative_comm {f : Space d → ℝ} (hf : ContDiffOn ℝ ∞ f (closedCube d))
    (i j : Fin d) {x : Space d} (hx : x ∈ closedCube d) :
    coordinateDerivative j (coordinateDerivative i f) x =
      coordinateDerivative i (coordinateDerivative j f) x := by
  have hU := uniqueDiffOn_closedCube d
  have hsymm : IsSymmSndFDerivWithinAt ℝ f (closedCube d) x :=
    (hf.contDiffWithinAt hx).isSymmSndFDerivWithinAt (by simp) hU
      (closedCube_subset_closure_interior d hx) hx
  have hF : DifferentiableWithinAt ℝ (fderivWithin ℝ f (closedCube d)) (closedCube d) x := by
    have := hf.fderivWithin hU (m := ∞) (by simp)
    exact (this.differentiableOn (by simp) x hx)
  have key : ∀ a b : Fin d, coordinateDerivative b (coordinateDerivative a f) x =
      fderivWithin ℝ (fderivWithin ℝ f (closedCube d)) (closedCube d) x (basis b) (basis a) := by
    intro a b
    unfold coordinateDerivative
    have h1 := (ContinuousLinearMap.apply ℝ ℝ (basis a)).hasFDerivAt.comp_hasFDerivWithinAt x
      hF.hasFDerivWithinAt
    have h2 := h1.fderivWithin (hU x hx)
    simp only [Function.comp_def] at h2 ⊢
    rw [show (fun y => (fderivWithin ℝ f (closedCube d) y) (basis a)) =
      (fun y => (ContinuousLinearMap.apply ℝ ℝ (basis a)) (fderivWithin ℝ f (closedCube d) y)) from rfl,
      h2]
    rfl
  rw [key, key]
  exact hsymm (basis j) (basis i)

theorem mixedPartial_append (a b : List (Fin d)) (f : Space d → ℝ) :
    mixedPartial (a ++ b) f = mixedPartial b (mixedPartial a f) := by
  induction a generalizing f with
  | nil => rfl
  | cons i a ih => exact ih (coordinateDerivative i f)

/-- A coordinate derivative at points of the cube only depends on the function on the cube. -/
theorem coordinateDerivative_congr {f g : Space d → ℝ} (h : ∀ x ∈ closedCube d, f x = g x)
    (i : Fin d) {x : Space d} (hx : x ∈ closedCube d) :
    coordinateDerivative i f x = coordinateDerivative i g x := by
  unfold coordinateDerivative
  rw [fderivWithin_congr (fun y hy => h y hy) (h x hx)]

theorem mixedPartial_congr (L : List (Fin d)) {f g : Space d → ℝ}
    (h : ∀ x ∈ closedCube d, f x = g x) {x : Space d} (hx : x ∈ closedCube d) :
    mixedPartial L f x = mixedPartial L g x := by
  induction L generalizing f g with
  | nil => exact h x hx
  | cons i L ih =>
    simp only [mixedPartial_cons]
    exact ih (fun y hy => coordinateDerivative_congr h i hy)

/-- Iterated coordinate derivatives on the closed cube are invariant under permutation of the
list of directions. -/
theorem mixedPartial_perm {L L' : List (Fin d)} (hp : L.Perm L') {f : Space d → ℝ}
    (hf : ContDiffOn ℝ ∞ f (closedCube d)) {x : Space d} (hx : x ∈ closedCube d) :
    mixedPartial L f x = mixedPartial L' f x := by
  induction hp generalizing f with
  | nil => rfl
  | cons a _ ih =>
    simp only [mixedPartial_cons]
    exact ih (contDiffOn_coordinateDerivative hf a)
  | swap a b l =>
    simp only [mixedPartial_cons]
    apply mixedPartial_congr l _ hx
    intro y hy
    exact (coordinateDerivative_comm hf a b hy).symm
  | trans _ _ ih1 ih2 => exact (ih1 hf).trans (ih2 hf)

theorem directionIndex_toMultiset (L : List (Fin d)) :
    (directionIndex L).toMultiset = (L : Multiset (Fin d)) := by
  ext i
  rw [Finsupp.count_toMultiset, directionIndex_apply, Multiset.coe_count]

/-- On the cube, `mixedPartial` depends on the list only through its multi-index. -/
theorem mixedPartial_eq_directions (L : List (Fin d)) {f : Space d → ℝ}
    (hf : ContDiffOn ℝ ∞ f (closedCube d)) {x : Space d} (hx : x ∈ closedCube d) :
    mixedPartial L f x = mixedPartial (directions (directionIndex L)) f x := by
  apply mixedPartial_perm _ hf hx
  unfold directions
  rw [← Multiset.coe_eq_coe, Multiset.coe_toList, directionIndex_toMultiset]

theorem mixedPartial_eq_of_directionIndex_eq {L L' : List (Fin d)}
    (h : directionIndex L = directionIndex L') {f : Space d → ℝ}
    (hf : ContDiffOn ℝ ∞ f (closedCube d)) {x : Space d} (hx : x ∈ closedCube d) :
    mixedPartial L f x = mixedPartial L' f x := by
  rw [mixedPartial_eq_directions L hf hx, mixedPartial_eq_directions L' hf hx, h]

/-- Coordinate derivative of a finite linear combination, at points of the cube. -/
theorem coordinateDerivative_sum {ι : Type*} (F : Finset ι) (c : ι → ℝ) (h : ι → Space d → ℝ)
    (hh : ∀ k, ContDiffOn ℝ ∞ (h k) (closedCube d)) (i : Fin d) {x : Space d}
    (hx : x ∈ closedCube d) :
    coordinateDerivative i (fun z => ∑ k ∈ F, c k * h k z) x =
      ∑ k ∈ F, c k * coordinateDerivative i (h k) x := by
  have hU := uniqueDiffOn_closedCube d
  have hd : ∀ k, HasFDerivWithinAt (h k) (fderivWithin ℝ (h k) (closedCube d) x)
      (closedCube d) x := fun k =>
    ((hh k).differentiableOn (by simp) x hx).hasFDerivWithinAt
  have hs : HasFDerivWithinAt (fun z => ∑ k ∈ F, c k * h k z)
      (∑ k ∈ F, c k • fderivWithin ℝ (h k) (closedCube d) x) (closedCube d) x :=
    HasFDerivWithinAt.fun_sum (fun k _ => (hd k).const_smul (c k))
  unfold coordinateDerivative
  rw [hs.fderivWithin (hU x hx)]
  simp

/-- `mixedPartial` is linear in the function, at points of the cube. -/
theorem mixedPartial_sum {ι : Type*} (L : List (Fin d)) (F : Finset ι) (c : ι → ℝ)
    (h : ι → Space d → ℝ) (hh : ∀ k, ContDiffOn ℝ ∞ (h k) (closedCube d)) {x : Space d}
    (hx : x ∈ closedCube d) :
    mixedPartial L (fun z => ∑ k ∈ F, c k * h k z) x = ∑ k ∈ F, c k * mixedPartial L (h k) x := by
  induction L generalizing h x with
  | nil => rfl
  | cons i L ih =>
    simp only [mixedPartial_cons]
    have h1 : mixedPartial L (coordinateDerivative i (fun z => ∑ k ∈ F, c k * h k z)) x =
        mixedPartial L (fun z => ∑ k ∈ F, c k * coordinateDerivative i (h k) z) x :=
      mixedPartial_congr L (fun y hy => coordinateDerivative_sum F c h hh i hy) hx
    rw [h1]
    exact ih (fun k => coordinateDerivative i (h k))
      (fun k => contDiffOn_coordinateDerivative (hh k) i) hx


end BecknerOnofri.V2.Reaudit.HeatKernel
