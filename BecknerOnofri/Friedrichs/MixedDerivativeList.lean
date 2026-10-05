import BecknerOnofri.Friedrichs.MixedFractionalStatementDefinitions
import Legacy.BecknerOnofri.AngularMixedTerms
import Mathlib.Algebra.BigOperators.Fin

noncomputable section
open scoped BigOperators
namespace BecknerOnofri.Friedrichs.MixedSpatial

lemma derivativeList_count {d : ℕ} (α : MultiIndex d) (i : Fin d) :
    (derivativeList α).count i=α i := by
  simp [derivativeList,List.count_flatten,List.sum_ofFn,List.count_replicate]

lemma countIndex_derivativeList {d : ℕ} (α : MultiIndex d) :
    Legacy.BecknerOnofri.AngularMixedTerms.countIndex (derivativeList α)=α :=
  funext (derivativeList_count α)

lemma derivativeList_ne_nil {d : ℕ} {α : MultiIndex d} (hα : α≠0) : derivativeList α≠[] := by
  intro h
  apply hα
  ext i
  have hi := derivativeList_count α i
  simpa only [h,List.count_nil,Pi.zero_apply] using hi.symm

#print axioms countIndex_derivativeList
end BecknerOnofri.Friedrichs.MixedSpatial
