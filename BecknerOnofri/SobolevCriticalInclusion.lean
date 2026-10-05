import BecknerOnofri.BranchDefinitions
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section
namespace BecknerOnofri.HighDim

/-- The critical-domain premise in the local-maximum interface is automatic on
H^s for s≥d/2, including the endpoint. -/
theorem inCriticalSobolev_of_inSobolev {d : ℕ} {s : ℝ}
    (hs : (d:ℝ)/2≤s) {u : Torus d → ℝ} (hu : InSobolev s u) :
    InCriticalSobolev u := by
  refine ⟨hu.1,?_⟩
  apply (hu.2.subtype (fun k => k≠0)).of_nonneg_of_le
    (fun k => by unfold potentialTerm frequencyLength; positivity)
  intro k
  have ha : 0≤2*Real.pi*frequencyLength k.val := by
    unfold frequencyLength
    positivity
  have hw : (2*Real.pi*frequencyLength k.val)^d ≤
      (1+(2*Real.pi*frequencyLength k.val)^2)^s := by
    calc
      _ = ((2*Real.pi*frequencyLength k.val)^2)^((d:ℝ)/2) := by
        rw [← Real.rpow_natCast,← Real.rpow_two,← Real.rpow_mul ha]
        congr 1
        push_cast
        ring
      _ ≤ (1+(2*Real.pi*frequencyLength k.val)^2)^((d:ℝ)/2) :=
        Real.rpow_le_rpow (sq_nonneg _) (by linarith) (by positivity)
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg (2*Real.pi*frequencyLength k.val)]) hs
  exact mul_le_mul_of_nonneg_right hw (sq_nonneg _)

#print axioms inCriticalSobolev_of_inSobolev
end BecknerOnofri.HighDim
