import BecknerOnofri.OrderParameterDefinitions
import BecknerOnofri.LocalHighShell
import BecknerOnofri.ComplementGap

/-! The finite coordinate expression is exactly the complete |k|=1 shell. -/
noncomputable section
open scoped BigOperators
namespace BecknerOnofri.HighDim.OrderParameterOnset

lemma signedAxis_true {d : ℕ} (i : Fin d) : signedAxis i true = axisFrequency i := by
  funext j
  simp [signedAxis,axisFrequency]

lemma signedAxis_false {d : ℕ} (i : Fin d) : signedAxis i false = -axisFrequency i := by
  funext j
  simp [signedAxis,axisFrequency,apply_ite]

lemma frequencyLength_eq_one_iff {d : ℕ} (k : Frequency d) :
    frequencyLength k = 1 ↔ latticeSquare k = 1 := by
  rw [frequencyLength,← latticeSquare_cast,Real.sqrt_eq_one]
  exact_mod_cast (Iff.rfl : latticeSquare k = 1 ↔ latticeSquare k = 1)

/-- No first-shell modes are omitted or counted twice in the trusted order parameter. -/
theorem orderParameter_squared {d : ℕ} (f : Torus d → ℝ) :
    (firstShellOrderParameter f)^2 =
      ∑' k : Frequency d, if frequencyLength k = 1 then ‖fourierCoeff f k‖^2 else 0 := by
  classical
  let F : Frequency d → ℝ := fun k => if latticeSquare k = 1 then ‖fourierCoeff f k‖^2 else 0
  have hs : Function.support F ⊆ Set.range (fun p : Fin d × Bool => signedAxis p.1 p.2) := by
    intro k hk
    have hl : latticeSquare k = 1 := by
      by_contra hn
      exact hk (by simp [F,hn])
    rcases (latticeSquare_eq_one_iff k).mp hl with ⟨i,he|he⟩
    · exact ⟨(i,true),(signedAxis_true i).trans he.symm⟩
    · exact ⟨(i,false),(signedAxis_false i).trans he.symm⟩
  have he := signedAxis_injective.tsum_eq hs
  simp only [tsum_fintype,Fintype.sum_prod_type,Fintype.sum_bool,
    signedAxis_true,signedAxis_false,F,latticeSquare_axis,latticeSquare_neg,if_true] at he
  rw [firstShellOrderParameter,Real.sq_sqrt (Finset.sum_nonneg (fun i _ =>
    add_nonneg (sq_nonneg _) (sq_nonneg _)))]
  simp_rw [frequencyLength_eq_one_iff]
  simpa only [F,add_comm] using he

#print axioms orderParameter_squared
end BecknerOnofri.HighDim.OrderParameterOnset
