import BecknerOnofri.VariationalTransitionQuotient
import BecknerOnofri.ConcentrationDivergence

/-! Convex-combination inequalities for the actual extended-real suprema.
They remain meaningful where the supremum is infinite and do not assume
finiteness at the concentration endpoint. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
namespace BecknerOnofri.HighDim.VariationalCurves

lemma pressure_convex_combination {d : ℕ} (hd : 0 < d) (β γ a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    pressure d (a*β+b*γ) ≤ (a:EReal)*pressure d β+(b:EReal)*pressure d γ := by
  apply iSup_le fun ρ => iSup_le fun hρ => ?_
  change pressureValue (a*β+b*γ) ρ ≤ _
  have hβ : pressureValue β ρ ≤ pressure d β := le_iSup_of_le ρ (le_iSup_of_le hρ le_rfl)
  have hγ : pressureValue γ ρ ≤ pressure d γ := le_iSup_of_le ρ (le_iSup_of_le hρ le_rfl)
  have he : pressureValue (a*β+b*γ) ρ = (a:EReal)*pressureValue β ρ+(b:EReal)*pressureValue γ ρ := by
    rw [pressureValue_eq hd _ ρ hρ,pressureValue_eq hd _ ρ hρ,pressureValue_eq hd _ ρ hρ,
      ← EReal.coe_mul,← EReal.coe_mul,← EReal.coe_add,EReal.coe_eq_coe_iff]
    linear_combination entropy ρ*hab
  rw [he]
  exact add_le_add (mul_le_mul_of_nonneg_left hβ (by exact_mod_cast ha))
    (mul_le_mul_of_nonneg_left hγ (by exact_mod_cast hb))

lemma coefficient_convex_combination {d : ℕ} (hd : 0 < d) (A B a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    coefficientDefect d (a*A+b*B) ≤ (a:EReal)*coefficientDefect d A+(b:EReal)*coefficientDefect d B := by
  apply iSup_le fun u => iSup_le fun hu => ?_
  have hA : logPartition u-((A*potentialEnergy u:ℝ):EReal) ≤ coefficientDefect d A :=
    le_iSup_of_le u (le_iSup_of_le hu le_rfl)
  have hB : logPartition u-((B*potentialEnergy u:ℝ):EReal) ≤ coefficientDefect d B :=
    le_iSup_of_le u (le_iSup_of_le hu le_rfl)
  have h := add_le_add (mul_le_mul_of_nonneg_left hA (by exact_mod_cast ha : (0:EReal) ≤ a))
    (mul_le_mul_of_nonneg_left hB (by exact_mod_cast hb : (0:EReal) ≤ b))
  refine le_trans ?_ h
  rw [logPartition_eq_log_integral hd u hu]
  repeat rw [← EReal.coe_sub]
  rw [← EReal.coe_mul,← EReal.coe_mul,← EReal.coe_add]
  apply le_of_eq
  apply congrArg (fun x : ℝ => (x:EReal))
  linear_combination -(Real.log (∫ x, Real.exp (centered u x) ∂torusMeasure d))*hab

lemma pressure_monotone {d : ℕ} (hd : 0 < d) : Monotone (pressure d) := by
  intro β γ hβγ
  apply iSup_le fun ρ => iSup_le fun hρ => ?_
  apply le_trans ?_ (show pressureValue γ ρ ≤ pressure d γ from le_iSup_of_le ρ (le_iSup_of_le hρ le_rfl))
  change pressureValue β ρ ≤ pressureValue γ ρ
  rw [pressureValue_eq hd _ ρ hρ,pressureValue_eq hd _ ρ hρ]
  exact EReal.coe_le_coe_iff.mpr (sub_le_sub_right (mul_le_mul_of_nonneg_right hβγ (interaction_nonneg hd ρ)) _)

#print axioms pressure_convex_combination
#print axioms coefficient_convex_combination
#print axioms pressure_monotone
end BecknerOnofri.HighDim.VariationalCurves
