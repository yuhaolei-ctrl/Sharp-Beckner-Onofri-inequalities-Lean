module

public import BecknerOnofri.LocalElevenCore.SubsetCubic
public import BecknerOnofri.LocalElevenCore.ReducedEnergyDeltaRemainder

@[expose] public section

noncomputable section
open scoped BigOperators
namespace BecknerOnofri.HighDim.LocalEleven.SubsetDiagonal
open ContinuousFirstShell ReducedQuarticExpansion QuadraticModes

theorem line_fourth_sum {d : ℕ} (I : Finset (Fin d)) (t : ℝ) :
    (∑ i,‖line I t i‖^4)=(I.card:ℝ)*t^4 := by
  have habs : |t|^4=t^4 := by
    calc
      _=(|t|^2)^2 := by ring
      _=(t^2)^2 := by rw [sq_abs]
      _=_ := by ring
  have he (i : Fin d) : ‖line I t i‖^4 = if i∈I then t^4 else 0 := by
    by_cases hi : i∈I <;> simp [line_apply,hi,Complex.norm_real,Real.norm_eq_abs,habs]
  simp_rw [he]
  simp

theorem quartic_line {d : ℕ} (I : Finset (Fin d)) (t : ℝ) :
    quarticValue (line I t)=-(I.card:ℝ)*coefficient I/2*t^4 := by
  have h := amplitude_sum_square (line I t)
  rw [line_square_sum,line_fourth_sum] at h
  unfold quarticValue
  rw [line_fourth_sum]
  have hm : mixedAmplitudeSum (line I t)=((I.card:ℝ)^2-I.card)/2*t^4 := by
    nlinarith [h]
  rw [hm]
  unfold coefficient
  ring

theorem support_pressure_coefficient {d : ℕ} (I : Finset (Fin d)) (hI : I.Nonempty) :
    (I.card:ℝ)/(2*coefficient I) = -1/(4*branchQuarticCoefficient d I.card) := by
  have hn : (I.card:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr hI)
  unfold coefficient branchQuarticCoefficient
  field_simp
  <;> ring

#print axioms quartic_line
end BecknerOnofri.HighDim.LocalEleven.SubsetDiagonal
