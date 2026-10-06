module

public import BecknerOnofri.GreenLogLower

@[expose] public section

/-! Pointwise comparison of the logarithmically normalized Green function
with the average of its one-dimensional coordinate kernels. -/
noncomputable section
open MeasureTheory Set Legacy.TorusEndpoint
open scoped BigOperators
namespace BecknerOnofri.AdamsEndpoint
open Legacy.BecknerOnofri.GreenHeatPointwise

def coordinateComparisonConstant (d : ℕ) : ℝ :=
  upperConstant d + logarithmicLowerConstant 1

theorem heatGreen_coordinate_le {d : ℕ} (hd : 0 < d)
    (x : Fin d → ℝ) (hx : ∀ i, |x i| ≤ 1/2) (i : Fin d) (hxi : x i ≠ 0) :
    heatGreen (fun j => (x j : UnitAddCircle)) ≤
      heatGreen (fun _ : Fin 1 => (x i : UnitAddCircle)) + coordinateComparisonConstant d := by
  have hx0 : x ≠ 0 := by
    intro he
    exact hxi (by simpa using congrFun he i)
  have hr : |x i| ≤ Real.sqrt (coordinateRadiusSq x) := by
    have hh : (x i)^2 ≤ coordinateRadiusSq x :=
      Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    simpa only [Real.sqrt_sq_eq_abs] using Real.sqrt_le_sqrt hh
  have hl := Real.log_le_log (abs_pos.mpr hxi) hr
  have hu := heatGreen_le_log hd x hx hx0
  have hb := heatGreen_log_lower (by norm_num : 0 < (1 : ℕ))
    (fun _ : Fin 1 => x i) (fun _ => hx i) (by
      intro he
      exact hxi (by simpa using congrFun he (0 : Fin 1)))
  simp only [coordinateRadiusSq,Fin.sum_univ_one,Real.sqrt_sq_eq_abs] at hb
  unfold coordinateComparisonConstant
  linarith

theorem heatGreen_average_coordinates_le {d : ℕ} (hd : 0 < d)
    (x : Fin d → ℝ) (hx : ∀ i, |x i| ≤ 1/2) (hxi : ∀ i, x i ≠ 0) :
    heatGreen (fun j => (x j : UnitAddCircle)) ≤
      (∑ i, heatGreen (fun _ : Fin 1 => (x i : UnitAddCircle))) / (d : ℝ) +
        coordinateComparisonConstant d := by
  have hh := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => heatGreen_coordinate_le hd x hx i (hxi i))
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    Finset.sum_add_distrib] at hh
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  rw [mul_comm (d : ℝ) (heatGreen (fun j => (x j : UnitAddCircle)))] at hh
  have hdiv := (le_div_iff₀ hdR).2 hh
  simpa only [add_div, mul_div_cancel_left₀ _ hdR.ne'] using hdiv

#print axioms heatGreen_average_coordinates_le
end BecknerOnofri.AdamsEndpoint
