import BecknerOnofri.CircleTorusFlow

/-! Uniform bounds along the actual positive-time Poisson flow. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
namespace BecknerOnofri.HighDim.CirclePoisson
open CircleOuter CircleFisher Legacy.TorusEndpoint

theorem torus_flow_bounds (p : Torus 1 → ℝ) (hp : Continuous p) (a b : ℝ)
    (hlo : ∀ x,a≤p x) (hhi : ∀ x,p x≤b) (s : ℝ) (hs : 0<s) (x : Torus 1) :
    a≤torusFlow s p x ∧ torusFlow s p x≤b := by
  have h := smoothing_bounds (Real.exp (-s)) (Real.exp_pos _).le
    (Real.exp_lt_one_iff.mpr (by linarith)) (fun z : UnitAddCircle => p (fun _ => z))
    (hp.comp (continuous_pi (fun _ => continuous_id))) a b (fun z => hlo (fun _ => z))
    (fun z => hhi (fun _ => z)) (x 0)
  simpa only [torusFlow,if_neg hs.ne'] using h

theorem lambda_flow_bound (p : Torus 1 → ℝ) (hp : Continuous p)
    (hw : Summable (fun k => linearWeight k*‖UnitAddTorus.mFourierCoeff (fun x => (p x:ℂ)) k‖))
    (s : ℝ) (hs : 0<s) (x : Torus 1) :
    |lambda (torusFlow s p) x|≤
      ∑' k,|(k (0:Fin 1):ℝ)| * ‖UnitAddTorus.mFourierCoeff (fun y => (p y:ℂ)) k‖ := by
  let F : Frequency 1 → ℂ := fun k => ((|(k (0:Fin 1):ℝ)|:ℝ):ℂ)*
    UnitAddTorus.mFourierCoeff (fun y => (torusFlow s p y:ℂ)) k*UnitAddTorus.mFourier k x
  have hbase := first_moment_summable (UnitAddTorus.mFourierCoeff (fun y => (p y:ℂ))) hw
  have hb (k : Frequency 1) : ‖F k‖≤
      |(k (0:Fin 1):ℝ)| * ‖UnitAddTorus.mFourierCoeff (fun y => (p y:ℂ)) k‖ := by
    dsimp only [F]
    rw [torus_flow_coefficient s hs p hp]
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_abs,
      abs_of_pos (Real.exp_pos _),mFourier_norm_apply,mul_one]
    have hE : Real.exp (-|(k (0:Fin 1):ℝ)| * s)≤1 := Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (abs_nonneg _)) hs.le)
    exact mul_le_mul_of_nonneg_left
      (mul_le_of_le_one_left (norm_nonneg _) hE) (abs_nonneg _)
  have hnorm : Summable (fun k => ‖F k‖) :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _) hb hbase
  calc
    |lambda (torusFlow s p) x|≤‖∑' k,F k‖ := Complex.abs_re_le_norm _
    _ ≤ ∑' k,‖F k‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ _ := hnorm.tsum_le_tsum hb hbase

#print axioms lambda_flow_bound
end BecknerOnofri.HighDim.CirclePoisson
