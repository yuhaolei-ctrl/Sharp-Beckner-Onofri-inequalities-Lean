import BecknerOnofri.CircleTorusFlowDefinitions
import BecknerOnofri.CirclePoissonMultiplier
import BecknerOnofri.CircleTorusRegularity
import BecknerOnofri.CircleLambda

/-! Continuity, exact Fourier multipliers and convergent reconstruction of
the actual Poisson flow on the product-torus representation of the circle. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
namespace BecknerOnofri.HighDim.CirclePoisson
open CircleOuter CircleRegularity CircleFisher Legacy.TorusEndpoint
open Legacy.BecknerOnofri.WeightedWiener

theorem torus_flow_continuous (s : ℝ) (hs : 0<s) (p : Torus 1 → ℝ) (hp : Continuous p) :
    Continuous (torusFlow s p) := by
  have hpc : Continuous (fun z : UnitAddCircle => p (fun _ => z)) :=
    hp.comp (continuous_pi (fun _ => continuous_id))
  have h := smoothing_continuous (Real.exp (-s)) (Real.exp_pos _).le
    (Real.exp_lt_one_iff.mpr (by linarith)) _ hpc
  exact (h.comp (continuous_apply 0)).congr (fun x => by simp [torusFlow,hs.ne'])

theorem torus_flow_coefficient (s : ℝ) (hs : 0<s) (p : Torus 1 → ℝ) (hp : Continuous p)
    (k : Frequency 1) :
    UnitAddTorus.mFourierCoeff (fun x => (torusFlow s p x:ℂ)) k=
      (Real.exp (-|(k (0:Fin 1):ℝ)| * s):ℂ)*UnitAddTorus.mFourierCoeff (fun x => (p x:ℂ)) k := by
  have hk : (fun _ : Fin 1 => k 0)=k := funext (fun i => congrArg k (Subsingleton.elim 0 i))
  have hpc : Continuous (fun z : UnitAddCircle => p (fun _ => z)) :=
    hp.comp (continuous_pi (fun _ => continuous_id))
  have h := flow_coefficient s hs _ hpc (k 0)
  rw [← torus_coefficient_circle (fun x => (p x:ℂ)),hk] at h
  rw [← hk,torus_coefficient_circle]
  simp only [torusFlow,if_neg hs.ne',Nat.cast_natAbs,Int.cast_abs] at h ⊢
  simpa only [hk,neg_mul] using h

theorem torus_flow_weighted (s : ℝ) (hs : 0<s) (p : Torus 1 → ℝ) (hp : Continuous p)
    (hw : Summable (fun k => linearWeight k*‖UnitAddTorus.mFourierCoeff (fun x => (p x:ℂ)) k‖)) :
    Summable (fun k => linearWeight k*‖UnitAddTorus.mFourierCoeff (fun x => (torusFlow s p x:ℂ)) k‖) := by
  apply Summable.of_nonneg_of_le (fun k => mul_nonneg (linearWeight_isWeight.nonneg k) (norm_nonneg _)) _ hw
  intro k
  rw [torus_flow_coefficient s hs p hp,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  have hE : Real.exp (-|(k (0:Fin 1):ℝ)| * s)≤1 := Real.exp_le_one_iff.mpr (by nlinarith [abs_nonneg (k (0:Fin 1):ℝ)])
  exact mul_le_mul_of_nonneg_left
    (mul_le_of_le_one_left (norm_nonneg _) hE) (linearWeight_isWeight.nonneg k)

theorem torus_flow_series (s : ℝ) (hs : 0<s) (p : Torus 1 → ℝ) (hp : Continuous p)
    (hw : Summable (fun k => linearWeight k*‖UnitAddTorus.mFourierCoeff (fun x => (p x:ℂ)) k‖))
    (x : Torus 1) :
    (torusFlow s p x:ℂ)=∑' k,(Real.exp (-|(k (0:Fin 1):ℝ)| * s):ℂ)*
      UnitAddTorus.mFourierCoeff (fun y => (p y:ℂ)) k*UnitAddTorus.mFourier k x := by
  let P : C(Torus 1,ℂ) := ⟨fun x => (torusFlow s p x:ℂ),
    Complex.continuous_ofReal.comp (torus_flow_continuous s hs p hp)⟩
  have hwf := torus_flow_weighted s hs p hp hw
  have h := UnitAddTorus.hasSum_mFourier_series_apply_of_summable (f:=P)
    (summable_norm linearWeight_isWeight hwf).of_norm x
  have he (k : Frequency 1) : UnitAddTorus.mFourierCoeff P k=
      (Real.exp (-|(k (0:Fin 1):ℝ)| * s):ℂ)*UnitAddTorus.mFourierCoeff (fun y => (p y:ℂ)) k :=
    torus_flow_coefficient s hs p hp k
  change P x=_
  simpa only [he,smul_eq_mul] using h.tsum_eq.symm

#print axioms torus_flow_series
end BecknerOnofri.HighDim.CirclePoisson
