import BecknerOnofri.CircleBesselSupersolution

/-! The source's Riccati supersolution comparison. Multiplication by h
removes the singular coefficient at zero; the positive-barrier argument
handles the same first-contact step without an asymptotic premise. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
namespace BecknerOnofri.HighDim.CircleScalar

theorem besselMoment_first_le_supersolution (b : ℝ) (hb : 0≤b) :
    besselMoment 1 b≤b/Real.sqrt (1+b^2) := by
  let f : ℝ → ℝ := fun h => h*(besselMoment 1 h-riccatiSupersolution h)
  let f' : ℝ → ℝ := fun h => (besselMoment 1 h-riccatiSupersolution h)+
    h*(1+besselMoment 2 h-2*(besselMoment 1 h)^2-riccatiSupersolutionSlope h)
  have hd (h : ℝ) : HasDerivAt f (f' h) h := by
    have hh := (hasDerivAt_id h).mul
      ((besselMoment_first_derivative h).sub (riccatiSupersolution_derivative h))
    convert hh using 1 <;> first | rfl | (dsimp [f']; ring)
  have hf : Continuous f := continuous_iff_continuousAt.mpr (fun h => (hd h).continuousAt)
  have hineq (h : ℝ) (hh : 0≤h) :
      f' h≤ -2*(besselMoment 1 h+riccatiSupersolution h)*f h := by
    have hres := riccatiSupersolution_weighted_residual h
    have hp : 0≤h*(Real.sqrt (1+h^2)-1)^2/(Real.sqrt (1+h^2))^3 := by positivity
    have hr := besselMoment_recurrence h
    dsimp [f',f]
    nlinarith
  have hzero : f 0=0 := by simp [f]
  have hfnon : f b≤0 := by
    apply le_of_forall_pos_le_add
    intro ε hε
    have hbound := image_le_of_deriv_right_lt_deriv_boundary
      (a:=0) (b:=b) hf.continuousOn
      (fun h _ => (hd h).hasDerivWithinAt)
      (B:=fun _ : ℝ => ε) (B':=fun _ => 0)
      (by simpa [hzero] using hε.le)
      (fun h => hasDerivAt_const h ε) (fun h hh he => ?_)
      (show b ∈ Icc (0:ℝ) b from ⟨hb,le_rfl⟩)
    · simpa using hbound
    · have hhpos : 0<h := by
        by_contra hn
        have hz : h=0 := le_antisymm (le_of_not_gt hn) hh.1
        rw [hz,hzero] at he
        linarith
      have hr : 0≤besselMoment 1 h := besselMoment_nonneg 1 hh.1
      have hs : 0<riccatiSupersolution h := by
        unfold riccatiSupersolution
        exact div_pos hhpos (Real.sqrt_pos.mpr (by positivity))
      have hh' := hineq h hh.1
      rw [he] at hh'
      have hp := mul_pos (by linarith : 0<2*(besselMoment 1 h+riccatiSupersolution h)) hε
      linarith
  by_cases hb0 : b=0
  · simp [hb0,besselMoment_one_zero]
  · have hbpos : 0<b := lt_of_le_of_ne hb (Ne.symm hb0)
    have h : besselMoment 1 b-riccatiSupersolution b≤0 :=
      nonpos_of_mul_nonpos_right hfnon hbpos
    exact sub_nonpos.mp h

#print axioms besselMoment_first_le_supersolution
end BecknerOnofri.HighDim.CircleScalar
