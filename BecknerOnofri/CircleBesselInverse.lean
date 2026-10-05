module

public import BecknerOnofri.CircleGammaDefinitions
public import BecknerOnofri.CircleBesselComparison

@[expose] public section

/-! Existence and uniqueness of the actual inverse Bessel mean throughout
0≤t<1. The Riccati equation excludes a range bounded below one. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
namespace BecknerOnofri.HighDim.CircleScalar

theorem besselMoment_exceeds_mean (t : ℝ) (ht : 0≤t) (ht1 : t<1) :
    ∃ h : ℝ, 0≤h ∧ t<besselMoment 1 h := by
  by_contra! hn
  let c : ℝ := 1-t^2
  let H : ℝ := 1/c
  have hc : 0<c := by dsimp [c]; nlinarith
  have hH : 0<H := div_pos (by norm_num) hc
  let f : ℝ → ℝ := fun h => besselMoment 1 h-c*h
  let f' : ℝ → ℝ := fun h => deriv (besselMoment 1) h-c
  have hd (h : ℝ) : HasDerivAt f (f' h) h := by
    exact (besselMoment_first_derivative h).differentiableAt.hasDerivAt.sub
      ((hasDerivAt_id h).const_mul c) |>.congr_deriv (by simp [f'])
  have hb (h : ℝ) (hh : H≤h) : 0≤f' h := by
    have hhpos : 0<h := hH.trans_le hh
    have hR := besselMoment_nonneg 1 hhpos.le
    have hRt := hn h hhpos.le
    have hsq := pow_le_pow_left₀ hR hRt 2
    have hhprod : 1≤h*c := (div_le_iff₀ hc).mp hh
    have hdiv : besselMoment 1 h/h≤c := by
      apply (div_le_iff₀ hhpos).mpr
      nlinarith
    have he := besselMoment_first_riccati h hhpos.ne'
    dsimp [f',c] at *
    linarith
  have hm : MonotoneOn f (Ici H) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici H)
      (continuous_iff_continuousAt.mpr (fun h => (hd h).continuousAt)).continuousOn
      (fun h _ => (hd h).hasDerivWithinAt)
    intro h hh
    exact hb h (mem_Ici.mp (interior_subset hh))
  have hstep : 0≤2/c := by positivity
  have hm' := hm (mem_Ici.mpr (le_rfl : H≤H)) (mem_Ici.mpr (show H≤H+2/c by linarith))
    (show H≤H+2/c by linarith)
  have hlow := besselMoment_nonneg 1 hH.le
  have hupp := hn (H+2/c) (by linarith)
  have hcancel : c*(H+2/c)=c*H+2 := by field_simp [hc.ne']
  dsimp [f] at hm'
  rw [hcancel] at hm'
  linarith

theorem parameter_mean {t : ℝ} (ht : 0≤t) (ht1 : t<1) :
    besselMoment 1 (parameter t)=t ∧ 0≤parameter t := by
  obtain ⟨h,hh,hR⟩ := besselMoment_exceeds_mean t ht ht1
  have hcont : Continuous (besselMoment 1) := continuous_iff_continuousAt.mpr
    (fun x => (besselMoment_first_derivative x).continuousAt)
  obtain ⟨x,hx,he⟩ := intermediate_value_Icc hh hcont.continuousOn
    (show t ∈ Icc (besselMoment 1 0) (besselMoment 1 h) from
      ⟨by simpa [besselMoment_one_zero] using ht,hR.le⟩)
  have hp : besselMoment 1 (parameter t)=t := Function.invFun_eq ⟨x,he⟩
  have heq : parameter t=x := besselMoment_first_strictMono.injective (hp.trans he.symm)
  exact ⟨hp,by simpa [heq] using hx.1⟩

#print axioms parameter_mean
end BecknerOnofri.HighDim.CircleScalar
