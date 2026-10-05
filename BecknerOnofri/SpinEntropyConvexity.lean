module

public import BecknerOnofri.SpinSupportingParabola

@[expose] public section

/-! The fixed-mean entropy convexity inequality, including boundary targets. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open Set
namespace BecknerOnofri.HighDim.Spin

theorem entropy_bregman_coordinate (x y b : ℝ) (hy : 0<y) (hb : 0<b) :
    x*Real.log (x/b)-y*Real.log (y/b)-
      (Real.log y-Real.log b+1)*(x-y)=x*Real.log (x/y)-x+y := by
  by_cases hx : x=0
  · rw [hx,Real.log_div hy.ne' hb.ne']
    ring
  · rw [Real.log_div hx hb.ne',Real.log_div hy.ne' hb.ne',Real.log_div hx hy.ne']
    ring

theorem entropy_bregman_identity {p q : Count → ℝ}
    (hpos : ∀ j,0<p j) (hp : (∑ j : Count,p j)=1) (hq : (∑ j : Count,q j)=1) :
    relativeEntropy q reference-relativeEntropy p reference-entropySlope p (q-p) 0=
      relativeEntropy q p := by
  simp only [relativeEntropy,entropySlope,zero_mul,add_zero,Pi.sub_apply]
  rw [← Finset.sum_sub_distrib,← Finset.sum_sub_distrib]
  simp_rw [entropy_bregman_coordinate _ _ _ (hpos _) (reference_pos _)]
  rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,hq,hp]
  ring

theorem fixed_mean_entropy_convexity {p q : Count → ℝ}
    (hp : Feasible p) (hpos : ∀ j,0<p j) (hq : Feasible q) (hmean : mean p=mean q) :
    functional p+(∑ j : Count,gradient p j*(q j-p j))+
      relativeEntropy q p/5≤functional q := by
  let v := q-p
  let f : ℝ → ℝ := fun t => functional (p+t•v)-relativeEntropy (p+t•v) reference/5
  let f' : ℝ → ℝ := fun t => functionalSlope p v t-entropySlope p v t/5
  let f'' : ℝ → ℝ := fun t => functionalHessian p v t-entropyHessian p v t/5
  have hv : (∑ j : Count,v j)=0 := by
    simp [v,Finset.sum_sub_distrib,hp.2.1,hq.2.1]
  have hvx : mean v=0 := by simp [v,mean_sub,hmean]
  have hcont : Continuous f := (functional_segment_continuous p v).sub
    ((relativeEntropy_reference_continuous.comp (by fun_prop)).div_const 5)
  have hd (t : ℝ) (ht : ∀ j,0<p j+t*v j) : HasDerivAt f (f' t) t :=
    (functional_segment_derivative p v t ht).sub ((entropy_segment_derivative p v t ht).div_const 5)
  have hdd (t : ℝ) (ht : ∀ j,0<p j+t*v j) : HasDerivAt f' (f'' t) t :=
    (functional_segment_second_derivative p v t ht).sub
      ((entropy_segment_second_derivative p v t ht).div_const 5)
  have hb (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) : 0≤f'' t := by
    have hr := feasible_segment hp hq ⟨ht.1.le,ht.2.le⟩
    have hrpos : ∀ j,0<(p+t•v) j := segment_positive hpos hq ht.1.le ht.2
    have hc := fixed_mean_curvature hr hrpos hv hvx
    change quadratic v≤(9/10)*entropyHessian p v t at hc
    dsimp [f'',functionalHessian]
    linarith
  have h := second_order_support hcont.continuousOn (hd 0 (by simpa using hpos))
    (fun t ht => hd t (segment_positive hpos hq ht.1.le ht.2))
    (fun t ht => hdd t (segment_positive hpos hq ht.1.le ht.2)) hb
  have he : p+(1:ℝ)•v=q := by dsimp [v]; module
  simp only [f,f',zero_smul,add_zero,he,zero_div] at h
  have hB := entropy_bregman_identity hpos hp.2.1 hq.2.1
  have hG := slope_at_zero_eq_gradient p v hpos
  change functionalSlope p v 0=(∑ j : Count,gradient p j*(q j-p j)) at hG
  change relativeEntropy q reference-relativeEntropy p reference-entropySlope p v 0=
    relativeEntropy q p at hB
  linarith

#print axioms fixed_mean_entropy_convexity
end BecknerOnofri.HighDim.Spin
