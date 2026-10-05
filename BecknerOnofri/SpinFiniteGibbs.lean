module

public import BecknerOnofri.SpinEntropyConvexity
public import BecknerOnofri.Entropy

@[expose] public section

/-! The finite Gibbs variational estimate used in the small-mean proof. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace BecknerOnofri.HighDim.Spin

theorem weighted_log_div (x y : ℝ) (hy : 0<y) :
    x*Real.log (x/y)=x*Real.log x-x*Real.log y := by
  by_cases hx : x=0
  · simp [hx]
  · rw [Real.log_div hx hy.ne']
    ring

theorem finite_partition_pos (p H : Count → ℝ) (hp : ∀ j,0<p j) :
    0<∑ j : Count,p j*Real.exp (H j) :=
  Finset.sum_pos (fun j _ => mul_pos (hp j) (Real.exp_pos _)) Finset.univ_nonempty

/-- No positivity assumption is imposed on the candidate probability q. -/
theorem finite_gibbs_variational (p q H : Count → ℝ)
    (hp : ∀ j,0<p j) (hq : ∀ j,0≤q j) (hmass : (∑ j : Count,q j)=1) :
    (∑ j : Count,q j*H j)-relativeEntropy q p ≤
      Real.log (∑ j : Count,p j*Real.exp (H j)) := by
  let Z := ∑ j : Count,p j*Real.exp (H j)
  have hZ : 0<Z := finite_partition_pos p H hp
  have he (j : Count) : Real.exp (H j+Real.log (p j)-Real.log Z)=p j*Real.exp (H j)/Z := by
    rw [Real.exp_sub,Real.exp_add,Real.exp_log (hp j),Real.exp_log hZ]
    ring
  have hj (j : Count) : q j*H j-q j*Real.log (q j/p j) ≤
      q j*Real.log Z-q j+p j*Real.exp (H j)/Z := by
    have h := BecknerOnofri.HighDim.entropy_young (q j)
      (H j+Real.log (p j)-Real.log Z) (hq j)
    rw [he] at h
    rw [weighted_log_div _ _ (hp j)]
    nlinarith
  have h := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset Count)) => hj j)
  have hz : (∑ j : Count,p j*Real.exp (H j)/Z)=1 := by
    rw [← Finset.sum_div]
    exact div_self hZ.ne'
  simpa only [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.sum_mul,
    hmass,one_mul,hz,sub_add_cancel,relativeEntropy] using h

/-- Reduction of the fixed-mean entropy lower bound to the exponential moment
of the actual nonaffine gradient term. -/
theorem functional_lower_of_gradient_decomposition (p q H : Count → ℝ) (ell η : ℝ)
    (hp : Feasible p) (hpos : ∀ j,0<p j) (hq : Feasible q) (hmean : mean p=mean q)
    (hgrad : ∀ j,gradient p j=ell+η*meanCoordinate j-H j)
    (hcenter : (∑ j : Count,p j*H j)=0) :
    functional p-(1/5)*Real.log (∑ j : Count,p j*Real.exp (5*H j))≤functional q := by
  have hg := fixed_mean_entropy_convexity hp hpos hq hmean
  have hv := finite_gibbs_variational p q (fun j => 5*H j) hpos hq.1 hq.2.1
  have hpair : (∑ j : Count,gradient p j*(q j-p j))= -(∑ j : Count,q j*H j) := by
    simp_rw [hgrad]
    have he (j : Count) : (ell+η*meanCoordinate j-H j)*(q j-p j)=
      ell*q j-ell*p j+η*(meanCoordinate j*q j)-η*(meanCoordinate j*p j)-q j*H j+p j*H j := by ring
    simp_rw [he]
    simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum,
      hp.2.1,hq.2.1,hcenter,mean,mul_one,sub_self,zero_add,add_zero]
    change η*mean q-η*mean p-(∑ j : Count,q j*H j)=_
    rw [hmean]
    ring
  have hscale : (∑ j : Count,q j*(5*H j))=5*(∑ j : Count,q j*H j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hpair] at hg
  rw [hscale] at hv
  linarith

#print axioms finite_gibbs_variational
#print axioms functional_lower_of_gradient_decomposition
end BecknerOnofri.HighDim.Spin
