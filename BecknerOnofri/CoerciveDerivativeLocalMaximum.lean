module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

@[expose] public section

/-! A genuine local maximum criterion from a coercive second derivative.
The proof controls first derivatives uniformly on a neighborhood and integrates
along segments; negativity of a Hessian is not used as a definition of a maximum. -/
noncomputable section
open Filter Set
open scoped Topology
namespace BecknerOnofri

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

 theorem isLocalMax_of_radial_derivative_nonpos {f : E → ℝ} {G : E → E →L[ℝ] ℝ} {a : E}
    (h : ∀ᶠ x in 𝓝 a,HasFDerivAt f (G x) x ∧ G x (x-a)≤0) : IsLocalMax f a := by
  obtain ⟨ε,hε,he⟩ := Metric.eventually_nhds_iff.mp h
  apply Filter.Eventually.mono (Metric.ball_mem_nhds a hε)
  intro y hy
  have hy' : ‖y-a‖<ε := by simpa only [Metric.mem_ball,dist_eq_norm] using hy
  let p : ℝ → E := fun t => a+t • (y-a)
  have hp (t : ℝ) (ht : t∈Icc (0:ℝ) 1) : dist (p t) a<ε := by
    rw [dist_eq_norm]
    have hh : p t-a=t • (y-a) := by dsimp [p]; abel
    rw [hh,norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1]
    exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) ht.2) hy'
  have hder (t : ℝ) (ht : t∈Icc (0:ℝ) 1) :
      HasDerivAt (fun s => f (p s)) (G (p t) (y-a)) t := by
    apply ((he (hp t ht)).1).comp_hasDerivAt t
    convert! ((hasDerivAt_id t).smul_const (y-a)).const_add a using 1 <;> simp [p]
  have hcont : ContinuousOn (fun t => f (p t)) (Icc (0:ℝ) 1) :=
    fun t ht => (hder t ht).continuousAt.continuousWithinAt
  have hm : AntitoneOn (fun t => f (p t)) (Icc (0:ℝ) 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) hcont
      (fun t ht => (hder t (interior_subset ht)).differentiableAt.differentiableWithinAt)
    intro t ht
    rw [interior_Icc] at ht
    rw [(hder t ⟨ht.1.le,ht.2.le⟩).deriv]
    have hh := (he (hp t ⟨ht.1.le,ht.2.le⟩)).2
    have heq : p t-a=t • (y-a) := by dsimp [p]; abel
    rw [heq,map_smul,smul_eq_mul] at hh
    exact nonpos_of_mul_nonpos_right hh ht.1
  have hend := hm (by simp : (0:ℝ)∈Icc (0:ℝ) 1)
    (by simp : (1:ℝ)∈Icc (0:ℝ) 1) (by norm_num : (0:ℝ)≤1)
  simpa [p] using hend

 theorem isLocalMax_of_coercive_derivative {f : E → ℝ} {G : E → E →L[ℝ] ℝ} {a : E}
    {A : E →L[ℝ] E →L[ℝ] ℝ} {c : ℝ} (hc : 0<c)
    (hf : ∀ᶠ x in 𝓝 a,HasFDerivAt f (G x) x)
    (hG : HasFDerivAt G A a) (hzero : G a=0)
    (hcoerce : ∀ v : E,A v v≤-c*‖v‖^2) : IsLocalMax f a := by
  apply isLocalMax_of_radial_derivative_nonpos
  filter_upwards [hf,hG.isLittleO.bound (show 0<c/2 by positivity)] with x hx he
  refine ⟨hx,?_⟩
  let v := x-a
  have hb := (G x-G a-A v).le_opNorm v
  have hl : (G x-G a-A v) v≤‖(G x-G a-A v) v‖ := by simpa only [Real.norm_eq_abs] using le_abs_self ((G x-G a-A v) v)
  have he' : ‖G x-G a-A v‖≤(c/2)*‖v‖ := he
  have hh := hl.trans (hb.trans (mul_le_mul_of_nonneg_right he' (norm_nonneg v)))
  simp only [hzero,sub_zero,sub_apply] at hh
  have ha := hcoerce v
  have hp := sq_nonneg ‖v‖
  change G x v≤0
  nlinarith

#print axioms isLocalMax_of_coercive_derivative
end BecknerOnofri
