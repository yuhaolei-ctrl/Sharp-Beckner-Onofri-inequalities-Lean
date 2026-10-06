module

public import BecknerOnofri.LocalElevenCore.ActiveHessianMatrix
public import BecknerOnofri.LocalElevenCore.ActiveFactorSupportedLine
public import BecknerOnofri.AnalyticPitchforkRadialBranch

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter Asymptotics
open scoped Topology
namespace BecknerOnofri.HighDim.LocalEleven.SquaredReducedEnergy
open AmplitudeLinearization ActiveAmplitudeFactor

def squaredBranchInput {d : ℕ} (hd : 11≤d) (I : Finset (Fin d)) (j : Fin d) (hj : j∈I)
    (t : ℝ) : ℝ × Amplitudes d :=
  (SubsetDiagonal.parameter hd I j hj t,realLine I (t^2))

theorem squaredBranchInput_tendsto {d : ℕ} (hd : 11≤d) (I : Finset (Fin d))
    (j : Fin d) (hj : j∈I) :
    Tendsto (squaredBranchInput hd I j hj) (𝓝 0) (𝓝 (1,0)) := by
  have hp := (AnalyticPitchfork.parameter_analytic (SubsetDiagonal.pitchforkData hd I j hj)).continuousAt
  have hc : ContinuousAt (fun t : ℝ => realLine I (t^2)) 0 :=
    (realLine I).continuous.continuousAt.comp (continuousAt_id.pow 2)
  change Tendsto (fun t : ℝ => (AnalyticPitchfork.parameter
    (SubsetDiagonal.pitchforkData hd I j hj) t,realLine I (t^2))) (𝓝 0) (𝓝 (1,0))
  simpa only [AnalyticPitchfork.parameter_base,
    zero_pow (by norm_num : 2≠0),map_zero] using (hp.prodMk hc).tendsto

theorem sqrtLift_realLine_square {d : ℕ} (I : Finset (Fin d)) {t : ℝ} (ht : 0≤t) :
    sqrtLift I (realLine I (t^2))=realLine I t := by
  funext i
  by_cases hi : i∈I <;> simp [sqrtLift,realLine_apply,hi,Real.sqrt_sq ht]

theorem activeExtend_one {d : ℕ} (I : Finset (Fin d)) :
    activeExtend I (fun _ => 1)=realLine I 1 := by
  funext i
  by_cases hi : i∈I <;> simp [hi]

theorem sqrtDerivative_active_one {d : ℕ} (I : Finset (Fin d)) {t : ℝ} (ht : 0≤t) :
    sqrtDerivative I (realLine I (t^2)) (activeExtend I (fun _ => 1))=
      (1/(2*t)) • realLine I 1 := by
  rw [activeExtend_one]
  funext i
  by_cases hi : i∈I <;> simp [sqrtDerivative_apply,hi,Real.sqrt_sq ht]

/-- The row sum is the genuine scalar quotient's amplitude derivative divided
by 2 tau t, as follows from differentiating r=t². -/
theorem activeHessian_radial_entry {d : ℕ} (hd : 11≤d) (I : Finset (Fin d))
    (j : Fin d) (hj : j∈I) :
    ∀ᶠ t in 𝓝 (0:ℝ),0<t →
      activeHessian hd I (SubsetDiagonal.parameter hd I j hj t) (realLine I (t^2))
        (fun _ => 1) ⟨j,hj⟩ =
      -(AnalyticPitchfork.amplitudePartial (SubsetDiagonal.pitchforkData hd I j hj)
        (SubsetDiagonal.parameter hd I j hj t,t)/(2*SubsetDiagonal.parameter hd I j hj t*t)) := by
  have ht := AnalyticPitchfork.parameter_pair_tendsto (SubsetDiagonal.pitchforkData hd I j hj)
  filter_upwards [ht.eventually (factor_line_amplitudePartial hd I j hj)] with t hder htpos
  rw [activeHessian_apply,hessianMap_apply,if_pos hj,sqrtLift_realLine_square I htpos.le,
    sqrtDerivative_active_one I htpos.le]
  have hv : ((0:ℝ),(1/(2*t)) • realLine I 1)=(1/(2*t)) • ((0:ℝ),realLine I 1) := by simp
  rw [hv,map_smul]
  change fderiv ℝ (factor hd j) (SubsetDiagonal.parameter hd I j hj t,realLine I t)
    (0,realLine I 1)=_ at hder
  rw [hder]
  simp only [smul_eq_mul,div_eq_mul_inv,mul_inv_rev,SubsetDiagonal.parameter]
  ring

/-- Radial eigenvalue of the actual restricted Hessian, with its analytic
extension through zero and the precise O(t²) expansion. -/
theorem exists_active_radial_eigenvalue {d : ℕ} (hd : 11≤d) (I : Finset (Fin d))
    (j : Fin d) (hj : j∈I) :
    ∃ R : ℝ → ℝ,AnalyticAt ℝ R 0 ∧ R 0=2*quarticA d+quarticB d*((I.card:ℝ)-1) ∧
      ((fun t => R t-(2*quarticA d+quarticB d*((I.card:ℝ)-1)))
        =O[𝓝 (0:ℝ)] (fun t => ‖t‖^2)) ∧
      (∀ᶠ t in 𝓝 (0:ℝ),0<t →
        activeHessian hd I (SubsetDiagonal.parameter hd I j hj t) (realLine I (t^2))
          (fun _ => 1)=R t • (fun _ => 1)) := by
  let D := SubsetDiagonal.pitchforkData hd I j hj
  obtain ⟨R,hR,hR0,hRo,he⟩ := AnalyticPitchfork.exists_radial_branch_coefficient D
  have hc : -D.coefficient=2*quarticA d+quarticB d*((I.card:ℝ)-1) := by
    simp only [D,SubsetDiagonal.pitchforkData,SubsetDiagonal.coefficient,neg_neg]
  refine ⟨R,hR,hR0.trans hc,?_,?_⟩
  · simpa only [hc] using hRo
  · have hμ : ∀ᶠ t in 𝓝 (0:ℝ),SubsetDiagonal.parameter hd I j hj t≠0 := by
      have hp := (AnalyticPitchfork.parameter_analytic D).continuousAt.tendsto
      rw [AnalyticPitchfork.parameter_base] at hp
      exact hp.eventually (eventually_ne_nhds (by norm_num : (1:ℝ)≠0))
    filter_upwards [activeHessian_radial_entry hd I j hj,he,hμ,
      (squaredBranchInput_tendsto hd I j hj).eventually
        (activeHessian_equicorrelated hd I ⟨j,hj⟩)] with t hrow he hμ hm ht
    have hrow' := hrow ht
    change AnalyticPitchfork.amplitudePartial D (SubsetDiagonal.parameter hd I j hj t,t)=_ at he
    rw [he] at hrow'
    have hr : activeHessian hd I (SubsetDiagonal.parameter hd I j hj t) (realLine I (t^2))
        (fun _ => 1) ⟨j,hj⟩=R t := by
      rw [hrow']
      change -(-(2*SubsetDiagonal.parameter hd I j hj t*t)*R t /
        (2*SubsetDiagonal.parameter hd I j hj t*t))=R t
      field_simp
    obtain ⟨a,b,hab⟩ := hm (fun k hk => by
      simpa only [squaredBranchInput,realLine_apply,if_pos hk] using sq_pos_of_pos ht)
      (fun k hk l hl => by simp only [squaredBranchInput,realLine_apply,if_pos hk,if_pos hl])
    change activeHessian hd I (SubsetDiagonal.parameter hd I j hj t) (realLine I (t^2))=_ at hab
    rw [hab] at hr ⊢
    funext i
    simpa only [EquicorrelatedSpectrum.operator_apply,Pi.smul_apply,smul_eq_mul,mul_one] using hr

#print axioms exists_active_radial_eigenvalue
end BecknerOnofri.HighDim.LocalEleven.SquaredReducedEnergy
