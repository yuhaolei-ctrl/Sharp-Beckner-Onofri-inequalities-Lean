import BecknerOnofri.LocalElevenCore.ActiveHessianRadial

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter Asymptotics
open scoped Topology
namespace BecknerOnofri.HighDim.LocalEleven.SquaredReducedEnergy
open AmplitudeLinearization ActiveAmplitudeFactor

/-- The transverse coefficient is an analytic germ of the actual Hessian,
with the manuscript's constant term and quadratic amplitude error. The
row-difference assertion is required when both selected indices are active. -/
theorem exists_active_transverse_coefficient {d : ℕ} (hd : 11≤d) (I : Finset (Fin d))
    (j : Fin d) (hj : j∈I) (a b : Fin d) (hab : a≠b) :
    ∃ T : ℝ → ℝ,AnalyticAt ℝ T 0 ∧ T 0=2*quarticA d-quarticB d ∧
      ((fun t => T t-(2*quarticA d-quarticB d))
        =O[𝓝 (0:ℝ)] (fun t => ‖t‖^2)) ∧
      (∀ᶠ t in 𝓝 (0:ℝ),0<t → ∀ (ha : a∈I) (hb : b∈I) (v : I → ℝ),
        activeHessian hd I (SubsetDiagonal.parameter hd I j hj t) (realLine I (t^2)) v ⟨a,ha⟩-
          activeHessian hd I (SubsetDiagonal.parameter hd I j hj t) (realLine I (t^2)) v ⟨b,hb⟩=
        T t*(v ⟨a,ha⟩-v ⟨b,hb⟩)) := by
  obtain ⟨H,hH,hH0,he,_⟩ := exists_transverse_branch_quotient hd I j hj a b hab
  let μ := SubsetDiagonal.parameter hd I j hj
  let T : ℝ → ℝ := fun t => -H (branchInput hd I j hj t)/μ t
  have hμ : AnalyticAt ℝ μ 0 := AnalyticPitchfork.parameter_analytic _
  have hμ0 : μ 0=1 := AnalyticPitchfork.parameter_base _
  have hcomp : AnalyticAt ℝ (fun t => H (branchInput hd I j hj t)) 0 := by
    have ho : AnalyticAt ℝ H (branchInput hd I j hj 0) := by
      simpa only [branchInput_base] using hH
    exact ho.comp (f := branchInput hd I j hj) (branchInput_analytic hd I j hj)
  have hT : AnalyticAt ℝ T 0 := hcomp.neg.div hμ (by rw [hμ0]; norm_num)
  have hT0 : T 0=2*quarticA d-quarticB d := by
    simp only [T,branchInput_base,hH0,hμ0,div_one]
    ring
  have heven : ∀ᶠ t in 𝓝 (0:ℝ),T (-t)=T t := by
    have hn := squared_difference_factor_negation hd a b hab hH (he.mono (fun _ h => h.2))
    filter_upwards [branchInput_neg hd I j hj,(branchInput_tendsto hd I j hj).eventually hn,
      AnalyticPitchfork.parameter_even (SubsetDiagonal.pitchforkData hd I j hj)] with t hp hn hμ
    dsimp only [T,μ,SubsetDiagonal.parameter]
    rw [hp,hn,hμ]
  refine ⟨T,hT,hT0,?_,?_⟩
  · simpa only [hT0] using analytic_even_quadratic_remainder hT heven
  · by_cases ha : a∈I
    · by_cases hb : b∈I
      · filter_upwards [(squaredBranchInput_tendsto hd I j hj).eventually
          (hessian_row_difference hd I a b ha hb hH (he.mono (fun _ h => h.2)))]
          with t ht hpos ha' hb' v
        have hp : ∀ k∈I,0<(realLine I (t^2)) k := fun k hk => by
          simpa only [realLine_apply,if_pos hk] using sq_pos_of_pos hpos
        have heq : (realLine I (t^2)) a=(realLine I (t^2)) b := by simp [ha,hb]
        have hh := ht hp heq (activeExtend I v)
        simpa only [squaredBranchInput,activeHessian_apply,activeExtend_apply,dif_pos ha',dif_pos hb',
          sqrtLift_realLine_square I hpos.le,T,μ,branchInput,neg_div] using hh
      · exact Filter.Eventually.of_forall (fun _ _ _ hb' _ => False.elim (hb hb'))
    · exact Filter.Eventually.of_forall (fun _ _ ha' _ _ => False.elim (ha ha'))

#print axioms exists_active_transverse_coefficient
end BecknerOnofri.HighDim.LocalEleven.SquaredReducedEnergy
