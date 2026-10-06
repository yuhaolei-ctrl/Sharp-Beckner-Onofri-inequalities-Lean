module

public import BecknerOnofri.LocalElevenCore.ActiveFactorNegation
public import BecknerOnofri.LocalElevenCore.SubsetStationaryBranch
public import BecknerOnofri.AnalyticEvenQuadratic

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter Asymptotics
open scoped Topology
namespace BecknerOnofri.HighDim.LocalEleven.ActiveAmplitudeFactor
open AmplitudeLinearization

def realLine {d : ℕ} (I : Finset (Fin d)) : ℝ →L[ℝ] Amplitudes d :=
  ContinuousLinearMap.pi (fun i => if i∈I then ContinuousLinearMap.id ℝ ℝ else 0)

@[simp] theorem realLine_apply {d : ℕ} (I : Finset (Fin d)) (t : ℝ) (i : Fin d) :
    realLine I t i=if i∈I then t else 0 := by
  simp only [realLine,ContinuousLinearMap.pi_apply]
  split_ifs <;> rfl

def branchInput {d : ℕ} (hd : 11≤d) (I : Finset (Fin d)) (j : Fin d) (hj : j∈I)
    (t : ℝ) : Input d := (SubsetDiagonal.parameter hd I j hj t,realLine I t)

@[simp] theorem branchInput_base {d : ℕ} (hd : 11≤d) (I : Finset (Fin d))
    (j : Fin d) (hj : j∈I) : branchInput hd I j hj 0=(1,0) := by
  simp [branchInput,SubsetDiagonal.parameter,AnalyticPitchfork.parameter_base]

theorem branchInput_analytic {d : ℕ} (hd : 11≤d) (I : Finset (Fin d))
    (j : Fin d) (hj : j∈I) : AnalyticAt ℝ (branchInput hd I j hj) 0 :=
  (AnalyticPitchfork.parameter_analytic (SubsetDiagonal.pitchforkData hd I j hj)).prod
    ((realLine I).analyticAt 0)

theorem branchInput_tendsto {d : ℕ} (hd : 11≤d) (I : Finset (Fin d))
    (j : Fin d) (hj : j∈I) :
    Tendsto (branchInput hd I j hj) (𝓝 0) (𝓝 (1,0)) := by
  simpa only [branchInput_base] using (branchInput_analytic hd I j hj).continuousAt.tendsto

theorem branchInput_neg {d : ℕ} (hd : 11≤d) (I : Finset (Fin d))
    (j : Fin d) (hj : j∈I) : ∀ᶠ t in 𝓝 (0:ℝ),
    branchInput hd I j hj (-t)=negateInput d (branchInput hd I j hj t) := by
  filter_upwards [AnalyticPitchfork.parameter_even (SubsetDiagonal.pitchforkData hd I j hj)] with t ht
  apply Prod.ext ht
  exact map_neg (realLine I) t

/-- The genuine analytic divided difference along every supported Euler
branch has the precise transverse leading coefficient and a quadratic
amplitude remainder. Identification with the squared-coordinate Hessian is
performed separately. -/
theorem exists_transverse_branch_quotient {d : ℕ} (hd : 11≤d) (I : Finset (Fin d))
    (j : Fin d) (hj : j∈I) (a b : Fin d) (hab : a≠b) :
    ∃ H : Input d → ℝ, AnalyticAt ℝ H (1,0) ∧ H (1,0)=quarticB d-2*quarticA d ∧
      (∀ᶠ x : Input d in 𝓝 (1,0),0<H x ∧
        factor hd a x-factor hd b x=(x.2 a^2-x.2 b^2)*H x) ∧
      (fun t => H (branchInput hd I j hj t)-(quarticB d-2*quarticA d))
        =O[𝓝 (0:ℝ)] (fun t => ‖t‖^2) := by
  obtain ⟨H,hH,hH0,he⟩ := exists_nonzero_squared_difference_factor hd a b hab
  refine ⟨H,hH,hH0,he,?_⟩
  have hn := squared_difference_factor_negation hd a b hab hH (he.mono (fun _ h => h.2))
  have ha : AnalyticAt ℝ (fun t => H (branchInput hd I j hj t)) 0 := by
    have ho : AnalyticAt ℝ H (branchInput hd I j hj 0) := by simpa only [branchInput_base] using hH
    exact ho.comp (f := branchInput hd I j hj) (branchInput_analytic hd I j hj)
  have hev : ∀ᶠ t in 𝓝 (0:ℝ), H (branchInput hd I j hj (-t))=H (branchInput hd I j hj t) := by
    filter_upwards [branchInput_neg hd I j hj,(branchInput_tendsto hd I j hj).eventually hn]
      with t ht hnt
    rw [ht,hnt]
  simpa only [branchInput_base,hH0] using analytic_even_quadratic_remainder ha hev

#print axioms exists_transverse_branch_quotient
end BecknerOnofri.HighDim.LocalEleven.ActiveAmplitudeFactor
