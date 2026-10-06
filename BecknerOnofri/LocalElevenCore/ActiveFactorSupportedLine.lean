module

public import BecknerOnofri.LocalElevenCore.ActiveTransverseBranch
public import BecknerOnofri.AnalyticPitchforkRadial

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology
namespace BecknerOnofri.HighDim.LocalEleven.ActiveAmplitudeFactor
open AmplitudeLinearization RescaledReducedEquation

def realLineEmbedding {d : ℕ} (I : Finset (Fin d)) : ℝ × ℝ →L[ℝ] Input d :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).prod
    ((realLine I).comp (ContinuousLinearMap.snd ℝ ℝ ℝ))

@[simp] theorem realLineEmbedding_apply {d : ℕ} (I : Finset (Fin d)) (x : ℝ × ℝ) :
    realLineEmbedding I x=(x.1,realLine I x.2) := rfl

@[simp] theorem realLineEmbedding_base {d : ℕ} (I : Finset (Fin d)) :
    realLineEmbedding I (1,0)=(1,0) := by simp

theorem realLineEmbedding_tendsto {d : ℕ} (I : Finset (Fin d)) :
    Tendsto (realLineEmbedding I) (𝓝 (1,0)) (𝓝 (1,0)) := by
  simpa only [realLineEmbedding_base] using (realLineEmbedding I).continuous.tendsto (1,0)

@[simp] theorem realCoordinates_realLine {d : ℕ} (I : Finset (Fin d)) (t : ℝ) :
    realCoordinates d (realLine I t)=SubsetDiagonal.line I t := by
  funext i
  simp only [realCoordinates_apply,realLine_apply,SubsetDiagonal.line_apply]
  split_ifs <;> simp

@[simp] theorem scalar_realLine {d : ℕ} (hd : 11≤d) (I : Finset (Fin d))
    (j : Fin d) (x : ℝ × ℝ) :
    scalar hd j (realLineEmbedding I x)=SubsetDiagonal.residual hd I j x := by
  simp only [scalar,realEmbedding_apply,realLineEmbedding_apply,realCoordinates_realLine,
    SubsetDiagonal.residual,SubsetDiagonal.embedding_apply]

/-- The coordinate factor and the scalar pitchfork quotient are the same
analytic germ on each supported real diagonal. -/
theorem factor_line_eq_quotient {d : ℕ} (hd : 11≤d) (I : Finset (Fin d))
    (j : Fin d) (hj : j∈I) :
    ∀ᶠ x : ℝ × ℝ in 𝓝 (1,0),
      factor hd j (realLineEmbedding I x)=
        AnalyticPitchfork.quotient (SubsetDiagonal.pitchforkData hd I j hj) x := by
  have ha : AnalyticAt ℝ (fun x => factor hd j (realLineEmbedding I x)) (1,0) := by
    have ho : AnalyticAt ℝ (factor hd j) (realLineEmbedding I (1,0)) := by
      simpa only [realLineEmbedding_base] using factor_analytic hd j
    exact ho.comp (f := realLineEmbedding I) ((realLineEmbedding I).analyticAt _)
  apply AnalyticParameterDivision.linear_factor_unique (ContinuousLinearMap.snd ℝ ℝ ℝ)
    (e := (0,1)) rfl rfl ha (AnalyticPitchfork.quotient_analytic _)
  filter_upwards [(realLineEmbedding_tendsto I).eventually (scalar_eq_coordinate_mul_factor hd j),
    AnalyticPitchfork.residual_eq_mul_quotient (SubsetDiagonal.pitchforkData hd I j hj)]
      with x hf hq
  rw [scalar_realLine] at hf
  simp only [realLineEmbedding_apply,realLine_apply,if_pos hj] at hf
  exact hf.symm.trans hq

theorem factor_axis {d : ℕ} (hd : 11≤d) (j : Fin d) :
    ∀ᶠ μ in 𝓝 (1:ℝ),factor hd j (μ,0)=1-μ := by
  have ht : Tendsto (fun μ : ℝ => (μ,(0:ℝ))) (𝓝 1) (𝓝 (1,0)) :=
    (continuous_id.prodMk continuous_const).continuousAt
  filter_upwards [ht.eventually (factor_line_eq_quotient hd {j} j (by simp)),
    AnalyticPitchfork.quotient_axis (SubsetDiagonal.pitchforkData hd {j} j (by simp))]
    with μ he ha
  simpa only [realLineEmbedding_apply,map_zero] using he.trans ha

theorem factor_branch_zero {d : ℕ} (hd : 11≤d) (I : Finset (Fin d))
    (j : Fin d) (hj : j∈I) :
    ∀ᶠ t in 𝓝 (0:ℝ),factor hd j (branchInput hd I j hj t)=0 := by
  filter_upwards [(AnalyticPitchfork.parameter_pair_tendsto
    (SubsetDiagonal.pitchforkData hd I j hj)).eventually (factor_line_eq_quotient hd I j hj),
    AnalyticPitchfork.parameter_solves (SubsetDiagonal.pitchforkData hd I j hj)] with t he hs
  exact he.trans hs

/-- Differentiate the identified germs, preserving their genuine coordinate
derivatives rather than a formal Taylor expression. -/
theorem factor_line_amplitudePartial {d : ℕ} (hd : 11≤d) (I : Finset (Fin d))
    (j : Fin d) (hj : j∈I) :
    ∀ᶠ x : ℝ × ℝ in 𝓝 (1,0),
      fderiv ℝ (factor hd j) (realLineEmbedding I x) (0,realLine I 1)=
        AnalyticPitchfork.amplitudePartial (SubsetDiagonal.pitchforkData hd I j hj) x := by
  filter_upwards [(factor_line_eq_quotient hd I j hj).eventually_nhds,
    (realLineEmbedding_tendsto I).eventually (factor_analytic hd j).eventually_analyticAt,
    (AnalyticPitchfork.quotient_analytic (SubsetDiagonal.pitchforkData hd I j hj)).eventually_analyticAt]
    with x he hf hq
  have hc := (hf.differentiableAt.hasFDerivAt.comp x (realLineEmbedding I).hasFDerivAt).congr_of_eventuallyEq
    (he.mono (fun _ h => h.symm))
  exact congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L (0,1))
    (hc.unique hq.differentiableAt.hasFDerivAt)

#print axioms factor_axis
#print axioms factor_branch_zero
#print axioms factor_line_amplitudePartial
end BecknerOnofri.HighDim.LocalEleven.ActiveAmplitudeFactor
