module

public import BecknerOnofri.V2.FiniteState.OriginEntropy
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

@[expose] public section

/-!
# Regularity of the explicit family at the origin

`p_j`, `log (p_j/b_j)`, `g_j`, `σ_x²`, `e_j`, `𝒱` and `f` are `C^n` at `t = 0` for every
`n : WithTop ℕ∞` (including `n = ω`, i.e. real analytic), since every denominator is nonzero at
`0` (`D(0) = 31`, `∏ (1 + kω(0)) = 1`, `p_j(0) = b_j > 0`, `σ_x²(0) = 1/12`).
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter Topology
open scoped BigOperators
namespace BecknerOnofri.V2.FiniteState
open BecknerOnofri.HighDim.Spin

theorem contDiffAt_prod_range {n : WithTop ℕ∞} {x : ℝ} (m : ℕ) (f : ℕ → ℝ → ℝ)
    (hf : ∀ k, ContDiffAt ℝ n (f k) x) :
    ContDiffAt ℝ n (fun t => ∏ k ∈ Finset.range m, f k t) x := by
  induction m with
  | zero => simpa using contDiffAt_const
  | succ m ih =>
    simp_rw [Finset.prod_range_succ]
    exact ih.mul (hf m)

theorem famBias_contDiff (n : WithTop ℕ∞) : ContDiff ℝ n famBias := by
  unfold famBias famL; fun_prop

theorem famLam_contDiffAt (n : WithTop ℕ∞) (x : ℝ) : ContDiffAt ℝ n famLam x := by
  unfold famLam
  have hL : ContDiff ℝ n famL := by unfold famL; fun_prop
  apply ContDiffAt.div hL.contDiffAt (contDiff_const.add hL).contDiffAt
  have := famL_nonneg_all x
  linarith

theorem famOmega_contDiffAt (n : WithTop ℕ∞) : ContDiffAt ℝ n famOmega 0 := by
  unfold famOmega
  apply ContDiffAt.div
  · fun_prop
  · unfold famP; fun_prop
  · simp [famP]

theorem famNu_contDiffAt (n : WithTop ℕ∞) (j : Count) :
    ContDiffAt ℝ n (fun t => famNu t j) 0 := by
  have hb := (famBias_contDiff n).contDiffAt (x := 0)
  have hω := famOmega_contDiffAt n
  unfold famNu
  apply ContDiffAt.div
  · refine ContDiffAt.mul (ContDiffAt.mul contDiffAt_const ?_) ?_
    · exact contDiffAt_prod_range _ _ (fun k => by fun_prop)
    · exact contDiffAt_prod_range _ _ (fun k => by fun_prop)
  · exact contDiffAt_prod_range _ _ (fun k => by fun_prop)
  · apply (Finset.prod_pos (fun k _ => ?_)).ne'
    simp [famOmega_zero]

theorem famLaw_contDiffAt (n : WithTop ℕ∞) (j : Count) :
    ContDiffAt ℝ n (fun t => famLaw t j) 0 := by
  have := famLam_contDiffAt n 0
  unfold famLaw
  exact (contDiffAt_const.sub this).mul (famNu_contDiffAt n j) |>.add (this.mul contDiffAt_const)

theorem famRatio_zero (j : Count) : famRatio j 0 = 1 := by
  unfold famRatio; rw [famLaw_zero]; exact div_self (reference_pos j).ne'

theorem famLogRatio_contDiffAt (n : WithTop ℕ∞) (j : Count) :
    ContDiffAt ℝ n (fun t => Real.log (famLaw t j / reference j)) 0 := by
  have h := (famLaw_contDiffAt n j).div_const (reference j)
  refine h.log ?_
  have := famRatio_zero j
  unfold famRatio at this
  rw [this]; norm_num

theorem famGradient_contDiffAt (n : WithTop ℕ∞) (j : Count) :
    ContDiffAt ℝ n (fun t => gradient (famLaw t) j) 0 := by
  unfold gradient
  refine ((contDiffAt_const.mul (famLogRatio_contDiffAt n j)).add contDiffAt_const).sub
    (contDiffAt_const.mul ?_)
  exact ContDiffAt.sum (fun k _ => contDiffAt_const.mul (famLaw_contDiffAt n k))

theorem famSpinVar_contDiffAt (n : WithTop ℕ∞) : ContDiffAt ℝ n famSpinVar 0 := by
  unfold famSpinVar regVar
  exact ContDiffAt.sum (fun k _ => (famLaw_contDiffAt n k).mul
    ((contDiffAt_const.sub contDiffAt_id).pow 2))

theorem famResid_contDiffAt (n : WithTop ℕ∞) (j : Count) :
    ContDiffAt ℝ n (fun t => famResid t j) 0 := by
  have hv := famSpinVar_contDiffAt n
  have hv0 : famSpinVar 0 ≠ 0 := by rw [famSpinVar_zero]; norm_num
  unfold famResid gradResid regResid regMean regSlope
  refine (famGradient_contDiffAt n j).sub ?_ |>.sub ?_
  · exact ContDiffAt.sum (fun k _ => (famLaw_contDiffAt n k).mul (famGradient_contDiffAt n k))
  · refine ContDiffAt.mul (ContDiffAt.div ?_ hv hv0) (contDiffAt_const.sub contDiffAt_id)
    exact ContDiffAt.sum (fun k _ =>
      ((famLaw_contDiffAt n k).mul (contDiffAt_const.sub contDiffAt_id)).mul
        (famGradient_contDiffAt n k))

theorem famResidVar_contDiffAt (n : WithTop ℕ∞) : ContDiffAt ℝ n famResidVar 0 := by
  unfold famResidVar
  exact ContDiffAt.sum (fun j _ => (famLaw_contDiffAt n j).mul ((famResid_contDiffAt n j).pow 2))

theorem psiV2_contDiffAt (n : WithTop ℕ∞) : ContDiffAt ℝ n psiV2 0 := by
  unfold psiV2
  apply ContDiffAt.div
  · fun_prop
  · fun_prop
  · norm_num

theorem famF_contDiffAt (n : WithTop ℕ∞) : ContDiffAt ℝ n famF 0 := by
  unfold famF functional relativeEntropy quadratic
  refine ContDiffAt.add (ContDiffAt.sub ?_ ?_) (contDiffAt_const.mul (psiV2_contDiffAt n))
  · refine contDiffAt_const.mul (ContDiffAt.sum (fun j _ => (famLaw_contDiffAt n j).mul
      (famLogRatio_contDiffAt n j)))
  · exact ContDiffAt.sum (fun i _ => ContDiffAt.sum (fun j _ =>
      ((famLaw_contDiffAt n i).mul contDiffAt_const).mul (famLaw_contDiffAt n j)))

end BecknerOnofri.V2.FiniteState
