module

public import Legacy.BecknerOnofri.ChebyshevProfileDefs
public import Legacy.BecknerOnofri.ClosedConvexSmoothSeries
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

@[expose] public section

/-! Actual tensor-Chebyshev derivative bounds and smoothness of the profile on
the entire closed cube. No analytic neighborhood extension is asserted. -/

open scoped BigOperators ContDiff

namespace Legacy.BecknerOnofri.ChebyshevProfile

open Legacy.TorusEndpoint TorusSobolev RadialWiener

set_option maxHeartbeats 800000

noncomputable def coordinate {d : ℕ} (k : Frequency d) (i : Fin d) (z : Space d) : ℝ :=
  (Polynomial.Chebyshev.T ℝ (Int.natAbs (k i) : ℤ)).eval (z i)

theorem coordinate_contDiff {d : ℕ} (k : Frequency d) (i : Fin d) :
    ContDiff ℝ ∞ (coordinate k i) :=
  (JacobiAngular.polynomial_contDiff _).comp
    (ContinuousLinearMap.proj i : Space d →L[ℝ] ℝ).contDiff

theorem tensor_contDiff {d : ℕ} (k : Frequency d) : ContDiff ℝ ∞ (tensor k) :=
  contDiff_prod (fun i _ => coordinate_contDiff k i)

theorem projection_norm_le {d : ℕ} (i : Fin d) :
    ‖(ContinuousLinearMap.proj i : Space d →L[ℝ] ℝ)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa using norm_le_pi_norm x i

theorem coordinate_derivative_bound {d : ℕ} (k : Frequency d) (i : Fin d) (m : ℕ)
    {z : Space d} (hz : z ∈ closedCube d) :
    ‖iteratedFDeriv ℝ m (coordinate k i) z‖ ≤ radialWeight (2*m) k := by
  let p := Polynomial.Chebyshev.T ℝ (Int.natAbs (k i) : ℤ)
  have hp : ContDiff ℝ (m : ℕ∞ω) (fun x => p.eval x) :=
    (JacobiAngular.polynomial_contDiff p).of_le (by exact_mod_cast (le_top : (m:ℕ∞) ≤ ⊤))
  change ‖iteratedFDeriv ℝ m ((fun x => p.eval x) ∘
    (ContinuousLinearMap.proj i : Space d →L[ℝ] ℝ)) z‖ ≤ _
  rw [(ContinuousLinearMap.proj i : Space d →L[ℝ] ℝ).iteratedFDeriv_comp_right hp z le_rfl]
  have hb : ‖iteratedFDeriv ℝ m (fun x => p.eval x) (z i)‖ ≤ (Int.natAbs (k i) : ℝ)^(2*m) := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate, Real.norm_eq_abs]
    exact ChebyshevDerivativeBound.actual_derivative_bound _ _ ((mem_closedCube.mp hz) i)
  calc
    _ ≤ ‖iteratedFDeriv ℝ m (fun x => p.eval x) (z i)‖ *
        ∏ _ : Fin m, ‖(ContinuousLinearMap.proj i : Space d →L[ℝ] ℝ)‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ (Int.natAbs (k i) : ℝ)^(2*m) * 1 := by
      apply mul_le_mul hb _ (Finset.prod_nonneg (fun _ _ => norm_nonneg _)) (by positivity)
      simpa using pow_le_pow_left₀ (norm_nonneg _) (projection_norm_le i) m
    _ ≤ radialWeight (2*m) k := by
      rw [mul_one]
      apply pow_le_pow_left₀ (by positivity)
      have hr := coordinate_abs_le_radius k i
      have he : (Int.natAbs (k i) : ℝ) = |(k i : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
      rw [he]
      linarith

noncomputable def derivativeConstant (d m : ℕ) : ℝ :=
  ∑ p ∈ (Finset.univ : Finset (Fin d)).sym m, ((p : Multiset (Fin d)).countPerms : ℝ)

theorem derivativeConstant_nonneg (d m : ℕ) : 0 ≤ derivativeConstant d m := by
  unfold derivativeConstant
  positivity

theorem tensor_derivative_bound {d : ℕ} (k : Frequency d) (m : ℕ)
    {z : Space d} (hz : z ∈ closedCube d) :
    ‖iteratedFDeriv ℝ m (tensor k) z‖ ≤ derivativeConstant d m * radialWeight (2*m*d) k := by
  classical
  have hp := norm_iteratedFDeriv_prod_le
    (fun (i : Fin d) (_ : i ∈ (Finset.univ : Finset (Fin d))) =>
      (coordinate_contDiff k i).of_le (by exact_mod_cast (le_top : (m:ℕ∞) ≤ ⊤))) (x := z) (n := m) le_rfl
  apply hp.trans
  rw [derivativeConstant, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro p _
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    _ ≤ ∏ _ : Fin d, radialWeight (2*m) k := by
      apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      intro i _
      apply (coordinate_derivative_bound k i ((p : Multiset (Fin d)).count i) hz).trans
      apply pow_le_pow_right₀ (by linarith [frequencyRadius_nonneg k])
      apply Nat.mul_le_mul_left 2
      simpa only [Sym.card_coe] using Multiset.count_le_card i (p : Multiset (Fin d))
    _ = radialWeight (2*m*d) k := by
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, radialWeight, ← pow_mul]

theorem profile_term_derivative_bound {d : ℕ} (a : Frequency d → ℂ) (k : Frequency d)
    (m : ℕ) {z : Space d} (hz : z ∈ closedCube d) :
    ‖iteratedFDeriv ℝ m (fun y => (a k).re * tensor k y) z‖ ≤
      derivativeConstant d m * (radialWeight (2*m*d) k * ‖a k‖) := by
  have hc : ContDiffAt ℝ (m : ℕ∞ω) (tensor k) z :=
    ((tensor_contDiff k).of_le (by exact_mod_cast (le_top : (m:ℕ∞) ≤ ⊤))).contDiffAt
  have hh := iteratedFDeriv_const_smul_apply' (a := (a k).re) hc
  simp only [smul_eq_mul] at hh
  rw [hh, norm_smul]
  calc
    _ ≤ ‖a k‖ * (derivativeConstant d m * radialWeight (2*m*d) k) := by
      exact mul_le_mul (by simpa only [Real.norm_eq_abs] using Complex.abs_re_le_norm (a k)) (tensor_derivative_bound k m hz)
        (norm_nonneg _) (norm_nonneg _)
    _ = _ := by ring

theorem profile_contDiffOn {d : ℕ} (a : Frequency d → ℂ)
    (ha : ∀ m : ℕ, RadialSummable a m) :
    ContDiffOn ℝ ∞ (profile a) (closedCube d) := by
  rw [← closure_openCube]
  apply ClosedConvexSmoothSeries.contDiffOn_tsum_closure (openCube_isOpen d) (openCube_convex d)
    (f := fun k z => (a k).re * tensor k z)
    (u := fun m k => derivativeConstant d m * (radialWeight (2*m*d) k * ‖a k‖))
  · intro k
    exact contDiff_const.mul (tensor_contDiff k)
  · intro m
    exact (ha (2*m*d)).mul_left _
  · intro m k z hz
    exact profile_term_derivative_bound a k m (by rwa [closure_openCube] at hz)

#print axioms tensor_derivative_bound
#print axioms profile_contDiffOn

end Legacy.BecknerOnofri.ChebyshevProfile
