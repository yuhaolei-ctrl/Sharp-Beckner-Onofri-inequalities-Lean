module

public import Legacy.BecknerOnofri.JacobiDerivativeBounds
public import Legacy.BecknerOnofri.CircleHeatDerivative
public import Legacy.BecknerOnofri.ClosedConvexSmoothSeries

@[expose] public section

/-! Gaussian summability and uniform joint time-space bounds for the genuine Jacobi heat series. -/
noncomputable section
open Set Filter MeasureTheory Polynomial
open scoped BigOperators ContDiff Topology
namespace Legacy.BecknerOnofri.JacobiHeatBounds
open JacobiEigenfunctions

abbrev HeatSpace := Fin 3 → ℝ

def uniformDerivativeConstant (m k : ℕ) : ℝ := ∑ j ∈ Finset.range (k+1), derivativeConstant m j

def heatFactor (m n : ℕ) (i : Fin 3) (z : HeatSpace) : ℝ :=
  if i=0 then Real.exp (-(eigenvalue m n)*z 0) else normalizedFunction m n (z i)

def heatTerm (m n : ℕ) (z : HeatSpace) : ℝ := ∏ i : Fin 3, heatFactor m n i z

def heatKernel (m : ℕ) (t x y : ℝ) : ℝ :=
  ∑' n : ℕ, Real.exp (-t*eigenvalue m n)*normalizedFunction m n x*normalizedFunction m n y

def jointHeat (m : ℕ) (z : HeatSpace) : ℝ := ∑' n : ℕ, heatTerm m n z

def timeSlab (ε : ℝ) : Set HeatSpace := {z | ε ≤ z 0}

def productConstant (k : ℕ) : ℝ :=
  ∑ p ∈ (Finset.univ : Finset (Fin 3)).sym k, ((p : Multiset (Fin 3)).countPerms : ℝ)

def heatMajorant (m k : ℕ) (ε : ℝ) (n : ℕ) : ℝ :=
  (productConstant k*uniformDerivativeConstant m k^2)*
    (degreeBase m n^(2*k+2*derivativeDegree m k)*Real.exp (-ε*eigenvalue m n))

theorem derivativeConstant_nonneg (m k : ℕ) : 0 ≤ derivativeConstant m k := by
  unfold derivativeConstant
  positivity

theorem uniformDerivativeConstant_nonneg (m k : ℕ) : 0 ≤ uniformDerivativeConstant m k :=
  Finset.sum_nonneg (fun j _ => derivativeConstant_nonneg m j)

theorem derivativeConstant_le_uniform {m j k : ℕ} (hj : j ≤ k) :
    derivativeConstant m j ≤ uniformDerivativeConstant m k :=
  Finset.single_le_sum (fun i _ => derivativeConstant_nonneg m i) (Finset.mem_range.mpr (by omega))

theorem normalized_derivative_uniform (m n k j : ℕ) (hj : j ≤ k) (x : ℝ) :
    ‖iteratedFDeriv ℝ j (normalizedFunction m n) x‖ ≤
      uniformDerivativeConstant m k*degreeBase m n^(derivativeDegree m k) := by
  refine (normalizedFunction_derivative_bound m n j x).trans ?_
  apply mul_le_mul (derivativeConstant_le_uniform hj)
    (pow_le_pow_right₀ (degreeBase_one_le m n) (by dsimp [derivativeDegree]; omega))
    (pow_nonneg (degreeBase_pos m n).le _) (uniformDerivativeConstant_nonneg m k)

theorem shifted_polynomial_gaussian_summable {ε : ℝ} (hε : 0 < ε) (m K : ℕ) :
    Summable (fun n : ℕ => degreeBase m n^K*Real.exp (-ε*eigenvalue m n)) := by
  have hs : Summable (fun n : ℕ => ((n:ℝ)+1)^K*Real.exp (-ε*(n:ℝ)^2)) := by
    have hh := summable_sum (s := Finset.range (K+1)) (fun j _ =>
      (CircleHeat.summable_polynomial_gaussian hε j).mul_left (K.choose j:ℝ))
    apply hh.congr
    intro n
    rw [add_pow,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    simp only [one_pow,mul_one]
    ring
  have hh := (summable_nat_add_iff m).mpr hs
  simpa only [degreeBase,eigenvalue,Nat.cast_add,Nat.cast_one] using hh

theorem heatMajorant_summable {ε : ℝ} (hε : 0 < ε) (m k : ℕ) : Summable (heatMajorant m k ε) :=
  (shifted_polynomial_gaussian_summable hε m _).mul_left _

theorem projection_norm_le (i : Fin 3) : ‖(ContinuousLinearMap.proj i : HeatSpace →L[ℝ] ℝ)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  simpa using norm_le_pi_norm z i

theorem projected_derivative_le {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (i : Fin 3) (k : ℕ) (z : HeatSpace) :
    ‖iteratedFDeriv ℝ k (fun w : HeatSpace => f (w i)) z‖ ≤ ‖iteratedFDeriv ℝ k f (z i)‖ := by
  change ‖iteratedFDeriv ℝ k (f ∘ (ContinuousLinearMap.proj i : HeatSpace →L[ℝ] ℝ)) z‖ ≤ _
  rw [(ContinuousLinearMap.proj i : HeatSpace →L[ℝ] ℝ).iteratedFDeriv_comp_right hf z
    (by exact_mod_cast (le_top : (k:ℕ∞) ≤ ⊤))]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hp : (∏ _ : Fin k, ‖(ContinuousLinearMap.proj i : HeatSpace →L[ℝ] ℝ)‖) ≤ 1 := by
    simpa using pow_le_pow_left₀ (norm_nonneg _) (projection_norm_le i) k
  exact mul_le_of_le_one_right (norm_nonneg _) hp

theorem timeFactor_derivative_bound {ε : ℝ} (m n k j : ℕ) (hj : j ≤ k) {t : ℝ} (ht : ε ≤ t) :
    ‖iteratedFDeriv ℝ j (fun s : ℝ => Real.exp (-(eigenvalue m n)*s)) t‖ ≤
      degreeBase m n^(2*k)*Real.exp (-ε*eigenvalue m n) := by
  have hlambda : 0 ≤ eigenvalue m n := by unfold eigenvalue; positivity
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,iteratedDeriv_exp_const_mul]
  simp only [norm_mul,Real.norm_eq_abs,abs_pow,abs_neg,abs_of_nonneg hlambda,abs_of_pos (Real.exp_pos _)]
  have hn : ((n+m:ℕ):ℝ) ≤ degreeBase m n := by dsimp [degreeBase]; push_cast; linarith
  have hp : eigenvalue m n^j ≤ degreeBase m n^(2*k) := by
    unfold eigenvalue
    rw [← pow_mul]
    exact (pow_le_pow_left₀ (Nat.cast_nonneg (n+m) : (0:ℝ) ≤ (n+m:ℕ)) hn _).trans
      (pow_le_pow_right₀ (degreeBase_one_le m n) (by omega))
  apply mul_le_mul hp (Real.exp_le_exp.mpr (by nlinarith)) (Real.exp_nonneg _) (pow_nonneg (degreeBase_pos m n).le _)

def factorMajorant (m k : ℕ) (ε : ℝ) (n : ℕ) (i : Fin 3) : ℝ :=
  if i=0 then degreeBase m n^(2*k)*Real.exp (-ε*eigenvalue m n)
  else uniformDerivativeConstant m k*degreeBase m n^(derivativeDegree m k)

theorem heatFactor_eq_time (m n : ℕ) : heatFactor m n 0 = fun z => Real.exp (-(eigenvalue m n)*z 0) := by
  funext z
  simp [heatFactor]

theorem heatFactor_eq_space (m n : ℕ) {i : Fin 3} (hi : i ≠ 0) :
    heatFactor m n i = fun z => normalizedFunction m n (z i) := by
  funext z
  simp [heatFactor,hi]

theorem heatFactor_contDiff (m n : ℕ) (i : Fin 3) : ContDiff ℝ ∞ (heatFactor m n i) := by
  by_cases hi : i=0
  · subst i
    rw [heatFactor_eq_time]
    exact Real.contDiff_exp.comp (contDiff_const.mul (ContinuousLinearMap.proj (0:Fin 3) : HeatSpace →L[ℝ] ℝ).contDiff)
  · rw [heatFactor_eq_space m n hi]
    exact (normalizedFunction_contDiff m n).comp (ContinuousLinearMap.proj i : HeatSpace →L[ℝ] ℝ).contDiff

theorem heatFactor_derivative_bound {ε : ℝ} (m n k j : ℕ) (hj : j ≤ k) (i : Fin 3)
    {z : HeatSpace} (hz : z ∈ timeSlab ε) :
    ‖iteratedFDeriv ℝ j (heatFactor m n i) z‖ ≤ factorMajorant m k ε n i := by
  by_cases hi : i=0
  · subst i
    rw [heatFactor_eq_time]
    simp only [factorMajorant,ite_true]
    have hf : ContDiff ℝ ∞ (fun t : ℝ => Real.exp (-(eigenvalue m n)*t)) :=
      Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)
    exact (projected_derivative_le hf 0 j z).trans (timeFactor_derivative_bound m n k j hj hz)
  · rw [heatFactor_eq_space m n hi]
    simp only [factorMajorant,if_neg hi]
    exact (projected_derivative_le (normalizedFunction_contDiff m n) i j z).trans
      (normalized_derivative_uniform m n k j hj (z i))

theorem heatTerm_contDiff (m n : ℕ) : ContDiff ℝ ∞ (heatTerm m n) :=
  contDiff_prod (fun i _ => heatFactor_contDiff m n i)

theorem heatTerm_derivative_bound {ε : ℝ} (m n k : ℕ) {z : HeatSpace} (hz : z ∈ timeSlab ε) :
    ‖iteratedFDeriv ℝ k (heatTerm m n) z‖ ≤ heatMajorant m k ε n := by
  have hh := norm_iteratedFDeriv_prod_le (u := (Finset.univ : Finset (Fin 3)))
    (fun i _ => heatFactor_contDiff m n i) (x := z) (n := k)
    (by exact_mod_cast (le_top : (k:ℕ∞) ≤ ⊤))
  refine hh.trans ?_
  have hp : (∏ i : Fin 3, factorMajorant m k ε n i) =
      uniformDerivativeConstant m k^2*degreeBase m n^(2*k+2*derivativeDegree m k)*Real.exp (-ε*eigenvalue m n) := by
    rw [Fin.prod_univ_three]
    simp only [factorMajorant,ite_true,if_neg (show (1:Fin 3) ≠ 0 by decide),if_neg (show (2:Fin 3) ≠ 0 by decide)]
    rw [pow_add,pow_mul]
    ring
  calc
    _ ≤ productConstant k*∏ i : Fin 3, factorMajorant m k ε n i := by
      rw [productConstant,Finset.sum_mul]
      apply Finset.sum_le_sum
      intro p _
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      intro i _
      apply heatFactor_derivative_bound m n k ((p:Multiset (Fin 3)).count i) _ i hz
      simpa only [Sym.card_coe] using Multiset.count_le_card i (p:Multiset (Fin 3))
    _ = _ := by rw [hp]; dsimp [heatMajorant]; ring

#print axioms heatTerm_derivative_bound
end Legacy.BecknerOnofri.JacobiHeatBounds
