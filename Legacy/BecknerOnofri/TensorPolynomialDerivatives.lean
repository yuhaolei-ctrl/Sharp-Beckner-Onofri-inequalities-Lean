import Legacy.BecknerOnofri.CubeProfileMonotone
import Legacy.BecknerOnofri.NormalizedExponentialPartials

/-! Explicit tensor polynomial formulas for genuine ordered mixed partials
in the unit cube. -/
noncomputable section
namespace Legacy.BecknerOnofri.TensorPolynomialDerivatives
open Set Polynomial FiniteDifferences
open scoped BigOperators ContDiff

def unitTensor {d : ℕ} (p : Fin d → Polynomial ℝ) (y : Space d) : ℝ :=
  ∏ i, (p i).eval (2*y i-1)

def differentiate {d : ℕ} (p : Fin d → Polynomial ℝ) (i : Fin d) : Fin d → Polynomial ℝ :=
  Function.update p i (p i).derivative

def iteratePolynomials {d : ℕ} (p : Fin d → Polynomial ℝ) (is : List (Fin d)) :
    Fin d → Polynomial ℝ := fun i => derivative^[is.count i] (p i)

theorem unitTensor_contDiff {d : ℕ} (p : Fin d → Polynomial ℝ) : ContDiff ℝ ∞ (unitTensor p) := by
  apply contDiff_prod
  intro i _
  exact (JacobiAngular.polynomial_contDiff _).comp
    ((contDiff_const.mul (contDiff_apply ℝ ℝ i)).sub contDiff_const)

theorem unitTensor_slice {d : ℕ} (p : Fin d → Polynomial ℝ) (x : Space d) (i : Fin d) (s : ℝ) :
    unitTensor p (Function.update x i s) = (p i).eval (2*s-1) *
      ∏ j ∈ Finset.univ.erase i, (p j).eval (2*x j-1) := by
  classical
  rw [unitTensor, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]

theorem unitTensor_differentiate_slice {d : ℕ} (p : Fin d → Polynomial ℝ)
    (x : Space d) (i : Fin d) (s : ℝ) :
    unitTensor (differentiate p i) (Function.update x i s) = (p i).derivative.eval (2*s-1) *
      ∏ j ∈ Finset.univ.erase i, (p j).eval (2*x j-1) := by
  rw [unitTensor_slice]
  simp only [differentiate, Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]

theorem unitTensor_slice_hasDerivAt {d : ℕ} (p : Fin d → Polynomial ℝ)
    (x : Space d) (i : Fin d) (s : ℝ) :
    HasDerivAt (fun t => unitTensor p (Function.update x i t))
      (2*unitTensor (differentiate p i) (Function.update x i s)) s := by
  have ha : HasDerivAt (fun t : ℝ => 2*t-1) 2 s := by
    simpa using ((hasDerivAt_id s).const_mul 2).sub_const 1
  have hp := ((p i).hasDerivAt (2*s-1)).comp s ha
  have hh := hp.mul_const (∏ j ∈ Finset.univ.erase i, (p j).eval (2*x j-1))
  convert! hh using 1
  · funext t; exact unitTensor_slice p x i t
  · rw [unitTensor_differentiate_slice]
    ring

theorem coordinateDerivative_unitTensor {d : ℕ} (p : Fin d → Polynomial ℝ)
    (i : Fin d) {x : Space d} (hx : x ∈ closedCube d) :
    coordinateDerivative i (unitTensor p) x = 2*unitTensor (differentiate p i) x := by
  have hc := hasDerivWithinAt_coordinate_of_contDiffOn (unitTensor_contDiff p).contDiffOn i hx
  have hh := (unitTensor_slice_hasDerivAt p x i (x i)).hasDerivWithinAt (s := Icc (0 : ℝ) 1)
  rw [Function.update_eq_self] at hh
  have huniq := uniqueDiffOn_Icc_zero_one (x i) ⟨hx.1 i, hx.2 i⟩
  exact (hc.derivWithin huniq).symm.trans (hh.derivWithin huniq)

theorem iteratePolynomials_nil {d : ℕ} (p : Fin d → Polynomial ℝ) :
    iteratePolynomials p [] = p := by funext i; simp [iteratePolynomials]

theorem iteratePolynomials_snoc {d : ℕ} (p : Fin d → Polynomial ℝ)
    (is : List (Fin d)) (i : Fin d) :
    iteratePolynomials p (is ++ [i]) = differentiate (iteratePolynomials p is) i := by
  funext j
  by_cases h : j = i
  · subst j
    simp [iteratePolynomials, differentiate, Function.iterate_succ_apply']
  · simp [iteratePolynomials, differentiate, h, Ne.symm h]

theorem mixedPartial_unitTensor {d : ℕ} (p : Fin d → Polynomial ℝ)
    (is : List (Fin d)) {x : Space d} (hx : x ∈ closedCube d) :
    mixedPartial is (unitTensor p) x = 2^is.length * unitTensor (iteratePolynomials p is) x := by
  induction is using List.reverseRecOn generalizing x with
  | nil => simp [iteratePolynomials_nil]
  | append_singleton is i ih =>
    rw [mixedPartial_append_single]
    rw [MixedExponentialDerivatives.coordinateDerivative_congr i (fun y hy => ih hy) hx]
    rw [NormalizedExponentialPartials.coordinateDerivative_const_mul i _
      (unitTensor_contDiff _).contDiffOn hx, coordinateDerivative_unitTensor _ i hx,
      iteratePolynomials_snoc]
    simp only [List.length_append, List.length_singleton, pow_succ]
    ring

#print axioms mixedPartial_unitTensor
end Legacy.BecknerOnofri.TensorPolynomialDerivatives
