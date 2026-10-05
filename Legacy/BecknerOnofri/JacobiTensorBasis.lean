import Legacy.BecknerOnofri.JacobiNeumann
import Mathlib.MeasureTheory.Integral.Pi

/-! Concrete finite products of the normalized Jacobi functions and their spectrum. -/
noncomputable section
open Set MeasureTheory Polynomial Filter
open scoped ContDiff Topology BigOperators
namespace Legacy.BecknerOnofri.JacobiTensor
open JacobiEigenfunctions

abbrev Space (d : ℕ) := Fin d → ℝ
abbrev Index (d : ℕ) := Fin d → ℕ

def measure (d : ℕ) : Measure (Space d) := Measure.pi (fun _ => intervalMeasure)
abbrev TensorL2 (d : ℕ) := Lp ℝ 2 (measure d)

instance (d : ℕ) : IsFiniteMeasure (measure d) := by unfold measure; infer_instance

def tensorFunction {d : ℕ} (a n : Index d) (x : Space d) : ℝ :=
  ∏ i, normalizedFunction (a i) (n i) (x i)

def tensorEigenvalue {d : ℕ} (a n : Index d) : ℝ :=
  ∑ i, eigenvalue (a i) (n i)

def spectralBottom {d : ℕ} (a : Index d) : ℝ := ∑ i, (a i : ℝ)^2

theorem normalizedFunction_bounded (m n : ℕ) :
    ∃ C : ℝ, ∀ t, ‖normalizedFunction m n t‖ ≤ C := by
  refine ⟨|(Real.sqrt (normSquared m n))⁻¹| * ((n+m : ℕ) : ℝ)^(2*m), fun t => ?_⟩
  rw [normalizedFunction, norm_mul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (eigenfunction_norm_bound m n t) (abs_nonneg _)

theorem tensorFunction_continuous {d : ℕ} (a n : Index d) : Continuous (tensorFunction a n) := by
  unfold tensorFunction
  exact continuous_finsetProd _ (fun i _ => (normalizedFunction_contDiff (a i) (n i)).continuous.comp
    (continuous_apply i))

theorem tensorFunction_bounded {d : ℕ} (a n : Index d) :
    ∃ C : ℝ, ∀ x, ‖tensorFunction a n x‖ ≤ C := by
  choose C hC using fun i => normalizedFunction_bounded (a i) (n i)
  refine ⟨∏ i, C i, fun x => ?_⟩
  rw [tensorFunction, norm_prod]
  exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => hC i (x i))

theorem tensorFunction_memLp {d : ℕ} (a n : Index d) :
    MemLp (tensorFunction a n) 2 (measure d) := by
  obtain ⟨C, hC⟩ := tensorFunction_bounded a n
  exact MemLp.of_bound (tensorFunction_continuous a n).aestronglyMeasurable C (ae_of_all _ hC)

def tensorVector {d : ℕ} (a n : Index d) : TensorL2 d :=
  (tensorFunction_memLp a n).toLp (tensorFunction a n)

theorem tensorVector_ae_eq {d : ℕ} (a n : Index d) :
    tensorVector a n =ᵐ[measure d] tensorFunction a n :=
  (tensorFunction_memLp a n).coeFn_toLp

theorem normalized_integral (m n l : ℕ) :
    (∫ t, normalizedFunction m n t * normalizedFunction m l t ∂intervalMeasure) =
      if n = l then 1 else 0 := by
  rw [← orthonormal_iff_ite.mp (normalizedVector_orthonormal_all m) n l, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [normalizedVector_ae_eq m n, normalizedVector_ae_eq m l] with t hn hl
  simp only [hn, hl, RCLike.inner_apply, conj_trivial]
  ring

theorem tensorVector_inner {d : ℕ} (a n l : Index d) :
    @inner ℝ (TensorL2 d) _ (tensorVector a n) (tensorVector a l) =
      ∫ x, tensorFunction a n x * tensorFunction a l x ∂measure d := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [tensorVector_ae_eq a n, tensorVector_ae_eq a l] with x hn hl
  simp only [hn, hl, RCLike.inner_apply, conj_trivial]
  ring

theorem tensorVector_orthonormal {d : ℕ} (a : Index d) :
    Orthonormal ℝ (tensorVector a) := by
  rw [orthonormal_iff_ite]
  intro n l
  rw [tensorVector_inner]
  simp only [tensorFunction, ← Finset.prod_mul_distrib, measure]
  have hi := integral_fintype_prod_eq_prod (μ := fun _ : Fin d => intervalMeasure)
    (fun i t => normalizedFunction (a i) (n i) t * normalizedFunction (a i) (l i) t)
  rw [hi]
  simp only [normalized_integral]
  split_ifs with h
  · subst l
    simp
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

theorem tensorEigenvalue_nonneg {d : ℕ} (a n : Index d) : 0 ≤ tensorEigenvalue a n :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem spectralBottom_le {d : ℕ} (a n : Index d) : spectralBottom a ≤ tensorEigenvalue a n := by
  apply Finset.sum_le_sum
  intro i _
  dsimp [eigenvalue]
  have hn : (0 : ℝ) ≤ (n i : ℝ) := by positivity
  have ha : (0 : ℝ) ≤ (a i : ℝ) := by positivity
  push_cast
  nlinarith

theorem spectralBottom_pos {d : ℕ} (a : Index d) (ha : ∃ i, 0 < a i) :
    0 < spectralBottom a := by
  obtain ⟨i, hi⟩ := ha
  have hp : (0 : ℝ) < (a i : ℝ)^2 := sq_pos_of_pos (by exact_mod_cast hi)
  exact hp.trans_le (Finset.single_le_sum (fun j _ => sq_nonneg (a j : ℝ)) (Finset.mem_univ i))

theorem tensorEigenvalue_pos {d : ℕ} (a : Index d) (ha : ∃ i, 0 < a i) (n : Index d) :
    0 < tensorEigenvalue a n := (spectralBottom_pos a ha).trans_le (spectralBottom_le a n)

theorem coordinate_le_eigenvalue {d : ℕ} (a n : Index d) (i : Fin d) :
    (n i : ℝ) ≤ tensorEigenvalue a n := by
  have hs : ((n i + a i : ℕ) : ℝ)^2 ≤ tensorEigenvalue a n :=
    Finset.single_le_sum (fun j _ => sq_nonneg (((n j + a j : ℕ) : ℝ))) (Finset.mem_univ i)
  have hnn : (n i : ℝ) ≤ (n i : ℝ)^2 := by
    simpa only [pow_two] using (show (n i : ℝ) ≤ (n i : ℝ)*(n i : ℝ) by
      exact_mod_cast (Nat.le_mul_self (n i)))
  have hn : (0 : ℝ) ≤ (n i : ℝ) := by positivity
  have ha : (0 : ℝ) ≤ (a i : ℝ) := by positivity
  push_cast at hs
  nlinarith

theorem finite_sublevel {d : ℕ} (a : Index d) (R : ℝ) :
    Set.Finite {n : Index d | tensorEigenvalue a n ≤ R} := by
  let f : {n : Index d // tensorEigenvalue a n ≤ R} → (Fin d → Fin (Nat.ceil R + 1)) :=
    fun n i => ⟨n.1 i, by
      have h : (n.1 i : ℝ) ≤ (Nat.ceil R : ℝ) :=
        (coordinate_le_eigenvalue a n.1 i).trans (n.2.trans (Nat.le_ceil R))
      exact Nat.lt_succ_of_le (by exact_mod_cast h)⟩
  have hf : Function.Injective f := by
    intro n l h
    apply Subtype.ext
    funext i
    exact congrArg Fin.val (congrFun h i)
  exact Set.finite_coe_iff.mp (Finite.of_injective f hf)

#print axioms tensorVector_orthonormal
#print axioms finite_sublevel
end Legacy.BecknerOnofri.JacobiTensor
