import BecknerOnofri.Friedrichs.PeriodicHilbertBasis
import Mathlib.Logic.Equiv.Nat

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped ContDiff
namespace BecknerOnofri.Friedrichs.MixedSpatial
open Legacy.BecknerOnofri

 def periodicIndex (n : ℕ) : PeriodicBasis.Index := Equiv.natSumNatEquivNat.symm n

def coordinateFunction : ℕ → ℕ → ℝ → ℝ
  | 0,n => fun t => (Real.sqrt (PeriodicBasis.normSquared (periodicIndex n)))⁻¹*
      PeriodicBasis.rawFunction (periodicIndex n) t
  | m+1,n => JacobiEigenfunctions.normalizedFunction (m+1) n

lemma coordinateFunction_smooth (m n : ℕ) : ContDiff ℝ ∞ (coordinateFunction m n) := by
  cases m with
  | zero =>
    apply contDiff_const.mul
    cases periodicIndex n <;> exact periodicMode_smooth _ _
  | succ m => exact JacobiEigenfunctions.normalizedFunction_contDiff (m+1) n

lemma coordinateFunction_memLp (m n : ℕ) : MemLp (coordinateFunction m n) 2 (coordinateMeasure m) :=
  (memLp_two_iff_integrable_sq (coordinateFunction_smooth m n).continuous.aestronglyMeasurable).mpr
    (coordinate_square_integrable m (coordinateFunction_smooth m n).continuous)

def coordinateVector (m n : ℕ) : Lp ℝ 2 (coordinateMeasure m) :=
  (coordinateFunction_memLp m n).toLp (coordinateFunction m n)

lemma coordinateVector_zero (n : ℕ) :
    coordinateVector 0 n=PeriodicBasis.normalizedVector (periodicIndex n) := by
  apply Lp.ext
  filter_upwards [(coordinateFunction_memLp 0 n).coeFn_toLp,
    Lp.coeFn_smul (Real.sqrt (PeriodicBasis.normSquared (periodicIndex n)))⁻¹
      (PeriodicBasis.rawVector (periodicIndex n)),
    (PeriodicBasis.rawFunction_memLp (periodicIndex n)).coeFn_toLp] with t ht hs hr
  change PeriodicBasis.rawVector (periodicIndex n) t=PeriodicBasis.rawFunction (periodicIndex n) t at hr
  change coordinateVector 0 n t=coordinateFunction 0 n t at ht
  rw [ht]
  simpa only [PeriodicBasis.normalizedVector,coordinateFunction,Pi.smul_apply,smul_eq_mul,hr] using hs.symm

lemma coordinateVector_succ (m n : ℕ) :
    coordinateVector (m+1) n=JacobiEigenfunctions.normalizedVector (m+1) n := by
  apply Lp.ext
  exact (coordinateFunction_memLp (m+1) n).coeFn_toLp.trans
    (JacobiEigenfunctions.normalizedVector_ae_eq (m+1) n).symm

lemma coordinateVector_orthonormal (m : ℕ) : Orthonormal ℝ (coordinateVector m) := by
  cases m with
  | zero =>
    rw [orthonormal_iff_ite]
    intro n l
    rw [coordinateVector_zero,coordinateVector_zero]
    have hi : periodicIndex n=periodicIndex l ↔ n=l := Equiv.natSumNatEquivNat.symm.injective.eq_iff
    simpa only [hi] using orthonormal_iff_ite.mp
      PeriodicBasis.normalizedVector_orthonormal (periodicIndex n) (periodicIndex l)
  | succ m =>
    simpa only [funext (coordinateVector_succ m)] using
      JacobiEigenfunctions.normalizedVector_orthonormal (Nat.succ_pos m)

lemma coordinateFunction_integral (m n l : ℕ) :
    (∫ t,coordinateFunction m n t*coordinateFunction m l t ∂coordinateMeasure m)=if n=l then 1 else 0 := by
  rw [← orthonormal_iff_ite.mp (coordinateVector_orthonormal m) n l,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(coordinateFunction_memLp m n).coeFn_toLp,
    (coordinateFunction_memLp m l).coeFn_toLp] with t hn hl
  change coordinateVector m n t=coordinateFunction m n t at hn
  change coordinateVector m l t=coordinateFunction m l t at hl
  simp only [hn,hl,RCLike.inner_apply,conj_trivial]
  ring

lemma coordinateFunction_total (m : ℕ) (f : Lp ℝ 2 (coordinateMeasure m))
    (h : ∀ n,(∫ t,coordinateFunction m n t*f t ∂coordinateMeasure m)=0) : f=0 := by
  have hi (n : ℕ) : inner ℝ f (coordinateVector m n)=0 := by
    rw [L2.inner_def]
    calc
      _ = ∫ t,coordinateFunction m n t*f t ∂coordinateMeasure m := by
        apply integral_congr_ae
        filter_upwards [(coordinateFunction_memLp m n).coeFn_toLp] with t ht
        change coordinateVector m n t=coordinateFunction m n t at ht
        simp only [ht,RCLike.inner_apply,conj_trivial]
      _ = 0 := h n
  cases m with
  | zero =>
    apply PeriodicBasis.total f
    intro i
    have he := hi (Equiv.natSumNatEquivNat i)
    simpa only [coordinateVector_zero,periodicIndex,Equiv.symm_apply_apply] using he
  | succ m =>
    apply JacobiEigenfunctions.eq_zero_of_orthogonal_normalizedVector f (m+1)
    simpa only [coordinateVector_succ] using hi

#print axioms coordinateFunction_total
#print axioms coordinateVector_orthonormal
end BecknerOnofri.Friedrichs.MixedSpatial
