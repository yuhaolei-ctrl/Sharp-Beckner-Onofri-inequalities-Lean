import Legacy.BecknerOnofri.PositiveKernelRayleigh
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-! Compact self-adjoint spectral extrema and the actual L2 absolute-value replacement.
Existence of an extremal eigenvector is derived from the compact spectral theorem.
-/
noncomputable section
open MeasureTheory Module
open scoped Topology
namespace Legacy.BecknerOnofri.PositiveKernelRayleigh

section Hilbert
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- A nonzero compact self-adjoint operator has an eigenvalue whose absolute value is its norm. -/
theorem exists_norm_eigenvector (T : E →L[ℝ] E) (hc : IsCompactOperator T)
    (hs : T.IsSymmetric) (hne : T ≠ 0) :
    ∃ c : ℝ, ∃ v : E, v ≠ 0 ∧ T v = c • v ∧ |c| = ‖T‖ := by
  have hsome : ∃ c : ℝ, Module.End.HasEigenvalue (T : Module.End ℝ E) c ∧ c ≠ 0 := by
    by_contra! h
    exact hne ((ContinuousLinearMap.eq_zero_of_forall_hasEigenvalue_eq_zero hc hs).mp h)
  obtain ⟨c0,hc0,hc0n⟩ := hsome
  have hspec : (spectrum ℝ T).Nonempty :=
    ⟨c0, (hc.hasEigenvalue_iff_mem_spectrum hc0n).mp hc0⟩
  obtain ⟨c,hcsp,hcn⟩ := spectrum.exists_nnnorm_eq_spectralRadius_of_nonempty hspec
  have he : |c| = ‖T‖ := by
    rw [T.spectralRadius_eq_nnnorm hs.isSelfAdjoint] at hcn
    have hh := congrArg ENNReal.toReal hcn
    simpa only [ENNReal.coe_toReal, coe_nnnorm, Real.norm_eq_abs] using hh
  have hcnz : c ≠ 0 := by
    intro hc0
    have : ‖T‖ = 0 := by simpa [hc0] using he.symm
    exact hne (norm_eq_zero.mp this)
  obtain ⟨v,hv⟩ := ((hc.hasEigenvalue_iff_mem_spectrum hcnz).mpr hcsp).exists_hasEigenvector
  exact ⟨c,v,hv.2,hv.apply_eq_smul,he⟩

/-- Compactness upgrades every-vector strict Rayleigh control to a uniform strict norm bound. -/
theorem norm_lt_one_of_strict_rayleigh (T : E →L[ℝ] E) (hc : IsCompactOperator T)
    (hs : T.IsSymmetric)
    (hstrict : ∀ v : E, v ≠ 0 → |inner ℝ v (T v)| < ‖v‖^2) : ‖T‖ < 1 := by
  by_cases ht : T = 0
  · simp [ht]
  obtain ⟨c,v,hv,hTv,he⟩ := exists_norm_eigenvector T hc hs ht
  have hp : 0 < ‖v‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hv)
  have hb := hstrict v hv
  rw [hTv,inner_smul_right,real_inner_self_eq_norm_sq,abs_mul,
    abs_of_nonneg (sq_nonneg ‖v‖),he] at hb
  nlinarith only [hb,hp]

/-- Equality in the operator quadratic bound forces the corresponding eigenvector equation. -/
theorem eigenvector_of_inner_eq (T : E →L[ℝ] E) (v : E)
    (he : inner ℝ v (T v) = ‖T‖*‖v‖^2) : T v = ‖T‖ • v := by
  have hsq : ‖T v‖^2 ≤ (‖T‖*‖v‖)^2 :=
    (sq_le_sq₀ (norm_nonneg (T v)) (by positivity : 0 ≤ ‖T‖*‖v‖)).mpr (T.le_opNorm v)
  have h := norm_sub_sq_real (T v) (‖T‖ • v)
  rw [inner_smul_right, real_inner_comm v (T v), he, norm_smul,
    Real.norm_of_nonneg (norm_nonneg T)] at h
  have hz : ‖T v-‖T‖ • v‖^2 = 0 := by nlinarith [sq_nonneg ‖T v-‖T‖ • v‖]
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))
end Hilbert

section L2
open PositiveOperatorNeumann
variable {α : Type*} [MeasurableSpace α] (μ : Measure α)

/-- A proved modulus comparison upgrades the compact extremal eigenvector to a nonnegative one.
The modulus comparison is an explicit intermediate interface, proved from kernels downstream. -/
theorem exists_nonnegative_top_of_modulus (T : Operator μ) (hc : IsCompactOperator T)
    (hs : T.IsSymmetric) (hne : T ≠ 0)
    (hmod : ∀ f : RealL2 μ, |inner ℝ f (T f)| ≤ inner ℝ |f| (T |f|)) :
    ∃ f : RealL2 μ, f ≠ 0 ∧ Nonnegative μ f ∧ T f = ‖T‖ • f := by
  obtain ⟨c,v,hv,hTv,he⟩ := exists_norm_eigenvector T hc hs hne
  have hvabs : |v| ≠ 0 := by
    intro hzero
    apply hv
    apply norm_eq_zero.mp
    simpa only [norm_abs_eq_norm, norm_zero] using congrArg norm hzero
  have hlower := hmod v
  rw [hTv,inner_smul_right,real_inner_self_eq_norm_sq,abs_mul,
    abs_of_nonneg (sq_nonneg ‖v‖),he] at hlower
  have hupper : inner ℝ |v| (T |v|) ≤ ‖T‖*‖v‖^2 := by
    have hi := (real_inner_le_norm |v| (T |v|)).trans
      (mul_le_mul_of_nonneg_left (T.le_opNorm |v|) (norm_nonneg |v|))
    simpa only [norm_abs_eq_norm, sq, mul_left_comm] using hi
  have heq : inner ℝ |v| (T |v|) = ‖T‖*‖|v|‖^2 := by
    rw [norm_abs_eq_norm]
    exact le_antisymm hupper hlower
  refine ⟨|v|,hvabs,?_,eigenvector_of_inner_eq T |v| heq⟩
  exact (nonnegative_iff μ _).mpr (abs_nonneg v)
end L2

#print axioms exists_norm_eigenvector
#print axioms norm_lt_one_of_strict_rayleigh
#print axioms exists_nonnegative_top_of_modulus
end Legacy.BecknerOnofri.PositiveKernelRayleigh
