import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Exact eigenspaces and their dimensions for the permutation-invariant
active-amplitude matrix. The analytic application must identify its actual
Hessian with this endomorphism and discharge the nonzero coefficient. -/
noncomputable section
open scoped BigOperators
namespace BecknerOnofri.EquicorrelatedSpectrum
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def total : (ι → ℝ) →ₗ[ℝ] ℝ where
  toFun := fun x => ∑ i,x i
  map_add' := fun x y => by simp [Finset.sum_add_distrib]
  map_smul' := fun c x => by simp [Finset.mul_sum]

def operator (a b : ℝ) : Module.End ℝ (ι → ℝ) :=
  a • LinearMap.id + b • LinearMap.pi (fun _ => total)

@[simp] theorem operator_apply (a b : ℝ) (x : ι → ℝ) (i : ι) :
    operator a b x i=a*x i+b*∑ j,x j := rfl

/-- The constant-amplitude line. -/
def constantLine : Submodule ℝ (ι → ℝ) := Submodule.span ℝ {(fun _ : ι => (1:ℝ))}

/-- Redistribution of squared amplitudes with fixed total amplitude. -/
def zeroSum : Submodule ℝ (ι → ℝ) := LinearMap.ker total

lemma mem_constantLine (x : ι → ℝ) : x∈constantLine ↔ ∃ c : ℝ,∀ i,x i=c := by
  rw [constantLine,Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c,hc⟩
    exact ⟨c,fun i => by simpa using (congrFun hc i).symm⟩
  · rintro ⟨c,hc⟩
    exact ⟨c,by funext i; simpa using (hc i).symm⟩

variable [Nonempty ι]

theorem radial_eigenspace (a b : ℝ) (hb : b≠0) :
    (operator (ι := ι) a b).eigenspace (a+(Fintype.card ι : ℝ)*b)=constantLine := by
  ext x
  rw [Module.End.mem_eigenspace_iff,mem_constantLine]
  constructor
  · intro hx
    have hn : (Fintype.card ι : ℝ)≠0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    refine ⟨(∑ i,x i)/(Fintype.card ι : ℝ),?_⟩
    intro i
    have hi := congrFun hx i
    simp only [operator_apply,Pi.smul_apply,smul_eq_mul] at hi
    apply (eq_div_iff hn).mpr
    apply mul_left_cancel₀ hb
    nlinarith [hi]
  · rintro ⟨c,hc⟩
    funext i
    simp only [operator_apply,Pi.smul_apply,smul_eq_mul,hc,
      Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    ring

theorem transverse_eigenspace (a b : ℝ) (hb : b≠0) :
    (operator (ι := ι) a b).eigenspace a=zeroSum := by
  ext x
  rw [Module.End.mem_eigenspace_iff]
  change operator a b x=a • x ↔ (∑ i,x i)=0
  constructor
  · intro hx
    have hi := congrFun hx (Classical.arbitrary ι)
    simp only [operator_apply,Pi.smul_apply,smul_eq_mul] at hi
    apply (mul_eq_zero.mp (show b*(∑ i,x i)=0 by linarith)).resolve_left hb
  · intro hx
    funext i
    simp [hx]

theorem constantLine_finrank : Module.finrank ℝ (constantLine (ι := ι))=1 := by
  apply finrank_span_singleton
  intro h
  have hi := congrFun h (Classical.arbitrary ι)
  norm_num at hi

theorem zeroSum_finrank : Module.finrank ℝ (zeroSum (ι := ι))=Fintype.card ι-1 := by
  have hs : Function.Surjective (total : (ι → ℝ) →ₗ[ℝ] ℝ) := by
    intro c
    refine ⟨Pi.single (Classical.arbitrary ι) c,?_⟩
    simp [total]
  have h := (total : (ι → ℝ) →ₗ[ℝ] ℝ).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hs] at h
  simp only [finrank_top,Module.finrank_self,Module.finrank_pi] at h
  change Module.finrank ℝ (LinearMap.ker (total (ι := ι)))=_
  omega

theorem eigenvalue_multiplicities (a b : ℝ) (hb : b≠0) :
    Module.finrank ℝ ((operator (ι := ι) a b).eigenspace (a+(Fintype.card ι : ℝ)*b))=1 ∧
    Module.finrank ℝ ((operator (ι := ι) a b).eigenspace a)=Fintype.card ι-1 := by
  rw [radial_eigenspace a b hb,transverse_eigenspace a b hb]
  exact ⟨constantLine_finrank,zeroSum_finrank⟩

#print axioms eigenvalue_multiplicities
end BecknerOnofri.EquicorrelatedSpectrum
