import BecknerOnofri.BranchDefinitions
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Topology.Constructions
import Mathlib.Tactic

/-! Raw smooth periodic lifts have smooth coordinate derivatives on the torus.
No assumption on Fourier coefficients is used. -/
noncomputable section
open scoped ContDiff
namespace BecknerOnofri.SmoothTorus
open HighDim

def quotient {d : ℕ} (x : Fin d → ℝ) : Torus d := fun i => (x i : UnitAddCircle)

def Smooth {d : ℕ} (f : Torus d → ℂ) : Prop :=
  ContDiff ℝ ∞ (fun x : Fin d → ℝ => f (quotient x))

def axis {d : ℕ} (j : Fin d) (t : ℝ) : Torus d :=
  quotient (Pi.single j t)

def coordinateDeriv {d : ℕ} (j : Fin d) (f : Torus d → ℂ) (x : Torus d) : ℂ :=
  deriv (fun t : ℝ => f (x + axis j t)) 0

theorem quotient_surjective (d : ℕ) : Function.Surjective (@quotient d) := by
  intro x
  choose y hy using fun i => QuotientAddGroup.mk_surjective (x i)
  exact ⟨y,funext hy⟩

theorem quotient_add {d : ℕ} (x y : Fin d → ℝ) :
    quotient (x+y) = quotient x + quotient y := by
  ext i
  change ((x i + y i : ℝ) : UnitAddCircle) = _
  rw [AddCircle.coe_add]
  rfl

theorem smooth_continuous {d : ℕ} {f : Torus d → ℂ} (hf : Smooth f) :
    Continuous f := by
  have hq : IsOpenQuotientMap (@quotient d) :=
    IsOpenQuotientMap.piMap (fun _ : Fin d => QuotientAddGroup.isOpenQuotientMap_mk)
  exact hq.isQuotientMap.continuous_iff.mpr hf.continuous

theorem axis_continuous {d : ℕ} (j : Fin d) : Continuous (axis j) := by
  unfold axis quotient
  apply continuous_pi
  intro i
  by_cases hi : i=j
  · subst i
    simpa using AddCircle.continuous_mk' (1:ℝ)
  · simpa [Pi.single_eq_of_ne hi] using
      (continuous_const : Continuous (fun _ : ℝ => (0 : UnitAddCircle)))

theorem partial_lift {d : ℕ} {f : Torus d → ℂ} (hf : Smooth f)
    (j : Fin d) (x : Fin d → ℝ) :
    coordinateDeriv j f (quotient x) =
      fderiv ℝ (fun y => f (quotient y)) x (Pi.single j 1) := by
  let e : Fin d → ℝ := Pi.single j 1
  have he (t : ℝ) : t • e = Pi.single j t := by
    ext i
    by_cases h : i=j <;> simp [e,Pi.single_apply,h]
  have hd := (hf.differentiable (by simp) (x+(0:ℝ) • e)).hasFDerivAt.comp_hasDerivAt 0
    ((hasDerivAt_id (0:ℝ)).smul_const e |>.const_add x)
  simp only [Function.comp_def,id_eq,zero_smul,add_zero,one_smul] at hd
  have heq : (fun t : ℝ => f (quotient (x+t • e))) =
      (fun t : ℝ => f (quotient x + axis j t)) := by
    funext t
    rw [he,quotient_add]
    rfl
  rw [heq] at hd
  exact hd.deriv

theorem partial_smooth {d : ℕ} {f : Torus d → ℂ} (hf : Smooth f) (j : Fin d) :
    Smooth (coordinateDeriv j f) := by
  unfold Smooth
  simp_rw [partial_lift hf]
  exact (hf.fderiv_right (by simp)).clm_apply contDiff_const

theorem partial_hasDerivAt {d : ℕ} {f : Torus d → ℂ} (hf : Smooth f)
    (j : Fin d) (x : Torus d) (t : ℝ) :
    HasDerivAt (fun s : ℝ => f (x + axis j s)) (coordinateDeriv j f (x + axis j t)) t := by
  obtain ⟨y,rfl⟩ := quotient_surjective d x
  let e : Fin d → ℝ := Pi.single j 1
  have he (s : ℝ) : s • e = Pi.single j s := by
    ext i
    by_cases h : i=j <;> simp [e,Pi.single_apply,h]
  have hd := (hf.differentiable (by simp) (y+t • e)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).smul_const e |>.const_add y)
  simp only [Function.comp_def,id_eq,one_smul] at hd
  have heq : (fun s : ℝ => f (quotient (y+s • e))) =
      (fun s : ℝ => f (quotient y + axis j s)) := by
    funext s
    rw [he,quotient_add]
    rfl
  rw [heq] at hd
  have hq : quotient y + axis j t = quotient (y+t • e) := by
    rw [he,quotient_add]; rfl
  rw [hq,partial_lift hf]
  exact hd

def iterPartial {d : ℕ} (j : Fin d) (f : Torus d → ℂ) : ℕ → Torus d → ℂ
  | 0 => f
  | m+1 => coordinateDeriv j (iterPartial j f m)

theorem iterPartial_smooth {d : ℕ} {f : Torus d → ℂ} (hf : Smooth f)
    (j : Fin d) (m : ℕ) : Smooth (iterPartial j f m) := by
  induction m with
  | zero => exact hf
  | succ m ih => exact partial_smooth ih j

theorem of_real {d : ℕ} {f : Torus d → ℝ} (hf : HighDim.SmoothOnTorus f) :
    Smooth (fun x => (f x : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp hf

#print axioms partial_smooth
#print axioms partial_hasDerivAt
end BecknerOnofri.SmoothTorus
