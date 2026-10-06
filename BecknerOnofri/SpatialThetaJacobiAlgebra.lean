module

public import BecknerOnofri.SpatialThetaProduct
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Analysis.Fourier.AddCircle

@[expose] public section

/-! Fourier coefficients of finite Laurent polynomials on a circle of arbitrary
nonzero complex radius. This is the algebraic coefficient-scaling step in the
normalized Jacobi product proof. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped BigOperators Topology
namespace BecknerOnofri.HighDim.SpatialThetaJacobi

abbrev Space := C(UnitAddCircle,ℂ)
abbrev Laurent := AddMonoidAlgebra ℂ ℤ

def coefficient (n : ℤ) : Space →L[ℂ] ℂ :=
  ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 n).comp
    (fourierBasis (T := 1)).repr.toContinuousLinearEquiv.toContinuousLinearMap).comp
      (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ)

theorem coefficient_apply (n : ℤ) (f : Space) : coefficient n f=fourierCoeff f n := by
  change fourierBasis.repr (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ f) n=_
  rw [fourierBasis_repr,fourierCoeff_toLp]

theorem coefficient_fourier (n k : ℤ) : coefficient n (fourier k)=if n=k then 1 else 0 := by
  rw [coefficient_apply,fourierCoeff_fourier]
  simp [Pi.single_apply,eq_comm]

theorem coefficient_ext {f g : Space} (h : ∀ n,coefficient n f=coefficient n g) : f=g := by
  apply ContinuousMap.toLp_injective (p := 2) (𝕜 := ℂ) AddCircle.haarAddCircle
  apply (fourierBasis (T := 1)).repr.injective
  exact lp.ext (funext h)

def radiusCharacter (R : ℂ) (hR : R≠0) : Multiplicative ℤ →* Space where
  toFun n := R^n.toAdd • fourier n.toAdd
  map_one' := by
    ext x
    simp
  map_mul' m n := by
    ext x
    change R^(m.toAdd+n.toAdd)*fourier (m.toAdd+n.toAdd) x=
      (R^m.toAdd*fourier m.toAdd x)*(R^n.toAdd*fourier n.toAdd x)
    rw [zpow_add₀ hR,fourier_add]
    ring

def evaluate (R : ℂ) (hR : R≠0) : Laurent →ₐ[ℂ] Space :=
  AddMonoidAlgebra.lift ℂ Space ℤ (radiusCharacter R hR)

theorem evaluate_single (R : ℂ) (hR : R≠0) (n : ℤ) (a : ℂ) :
    evaluate R hR (AddMonoidAlgebra.single n a)=(a*R^n) • fourier n := by
  rw [evaluate,AddMonoidAlgebra.lift_single]
  exact smul_smul a (R^n) (fourier n)

/-- Coefficients scale by the genuine Laurent radius to the integer frequency. -/
theorem coefficient_evaluate (R : ℂ) (hR : R≠0) (p : Laurent) (n : ℤ) :
    coefficient n (evaluate R hR p)=R^n*p.coeff n := by
  induction p using AddMonoidAlgebra.induction_on with
  | of k =>
      change coefficient n (evaluate R hR (AddMonoidAlgebra.single k 1))=_
      rw [evaluate_single,map_smul,coefficient_fourier]
      by_cases hnk : n=k
      · subst n
        simp
      · simp [hnk,Ne.symm hnk]
  | add p q hp hq =>
      simp only [map_add,hp,hq,AddMonoidAlgebra.coeff_add,Finsupp.coe_add,Pi.add_apply,mul_add]
  | smul a p hp =>
      simp only [map_smul,hp,AddMonoidAlgebra.coeff_smul,Finsupp.coe_smul,Pi.smul_apply,smul_eq_mul]
      ring

theorem coefficient_radius_scaling (R : ℂ) (hR : R≠0) (p : Laurent) (n : ℤ) :
    coefficient n (evaluate R hR p)=R^n*coefficient n (evaluate 1 one_ne_zero p) := by
  simp only [coefficient_evaluate,one_zpow,one_mul]

theorem coefficient_mul_fourier (f : Space) (k n : ℤ) :
    coefficient n (fourier k*f)=coefficient (n-k) f := by
  simp only [coefficient_apply,fourierCoeff,ContinuousMap.mul_apply,smul_eq_mul]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  dsimp only
  rw [← mul_assoc,← fourier_add,show -n+k=-(n-k) by ring]

#print axioms coefficient_evaluate
#print axioms coefficient_radius_scaling
end BecknerOnofri.HighDim.SpatialThetaJacobi
