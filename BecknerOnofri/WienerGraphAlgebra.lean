import BecknerOnofri.WienerGraphNorm
import Mathlib.Algebra.Ring.InjSurj

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace BecknerOnofri.HighDim.WienerGraph
open ContinuousGibbs ContinuousFirstShell
open LocalEleven.GraphRegularity LocalEleven.GraphWienerBounds LocalEleven.WienerAlgebraBounds

lemma graph_norm_smul {d m : ℕ} (c : ℝ) (x : graph d m) : ‖c • x‖=‖c‖*‖x‖ := norm_smul c x

instance graphOne (d m : ℕ) : One (graph d m) := ⟨ofRadial 1 (radial_one m)⟩
instance graphMul (d m : ℕ) : Mul (graph d m) := ⟨fun x y =>
  ofRadial (toContinuous d m x*toContinuous d m y)
    (radial_mul m _ _ (toContinuous_radial x) (toContinuous_radial y))⟩
instance graphNatCast (d m : ℕ) : NatCast (graph d m) := ⟨fun n => (n:ℝ) • (1 : graph d m)⟩
instance graphIntCast (d m : ℕ) : IntCast (graph d m) := ⟨fun n => (n:ℝ) • (1 : graph d m)⟩
instance graphPow (d m : ℕ) : Pow (graph d m) ℕ := ⟨fun x n => npowRec n x⟩

@[simp] lemma toContinuous_one (d m : ℕ) : toContinuous d m 1=1 := rfl
@[simp] lemma toContinuous_mul {d m : ℕ} (x y : graph d m) :
    toContinuous d m (x*y)=toContinuous d m x*toContinuous d m y := rfl

lemma toContinuous_pow {d m : ℕ} (x : graph d m) (n : ℕ) :
    toContinuous d m (x^n)=(toContinuous d m x)^n := by
  change toContinuous d m (npowRec n x)=(toContinuous d m x)^n
  induction n with
  | zero => rfl
  | succ n ih =>
      change toContinuous d m (npowRec n x*x)=(toContinuous d m x)^(n+1)
      rw [toContinuous_mul,ih,pow_succ]

lemma toContinuous_natCast (d m n : ℕ) : toContinuous d m (n : graph d m)=n := by
  change toContinuous d m ((n:ℝ) • (1 : graph d m))=n
  rw [map_smul,toContinuous_one]
  ext x
  simp

lemma toContinuous_intCast (d m : ℕ) (n : ℤ) : toContinuous d m (n : graph d m)=n := by
  change toContinuous d m ((n:ℝ) • (1 : graph d m))=n
  rw [map_smul,toContinuous_one]
  ext x
  simp

instance graphCommRing (d m : ℕ) : CommRing (graph d m) :=
  Function.Injective.commRing (toContinuous d m) (toContinuous_injective d m)
    (map_zero _) (toContinuous_one d m) (map_add _) toContinuous_mul
    (map_neg _) (map_sub _) (fun n x => map_nsmul _ n x) (fun n x => map_zsmul _ n x)
    toContinuous_pow (toContinuous_natCast d m) (toContinuous_intCast d m)

instance graphNormedCommRing (d m : ℕ) : NormedCommRing (graph d m) where
  __ := graphCommRing d m
  __ : NormedAddCommGroup (graph d m) := inferInstance
  norm_mul_le x y := by
    rw [norm_eq_wienerSize,norm_eq_wienerSize,norm_eq_wienerSize,toContinuous_mul]
    exact wienerSize_mul_le m _ _ (toContinuous_radial x) (toContinuous_radial y)

instance graphAlgebra (d m : ℕ) : Algebra ℝ (graph d m) :=
  Algebra.ofModule
    (fun c x y => (toContinuous_injective d m) (by
      simp only [toContinuous_mul,map_smul]
      exact smul_mul_assoc _ _ _))
    (fun c x y => (toContinuous_injective d m) (by
      simp only [toContinuous_mul,map_smul]
      exact mul_smul_comm _ _ _))

instance graphNormedAlgebra (d m : ℕ) : NormedAlgebra ℝ (graph d m) where
  __ := graphAlgebra d m
  norm_smul_le r x := le_of_eq (graph_norm_smul r x)

/-- The complete weighted Fourier space is a commutative real Banach algebra
whose product is the actual pointwise product of continuous torus functions. -/
theorem norm_mul_bound {d m : ℕ} (x y : graph d m) : ‖x*y‖≤‖x‖*‖y‖ := norm_mul_le x y

#print axioms norm_mul_bound
end BecknerOnofri.HighDim.WienerGraph
