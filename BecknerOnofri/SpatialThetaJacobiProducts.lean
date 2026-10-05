import BecknerOnofri.SpatialThetaJacobiAlgebra

/-! Norm-convergent Jacobi products in the actual circle Banach algebra and
their exact Fourier coefficient scaling with Laurent radius. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Filter
open scoped BigOperators Topology
namespace BecknerOnofri.HighDim.SpatialThetaJacobi
open SpatialThetaProduct

def oneSided (t : ℝ) (R : ℂ) (k : ℤ) : Space :=
  ∏' n : ℕ, (1+((qMode t n:ℂ)*R) • fourier k)

theorem oneSided_multipliable {t : ℝ} (ht : 0<t) (R : ℂ) (k : ℤ) :
    Multipliable (fun n : ℕ => (1+((qMode t n:ℂ)*R) • fourier k : Space)) := by
  apply multipliable_one_add_of_summable
  apply ((qMode_summable ht).mul_right ‖R‖).congr
  intro n
  simp only [norm_smul,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (qMode_pos t n),fourier_norm,mul_one]

theorem qMode_succ (t : ℝ) (n : ℕ) :
    qMode t (n+1)=qMode t n*Real.exp (-2*t) := by
  unfold qMode
  rw [← Real.exp_add]
  congr 1
  push_cast
  ring

/-- Exact shift of the norm-convergent one-sided product. -/
theorem oneSided_shift {t : ℝ} (ht : 0<t) (R : ℂ) (k : ℤ) :
    oneSided t R k=(1+((Real.exp (-t):ℂ)*R) • fourier k)*
      oneSided t ((Real.exp (-2*t):ℂ)*R) k := by
  have he (n : ℕ) : (1+((qMode t (n+1):ℂ)*R) • fourier k : Space)=
      1+((qMode t n:ℂ)*((Real.exp (-2*t):ℂ)*R)) • fourier k := by
    rw [qMode_succ,Complex.ofReal_mul,mul_assoc]
  have hs : Multipliable (fun n : ℕ => (1+((qMode t (n+1):ℂ)*R) • fourier k : Space)) :=
    (oneSided_multipliable ht ((Real.exp (-2*t):ℂ)*R) k).congr (fun n => (he n).symm)
  rw [oneSided,tprod_eq_zero_mul' hs,show qMode t 0=Real.exp (-t) by simp [qMode]]
  congr 1
  apply tprod_congr
  exact he

def pairedProduct (t : ℝ) (R : ℂ) : Space := oneSided t R 1*oneSided t R⁻¹ (-1)

def finiteLaurent (t : ℝ) (N : ℕ) : Laurent :=
  ∏ n∈Finset.range N,
    (1+AddMonoidAlgebra.single (1:ℤ) (qMode t n:ℂ))*
      (1+AddMonoidAlgebra.single (-1:ℤ) (qMode t n:ℂ))

theorem evaluate_finiteLaurent (t : ℝ) (N : ℕ) (R : ℂ) (hR : R≠0) :
    evaluate R hR (finiteLaurent t N)=
      (∏ n∈Finset.range N, (1+((qMode t n:ℂ)*R) • fourier 1)) *
      (∏ n∈Finset.range N, (1+((qMode t n:ℂ)*R⁻¹) • fourier (-1))) := by
  simp only [finiteLaurent,map_prod,map_mul,map_add,map_one,evaluate_single,
    zpow_one,zpow_neg_one,Finset.prod_mul_distrib]

/-- Laurent polynomial approximants converge in supremum norm at every
nonzero complex radius. No coefficient or product identity is presumed. -/
theorem tendsto_evaluate {t : ℝ} (ht : 0<t) (R : ℂ) (hR : R≠0) :
    Tendsto (fun N => evaluate R hR (finiteLaurent t N)) atTop (𝓝 (pairedProduct t R)) := by
  simp only [evaluate_finiteLaurent]
  exact (oneSided_multipliable ht R 1).tendsto_prod_tprod_nat.mul
    (oneSided_multipliable ht R⁻¹ (-1)).tendsto_prod_tprod_nat

/-- Pass the exact finite Laurent radius scaling through norm-convergent
products and the actual continuous Fourier coefficient map. -/
theorem coefficient_paired_scaling {t : ℝ} (ht : 0<t) (R : ℂ) (hR : R≠0) (n : ℤ) :
    coefficient n (pairedProduct t R)=R^n*coefficient n (pairedProduct t 1) := by
  have h1 := (coefficient n).continuous.continuousAt.tendsto.comp (tendsto_evaluate ht R hR)
  have h2 := (tendsto_const_nhds (x := R^n)).mul
    ((coefficient n).continuous.continuousAt.tendsto.comp (tendsto_evaluate ht 1 one_ne_zero))
  apply tendsto_nhds_unique h1
  exact h2.congr' (Filter.Eventually.of_forall
    (fun N => (coefficient_radius_scaling R hR (finiteLaurent t N) n).symm))

theorem pairedProduct_shift {t : ℝ} (ht : 0<t) :
    pairedProduct t (Real.exp (-2*t):ℂ)=
      (Real.exp (-t):ℂ)⁻¹ • (fourier (-1)*pairedProduct t 1) := by
  let q : ℂ := Real.exp (-t)
  let b : ℂ := Real.exp (-2*t)
  have hq : q≠0 := Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'
  have hb : b≠0 := Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'
  have hbq : b=q^2 := by
    dsimp [q,b]
    rw [← Complex.ofReal_pow]
    congr 1
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
  have hA := oneSided_shift ht (1:ℂ) (1:ℤ)
  have hB := oneSided_shift ht b⁻¹ (-1:ℤ)
  simp only [mul_one] at hA
  rw [mul_inv_cancel₀ hb] at hB
  have hchars (x : UnitAddCircle) : fourier (-1) x*fourier 1 x=(1:ℂ) := by
    rw [← fourier_add]
    norm_num
  ext x
  change oneSided t b 1 x*oneSided t b⁻¹ (-1) x=
    q⁻¹*(fourier (-1) x*(oneSided t 1 1 x*oneSided t 1⁻¹ (-1) x))
  rw [hB,hA,inv_one]
  simp only [ContinuousMap.mul_apply,ContinuousMap.add_apply,ContinuousMap.one_apply,
    ContinuousMap.smul_apply,smul_eq_mul]
  change oneSided t b 1 x*((1+(q*b⁻¹)*fourier (-1) x)*oneSided t 1 (-1) x)=
    q⁻¹*(fourier (-1) x*((1+q*fourier 1 x)*oneSided t b 1 x*oneSided t 1 (-1) x))
  have hqb : q*b⁻¹=q⁻¹ := by rw [hbq]; field_simp
  have hh : 1+q⁻¹*fourier (-1) x=q⁻¹*fourier (-1) x*(1+q*fourier 1 x) := by
    symm
    calc
      _ = q⁻¹*fourier (-1) x+(q⁻¹*q)*(fourier (-1) x*fourier 1 x) := by ring
      _ = _ := by rw [inv_mul_cancel₀ hq,hchars]; ring
  rw [hqb,hh]
  ring

#print axioms coefficient_paired_scaling
#print axioms pairedProduct_shift
end BecknerOnofri.HighDim.SpatialThetaJacobi
