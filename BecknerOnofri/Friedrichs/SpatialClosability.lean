module

public import BecknerOnofri.Friedrichs.AngularOperatorGraph
public import BecknerOnofri.Friedrichs.ClosedFormTests
public import Legacy.BecknerOnofri.JacobiCompleteness

@[expose] public section

/-! Uniqueness of the derivative and potential components in the spatial form
closure. Completeness of ordinary cosine and sine-weighted polynomial tests
is used only to separate L2 vectors, not to define the form domain. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped ContDiff
namespace BecknerOnofri.Friedrichs.SpatialForm
open Legacy.BecknerOnofri.JacobiAngular

def continuousLp {f : ℝ → ℝ} (hf : Continuous f) : H := (continuous_memLp hf).toLp f

lemma core_derivative_test {m : ℕ} {v : EnergySpace} (hv : v∈core m)
    {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) :
    inner ℝ v.2.1 (continuousLp hg.continuous) =
      -inner ℝ v.1 (continuousLp (contDiff_infty_iff_deriv.mp hg).2.continuous) := by
  obtain ⟨φ,hφ,hφc,hφs,hv0,hv1,hvV⟩ := hv
  have hend := compact_test_endpoints hφs
  unfold continuousLp
  rw [inner_eq_integral_of_ae hv1 (continuous_memLp hg.continuous).coeFn_toLp,
    inner_eq_integral_of_ae hv0
      (continuous_memLp (contDiff_infty_iff_deriv.mp hg).2.continuous).coeFn_toLp]
  have hip := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := (0:ℝ)) (b := Real.pi)
    (fun t _ => (hφ.differentiable (by simp) t).hasDerivAt)
    (fun t _ => (hg.differentiable (by simp) t).hasDerivAt)
    ((contDiff_infty_iff_deriv.mp hφ).2.continuous.intervalIntegrable 0 Real.pi)
    ((contDiff_infty_iff_deriv.mp hg).2.continuous.intervalIntegrable 0 Real.pi)
  simp only [hend.1,hend.2,zero_mul,sub_self,zero_sub,
    intervalIntegral.integral_of_le Real.pi_pos.le,integral_Ioc_eq_integral_Ioo] at hip
  change (∫ t in Ioo 0 Real.pi,deriv φ t*g t)=-(∫ t in Ioo 0 Real.pi,φ t*deriv g t)
  linarith

lemma closed_derivative_test {m : ℕ} {v : EnergySpace} (hv : v∈formClosure m)
    {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) :
    inner ℝ v.2.1 (continuousLp hg.continuous) =
      -inner ℝ v.1 (continuousLp (contDiff_infty_iff_deriv.mp hg).2.continuous) := by
  exact closure_minimal (fun w hw => core_derivative_test hw hg)
    (isClosed_eq ((continuous_fst.comp continuous_snd).inner continuous_const)
      ((continuous_fst.inner continuous_const).neg)) hv

lemma closed_potential_test {m : ℕ} {v : EnergySpace} (hv : v∈formClosure m)
    {g q : ℝ → ℝ} (hg : Continuous g) (hq : Continuous q)
    (he : (fun t => potentialFactor m t*g t)=ᵐ[intervalMeasure] q) :
    inner ℝ v.2.2 (continuousLp hg)=inner ℝ v.1 (continuousLp hq) := by
  apply closure_minimal (s := core m) (t := {w : EnergySpace |
    inner ℝ w.2.2 (continuousLp hg)=inner ℝ w.1 (continuousLp hq)}) _
    (isClosed_eq ((continuous_snd.comp continuous_snd).inner continuous_const)
      (continuous_fst.inner continuous_const)) hv
  intro w hw
  obtain ⟨φ,hφ,hφc,hφs,hw0,hw1,hwV⟩ := hw
  change inner ℝ w.2.2 (continuousLp hg)=inner ℝ w.1 (continuousLp hq)
  unfold continuousLp
  rw [inner_eq_integral_of_ae hwV (continuous_memLp hg).coeFn_toLp,
    inner_eq_integral_of_ae hw0 (continuous_memLp hq).coeFn_toLp]
  apply integral_congr_ae
  filter_upwards [he] with t ht
  rw [← ht]
  ring

lemma derivative_component_unique {m : ℕ} {v w : EnergySpace}
    (hv : v∈formClosure m) (hw : w∈formClosure m) (he : v.1=w.1) : v.2.1=w.2.1 := by
  apply sub_eq_zero.mp
  apply Legacy.BecknerOnofri.JacobiEigenfunctions.eq_zero_of_orthogonal_eigenvector (v.2.1-w.2.1) 0
  intro n
  have hv' := closed_derivative_test hv (Legacy.BecknerOnofri.JacobiEigenfunctions.eigenfunction_contDiff 0 n)
  have hw' := closed_derivative_test hw (Legacy.BecknerOnofri.JacobiEigenfunctions.eigenfunction_contDiff 0 n)
  have ht : continuousLp (Legacy.BecknerOnofri.JacobiEigenfunctions.eigenfunction_contDiff 0 n).continuous=Legacy.BecknerOnofri.JacobiEigenfunctions.eigenvector 0 n := by
    apply Lp.ext
    exact (continuous_memLp (Legacy.BecknerOnofri.JacobiEigenfunctions.eigenfunction_contDiff 0 n).continuous).coeFn_toLp.trans
      (Legacy.BecknerOnofri.JacobiEigenfunctions.eigenvector_ae_eq 0 n).symm
  rw [ht,he] at hv'
  rw [ht] at hw'
  rw [inner_sub_left,hv',hw',sub_self]

lemma potential_component_unique {m : ℕ} {v w : EnergySpace}
    (hv : v∈formClosure m) (hw : w∈formClosure m) (he : v.1=w.1) : v.2.2=w.2.2 := by
  apply sub_eq_zero.mp
  apply Legacy.BecknerOnofri.JacobiEigenfunctions.eq_zero_of_orthogonal_eigenvector (v.2.2-w.2.2) 1
  intro n
  let q : ℝ → ℝ := fun t => Real.sqrt ((m:ℝ)*((m:ℝ)-1))*(Legacy.BecknerOnofri.JacobiEigenfunctions.polynomial 1 n).eval (Real.cos t)
  have hq : Continuous q := continuous_const.mul
    ((polynomial_contDiff (Legacy.BecknerOnofri.JacobiEigenfunctions.polynomial 1 n)).continuous.comp Real.continuous_cos)
  have hmul : (fun t => potentialFactor m t*Legacy.BecknerOnofri.JacobiEigenfunctions.eigenfunction 1 n t)=ᵐ[intervalMeasure] q := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have hn := (Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2).ne'
    dsimp [potentialFactor,Legacy.BecknerOnofri.JacobiEigenfunctions.eigenfunction,angular,q]
    simp only [pow_one]
    field_simp
  have hv' := closed_potential_test hv (Legacy.BecknerOnofri.JacobiEigenfunctions.eigenfunction_contDiff 1 n).continuous hq hmul
  have hw' := closed_potential_test hw (Legacy.BecknerOnofri.JacobiEigenfunctions.eigenfunction_contDiff 1 n).continuous hq hmul
  have ht : continuousLp (Legacy.BecknerOnofri.JacobiEigenfunctions.eigenfunction_contDiff 1 n).continuous=Legacy.BecknerOnofri.JacobiEigenfunctions.eigenvector 1 n := by
    apply Lp.ext
    exact (continuous_memLp (Legacy.BecknerOnofri.JacobiEigenfunctions.eigenfunction_contDiff 1 n).continuous).coeFn_toLp.trans
      (Legacy.BecknerOnofri.JacobiEigenfunctions.eigenvector_ae_eq 1 n).symm
  rw [ht,he] at hv'
  rw [ht] at hw'
  rw [inner_sub_left,hv',hw',sub_self]

theorem formClosure_fst_injective (m : ℕ) :
    Set.InjOn (fun v : EnergySpace => v.1) (formClosure m) := by
  intro v hv w hw he
  exact Prod.ext he (Prod.ext (derivative_component_unique hv hw he)
    (potential_component_unique hv hw he))

#print axioms formClosure_fst_injective
end BecknerOnofri.Friedrichs.SpatialForm
