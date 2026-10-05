import BecknerOnofri.CubeLatticeTail

/-! The exact gamma bound for transverse lattice slices. -/
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Classical
open scoped BigOperators
namespace BecknerOnofri.HighDim.CubeLatticeTail
open Legacy.BecknerOnofri.ThetaDomination
open Legacy.TorusEndpoint.GreenMultiplierSummability

theorem finite_gaussian_le {m : ℕ} (B : Finset (Fin m → ℤ)) {t : ℝ} (ht : 0<t) :
    (∑ k∈B, Real.exp (-t * radiusSq k)) ≤ (1+Real.sqrt (Real.pi/t))^m := by
  let D : Fin m → Finset ℤ := fun i => B.image (fun k => k i)
  have hsub : B ⊆ Fintype.piFinset D := by
    intro k hk
    simp only [Fintype.mem_piFinset]
    intro i
    exact Finset.mem_image.mpr ⟨k,hk,rfl⟩
  have he (k : Fin m → ℤ) : Real.exp (-t*radiusSq k)=∏i,Real.exp (-t*(k i:ℝ)^2) := by
    rw [radiusSq,Finset.mul_sum,Real.exp_sum]
  simp_rw [he]
  calc
    _ ≤ ∑ k∈Fintype.piFinset D, ∏i,Real.exp (-t*(k i:ℝ)^2) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (by intro k hk hk'; positivity)
    _ = ∏i, ∑n∈D i,Real.exp (-t*(n:ℝ)^2) := (Finset.prod_univ_sum D (fun (_ : Fin m) (n : ℤ) => Real.exp (-t*(n:ℝ)^2))).symm
    _ ≤ ∏ _i : Fin m, (1+Real.sqrt (Real.pi/t)) := by
      apply Finset.prod_le_prod
      · intro i hi; positivity
      · intro i hi
        exact ((summable_realTheta ht).sum_le_tsum (D i) (by intro n hn; positivity)).trans
          (realTheta_le ht)
    _ = _ := by simp

def sliceWeight (p a : ℝ) {m : ℕ} (k : Fin m → ℤ) : ℝ := (a^2+radiusSq k)^(-p)
def sliceKernel (p a : ℝ) {m : ℕ} (k : Fin m → ℤ) (t : ℝ) : ℝ :=
  t^(p-1)*Real.exp (-((a^2+radiusSq k)*t))
def gammaKernel (p a : ℝ) (j : ℕ) (t : ℝ) : ℝ :=
  Real.pi^((j:ℝ)/2)*t^(p-(j:ℝ)/2-1)*Real.exp (-(a^2*t))
def gammaValue (p a : ℝ) (j : ℕ) : ℝ :=
  Real.pi^((j:ℝ)/2)*(1/a^2)^(p-(j:ℝ)/2)*Real.Gamma (p-(j:ℝ)/2)

theorem sliceKernel_integrable {p a : ℝ} (hp : 0<p) (ha : 0<a) {m : ℕ}
    (k : Fin m → ℤ) : IntegrableOn (sliceKernel p a k) (Ioi 0) := by
  apply Legacy.TorusEndpoint.GreenMellinMultiplier.gamma_integrand_integrable hp
  exact add_pos_of_pos_of_nonneg (sq_pos_of_pos ha) (radiusSq_nonneg k)

theorem integral_sliceKernel {p a : ℝ} (hp : 0<p) (ha : 0<a) {m : ℕ}
    (k : Fin m → ℤ) : (∫t in Ioi 0,sliceKernel p a k t)=Real.Gamma p*sliceWeight p a k := by
  have hk0 : 0≤a^2+radiusSq k := add_nonneg (sq_nonneg a) (radiusSq_nonneg k)
  unfold sliceKernel sliceWeight
  rw [Real.integral_rpow_mul_exp_neg_mul_Ioi hp
    (add_pos_of_pos_of_nonneg (sq_pos_of_pos ha) (radiusSq_nonneg k)),one_div,
    Real.inv_rpow hk0,← Real.rpow_neg hk0]
  exact mul_comm _ _

theorem gammaKernel_integrable {p a : ℝ} {j : ℕ} (hp : (j:ℝ)/2<p) (ha : 0<a) :
    IntegrableOn (gammaKernel p a j) (Ioi 0) := by
  unfold gammaKernel
  simpa only [IntegrableOn,mul_assoc] using
    (Legacy.TorusEndpoint.GreenMellinMultiplier.gamma_integrand_integrable
      (sub_pos.mpr hp) (sq_pos_of_pos ha)).const_mul (Real.pi^((j:ℝ)/2))

theorem integral_gammaKernel {p a : ℝ} {j : ℕ} (hp : (j:ℝ)/2<p) (ha : 0<a) :
    (∫t in Ioi 0,gammaKernel p a j t)=gammaValue p a j := by
  simp only [gammaKernel,gammaValue,mul_assoc,integral_const_mul]
  rw [Real.integral_rpow_mul_exp_neg_mul_Ioi (sub_pos.mpr hp) (sq_pos_of_pos ha)]

/-- Binomial expansion of the Gaussian integral majorant. -/
theorem binomial_kernel {p a t : ℝ} (ht : 0<t) (m : ℕ) :
    t^(p-1)*Real.exp (-(a^2*t))*(1+Real.sqrt (Real.pi/t))^m =
      ∑j∈Finset.range (m+1), (m.choose j:ℝ)*gammaKernel p a j t := by
  rw [add_comm 1,add_pow]
  simp only [one_pow,mul_one,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hpow : (Real.sqrt (Real.pi/t))^j=Real.pi^((j:ℝ)/2)*t^(-((j:ℝ)/2)) := by
    rw [Real.sqrt_eq_rpow,← Real.rpow_natCast,← Real.rpow_mul (by positivity),
      Real.div_rpow (by positivity) ht.le]
    rw [show (1/2:ℝ)*j=(j:ℝ)/2 by ring,div_eq_mul_inv,← Real.rpow_neg ht.le]
  rw [hpow]
  unfold gammaKernel
  have hr := Real.rpow_add ht (p-1) (-((j:ℝ)/2))
  rw [show p-(j:ℝ)/2-1=(p-1)+(-((j:ℝ)/2)) by ring,hr]
  ring

theorem finite_sliceKernel_le {p a t : ℝ} (ht : 0<t) {m : ℕ}
    (B : Finset (Fin m → ℤ)) :
    (∑k∈B,sliceKernel p a k t) ≤
      ∑j∈Finset.range (m+1), (m.choose j:ℝ)*gammaKernel p a j t := by
  rw [← binomial_kernel ht m]
  have he (k : Fin m → ℤ) : sliceKernel p a k t=
      (t^(p-1)*Real.exp (-(a^2*t)))*Real.exp (-t*radiusSq k) := by
    unfold sliceKernel
    rw [show -((a^2+radiusSq k)*t)=-(a^2*t)+(-t*radiusSq k) by ring,Real.exp_add]
    ring
  simp_rw [he]
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (finite_gaussian_le B ht) (by positivity)

/-- Every finite part of the actual transverse lattice slice has the exact gamma bound. -/
theorem finite_slice_le {p a : ℝ} {m : ℕ} (hp : (m:ℝ)/2<p) (ha : 0<a)
    (B : Finset (Fin m → ℤ)) :
    (∑k∈B,sliceWeight p a k) ≤
      (∑j∈Finset.range (m+1),(m.choose j:ℝ)*gammaValue p a j)/Real.Gamma p := by
  have hp0 : 0<p := lt_of_le_of_lt (by positivity) hp
  have hjp (j : ℕ) (hj : j∈Finset.range (m+1)) : (j:ℝ)/2<p := by
    have hjm : (j:ℝ)≤m := by exact_mod_cast (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
    linarith
  have hleft : IntegrableOn (fun t=>∑k∈B,sliceKernel p a k t) (Ioi 0) :=
    integrable_finset_sum _ (fun k hk=>sliceKernel_integrable hp0 ha k)
  have hright : IntegrableOn (fun t=>∑j∈Finset.range (m+1),(m.choose j:ℝ)*gammaKernel p a j t)
      (Ioi 0) := integrable_finset_sum _ (fun j hj=>(gammaKernel_integrable (hjp j hj) ha).const_mul _)
  have hint := integral_mono_ae hleft hright (ae_restrict_of_forall_mem measurableSet_Ioi
    (fun t ht=>finite_sliceKernel_le ht B))
  rw [integral_finset_sum _ (fun k hk=>sliceKernel_integrable hp0 ha k)] at hint
  rw [integral_finset_sum _ (fun j hj=>(gammaKernel_integrable (hjp j hj) ha).const_mul _)] at hint
  simp_rw [integral_sliceKernel hp0 ha,← Finset.mul_sum] at hint
  have he : (∑j∈Finset.range (m+1), ∫t in Ioi 0,(m.choose j:ℝ)*gammaKernel p a j t)=
      ∑j∈Finset.range (m+1),(m.choose j:ℝ)*gammaValue p a j := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [integral_const_mul,integral_gammaKernel (hjp j hj) ha]
  rw [he] at hint
  exact (le_div_iff₀ (Real.Gamma_pos_of_pos hp0)).mpr (by simpa [mul_comm] using hint)

def sliceBound (p : ℝ) (m : ℕ) (a : ℝ) : ℝ :=
  ∑j∈Finset.range (m+1), (m.choose j:ℝ)*Real.pi^((j:ℝ)/2)*
    Real.Gamma (p-(j:ℝ)/2)/Real.Gamma p * a^((j:ℝ)-2*p)

theorem gammaValue_eq {p a : ℝ} (ha : 0<a) (j : ℕ) :
    gammaValue p a j=Real.pi^((j:ℝ)/2)*Real.Gamma (p-(j:ℝ)/2)*a^((j:ℝ)-2*p) := by
  unfold gammaValue
  have he : (1/a^2)^(p-(j:ℝ)/2)=a^((j:ℝ)-2*p) := by
    rw [one_div,Real.inv_rpow (sq_nonneg a),← Real.rpow_neg (sq_nonneg a),
      ← Real.rpow_natCast,← Real.rpow_mul ha.le]
    congr 1
    push_cast
    ring
  rw [he]
  ring

theorem finite_slice_le_explicit {p a : ℝ} {m : ℕ} (hp : (m:ℝ)/2<p) (ha : 0<a)
    (B : Finset (Fin m → ℤ)) : (∑k∈B,sliceWeight p a k) ≤ sliceBound p m a := by
  convert finite_slice_le hp ha B using 1
  unfold sliceBound
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  rw [gammaValue_eq ha]
  ring

theorem slice_summable {p a : ℝ} {m : ℕ} (hp : (m:ℝ)/2<p) (ha : 0<a) :
    Summable (sliceWeight p a : (Fin m → ℤ) → ℝ) :=
  summable_of_sum_le (fun k=>Real.rpow_nonneg (add_nonneg (sq_nonneg a) (radiusSq_nonneg k)) _)
    (finite_slice_le_explicit hp ha)

theorem slice_tsum_le {p a : ℝ} {m : ℕ} (hp : (m:ℝ)/2<p) (ha : 0<a) :
    (∑' k : Fin m → ℤ,sliceWeight p a k) ≤ sliceBound p m a :=
  (slice_summable hp ha).tsum_le_of_sum_le (finite_slice_le_explicit hp ha)

#print axioms slice_tsum_le
end BecknerOnofri.HighDim.CubeLatticeTail
