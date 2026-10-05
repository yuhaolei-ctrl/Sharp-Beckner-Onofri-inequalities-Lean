import Legacy.BecknerOnofri.CircleHeatDerivative

/-! Actual spatial theta Fourier truncation with an explicit complete tail.
The parameter is the source convention exp(-t*n²), including t∈[a,b]. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Topology BigOperators
namespace BecknerOnofri.HighDim.RadialThetaTail
open Legacy.BecknerOnofri.CircleHeat

def theta (t y : ℝ) : ℝ := realHeat (t/Real.pi) y

def mode (t y : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-t*((n:ℝ)+1)^2)*Real.cos (2*Real.pi*((n:ℝ)+1)*y)

def partialTheta (M : ℕ) (t y : ℝ) : ℝ := 1+2*∑ n∈Finset.range M,mode t y n

theorem mode_eq (t y : ℝ) (n : ℕ) : mode t y n=cosineTerm (t/Real.pi) n y := by
  unfold mode cosineTerm
  congr 2
  field_simp

theorem mode_summable {t : ℝ} (ht : 0<t) (y : ℝ) : Summable (mode t y) := by
  exact (summable_cosineTerm (div_pos ht Real.pi_pos) y).congr (fun n => (mode_eq t y n).symm)

theorem theta_series {t : ℝ} (ht : 0<t) (y : ℝ) : theta t y=1+2*∑' n,mode t y n := by
  simpa only [theta,mode_eq] using realHeat_eq_cosine_series (div_pos ht Real.pi_pos) y

theorem mode_shift_bound {a t : ℝ} (ha : 0<a) (hat : a≤t) (M n : ℕ) (y : ℝ) :
    |mode t y (n+M)|≤Real.exp (-a*((M:ℝ)+1)^2)*(Real.exp (-a*(2*(M:ℝ)+3)))^n := by
  have hn : (0:ℝ)≤n := Nat.cast_nonneg n
  have hM : (0:ℝ)≤M := Nat.cast_nonneg M
  have hn2 : (n:ℝ)≤(n:ℝ)^2 := by exact_mod_cast Nat.le_self_pow (by norm_num : 2≠0) n
  have hsq : ((M:ℝ)+1)^2+(2*(M:ℝ)+3)*n≤((n:ℝ)+M+1)^2 := by nlinarith
  have h1 := mul_le_mul_of_nonneg_left hsq ha.le
  have h2 := mul_le_mul_of_nonneg_right hat (sq_nonneg ((n:ℝ)+M+1))
  calc
    _ ≤ Real.exp (-t*(((n+M:ℕ):ℝ)+1)^2) := by
      unfold mode
      rw [abs_mul,abs_of_pos (Real.exp_pos _)]
      exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_cos_le_one _)
    _ ≤ _ := by
      rw [← Real.exp_nat_mul,← Real.exp_add]
      apply Real.exp_le_exp.mpr
      push_cast
      nlinarith

theorem tail_geometric_hasSum {a : ℝ} (ha : 0<a) (M : ℕ) :
    HasSum (fun n : ℕ => Real.exp (-a*((M:ℝ)+1)^2)*(Real.exp (-a*(2*(M:ℝ)+3)))^n)
      (Real.exp (-a*((M:ℝ)+1)^2)/(1-Real.exp (-a*(2*(M:ℝ)+3)))) := by
  have hM : (0:ℝ)≤M := Nat.cast_nonneg M
  have hlt : ‖Real.exp (-a*(2*(M:ℝ)+3))‖<1 := by
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),Real.exp_lt_one_iff]
    have hp : 0<a*(2*(M:ℝ)+3) := mul_pos ha (by linarith)
    linarith
  simpa only [div_eq_mul_inv] using (hasSum_geometric_of_norm_lt_one hlt).mul_left
    (Real.exp (-a*((M:ℝ)+1)^2))

/-- Every omitted Fourier mode is included in the geometric error bound. -/
theorem theta_truncation_error {a t : ℝ} (ha : 0<a) (hat : a≤t) (M : ℕ) (y : ℝ) :
    |theta t y-partialTheta M t y|≤
      2*Real.exp (-a*((M:ℝ)+1)^2)/(1-Real.exp (-a*(2*(M:ℝ)+3))) := by
  have ht : 0<t := ha.trans_le hat
  have hs := mode_summable ht y
  have he := hs.sum_add_tsum_nat_add M
  have hn : Summable (fun n : ℕ => ‖mode t y (n+M)‖) := by
    apply (tail_geometric_hasSum ha M).summable.of_norm_bounded
    intro n
    simpa only [norm_norm,Real.norm_eq_abs,abs_abs] using mode_shift_bound ha hat M n y
  have hbound : |∑' n,mode t y (n+M)|≤
      Real.exp (-a*((M:ℝ)+1)^2)/(1-Real.exp (-a*(2*(M:ℝ)+3))) := by
    calc
      _ ≤ ∑' n,‖mode t y (n+M)‖ := by simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hn
      _ ≤ _ := hasSum_le (fun n => by
        simpa only [Real.norm_eq_abs] using mode_shift_bound ha hat M n y) hn.hasSum (tail_geometric_hasSum ha M)
  rw [theta_series ht,partialTheta]
  have he' : (1+2*∑' n,mode t y n)-(1+2*∑ n∈Finset.range M,mode t y n)=
      2*∑' n,mode t y (n+M) := by linarith [he]
  rw [he',abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
  exact (mul_le_mul_of_nonneg_left hbound (by norm_num)).trans_eq (by ring)

/-- The twelve-mode remainder appearing verbatim in the d12 seed construction. -/
theorem theta_twelve_remainder {a t : ℝ} (ha : 0<a) (hat : a≤t) (y : ℝ) :
    |theta t y-partialTheta 12 t y|≤2*Real.exp (-169*a)/(1-Real.exp (-27*a)) := by
  convert! theta_truncation_error ha hat 12 y using 1 <;> congr 1 <;> norm_num <;> ring

#print axioms theta_truncation_error
#print axioms theta_twelve_remainder
end BecknerOnofri.HighDim.RadialThetaTail
