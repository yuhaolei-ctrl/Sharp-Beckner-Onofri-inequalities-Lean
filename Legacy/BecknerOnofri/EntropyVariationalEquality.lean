import Legacy.TorusEndpoint.EntropyVariational
import Legacy.BecknerOnofri.Endpoint

/-! The equality case of the actual Gibbs variational inequality, with all
integrability and normalization conditions explicit. -/
namespace Legacy.BecknerOnofri.EntropyVariationalEquality
open MeasureTheory Legacy.TorusEndpoint

theorem entropy_young_eq_iff {r u : ℝ} (hr : 0 ≤ r) :
    r*u = r*Real.log r-r+Real.exp u ↔ r = Real.exp u := by
  constructor
  · intro he
    by_contra hne
    by_cases hz : r = 0
    · simp only [hz, zero_mul, sub_zero, zero_add] at he
      exact (Real.exp_pos u).ne he
    have hp : 0 < r := lt_of_le_of_ne hr (Ne.symm hz)
    have hdiff : u-Real.log r ≠ 0 := by
      intro h
      have hu := sub_eq_zero.mp h
      exact hne (by rw [hu, Real.exp_log hp])
    have h := Real.add_one_lt_exp hdiff
    rw [Real.exp_sub, Real.exp_log hp] at h
    have hm := (lt_div_iff₀ hp).mp h
    nlinarith
  · intro he
    rw [he, Real.log_exp]
    ring

theorem eq_normalized_exp_of_variational_eq {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsProbabilityMeasure μ] {rho u : X → ℝ}
    (hnonneg : ∀ᵐ x ∂μ, 0 ≤ rho x) (hmass : (∫ x, rho x ∂μ) = 1)
    (hr : Integrable rho μ)
    (hent : Integrable (fun x => rho x*Real.log (rho x)) μ)
    (hprod : Integrable (fun x => rho x*u x) μ)
    (hexp : Integrable (fun x => Real.exp (u x)) μ)
    (he : (∫ x, rho x*Real.log (rho x) ∂μ) =
      (∫ x, rho x*u x ∂μ) - Real.log (∫ x, Real.exp (u x) ∂μ)) :
    rho =ᵐ[μ] (fun x => Real.exp (u x)/(∫ y, Real.exp (u y) ∂μ)) := by
  let Z := ∫ x, Real.exp (u x) ∂μ
  have hZ : 0 < Z := integral_exp_pos hexp
  have hs : Integrable (fun x => rho x*(u x-Real.log Z)) μ := by
    have heq : (fun x => rho x*(u x-Real.log Z)) =
        (fun x => rho x*u x) - (fun x => rho x*Real.log Z) := by
      funext x
      exact mul_sub _ _ _
    rw [heq]
    exact hprod.sub (hr.mul_const (Real.log Z))
  have hn : Integrable (fun x => Real.exp (u x-Real.log Z)) μ := by
    simpa only [Real.exp_sub, Real.exp_log hZ, div_eq_mul_inv] using hexp.mul_const Z⁻¹
  have hnm : (∫ x, Real.exp (u x-Real.log Z) ∂μ) = 1 := by
    simp only [Real.exp_sub, Real.exp_log hZ, div_eq_mul_inv, integral_mul_const]
    exact mul_inv_cancel₀ hZ.ne'
  have hsi : (∫ x, rho x*(u x-Real.log Z) ∂μ) =
      (∫ x, rho x*u x ∂μ) - Real.log Z := by
    simp only [mul_sub]
    rw [integral_sub hprod (hr.mul_const _), integral_mul_const, hmass, one_mul]
  have hp : (fun x => rho x*(u x-Real.log Z)) ≤ᵐ[μ]
      (fun x => rho x*Real.log (rho x)-rho x+Real.exp (u x-Real.log Z)) := by
    filter_upwards [hnonneg] with x hx
    exact entropy_young _ _ hx
  have hi : (∫ x, rho x*(u x-Real.log Z) ∂μ) =
      ∫ x, rho x*Real.log (rho x)-rho x+Real.exp (u x-Real.log Z) ∂μ := by
    have hgs : Integrable (fun x => rho x*Real.log (rho x)-rho x) μ := hent.sub hr
    rw [hsi, integral_add hgs hn, integral_sub hent hr, hmass, hnm]
    change _ = (∫ x, rho x*Real.log (rho x) ∂μ)-1+1
    rw [he]
    ring
  have hae := (integral_eq_iff_of_ae_le hs ((hent.sub hr).add hn) hp).mp hi
  filter_upwards [hnonneg, hae] with x hx heq
  have h := (entropy_young_eq_iff hx).mp heq
  simpa only [Real.exp_sub, Real.exp_log hZ] using h

theorem entropy_eq_zero_iff {d : ℕ} (r : ProbabilityDensity d) (hr : r.FiniteEntropy) :
    densityEntropy r.value = 0 ↔ r.value =ᵐ[torusMeasure d] (fun _ => 1) := by
  constructor
  · intro he
    have hprod : Integrable (fun x => r.value x*(0:ℝ)) (torusMeasure d) := by simp
    have hexp : Integrable (fun _ : Torus d => Real.exp (0:ℝ)) (torusMeasure d) := integrable_const _
    have he' : (∫ x, r.value x*Real.log (r.value x) ∂torusMeasure d) =
        (∫ x, r.value x*(0:ℝ) ∂torusMeasure d) -
          Real.log (∫ _ : Torus d, Real.exp (0:ℝ) ∂torusMeasure d) := by
      simpa [densityEntropy] using he
    simpa using eq_normalized_exp_of_variational_eq r.nonneg r.mass r.integrable hr hprod hexp he'
  · intro he
    unfold densityEntropy
    calc
      _ = ∫ _ : Torus d, (1:ℝ)*Real.log 1 ∂torusMeasure d := by
        apply integral_congr_ae
        filter_upwards [he] with x hx
        rw [hx]
      _ = 0 := by simp

#print axioms eq_normalized_exp_of_variational_eq
#print axioms entropy_eq_zero_iff
end Legacy.BecknerOnofri.EntropyVariationalEquality
