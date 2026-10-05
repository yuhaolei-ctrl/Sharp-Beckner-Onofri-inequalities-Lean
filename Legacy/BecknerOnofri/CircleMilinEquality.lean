import Legacy.BecknerOnofri.CircleMilinVariance
import Mathlib.Topology.Algebra.InfiniteSum.Order

noncomputable section
open scoped BigOperators
open Filter
namespace Legacy.BecknerOnofri.CircleMilin

/-- Equality of the total coefficient masses forces equality at every degree.
This uses the actual termwise coefficient bound, not an equality premise on
individual coefficients. -/
theorem coefficient_equality_of_equal_mass (a : ℕ → ℂ)
    (hp : Summable (pCoeff a)) (hb : Summable (fun n => ‖bCoeff a n‖^2))
    (he : (∑' n,pCoeff a n) = ∑' n,‖bCoeff a n‖^2) (n : ℕ) :
    pCoeff a n = ‖bCoeff a n‖^2 := by
  have hs := hp.sub hb
  have hzero : (∑' n,(pCoeff a n-‖bCoeff a n‖^2)) = 0 := by
    rw [hp.tsum_sub hb,he,sub_self]
  have hle := hs.le_tsum n (fun m hm => sub_nonneg.mpr (coefficient_sq_le a m))
  rw [hzero] at hle
  exact le_antisymm (sub_nonpos.mp hle) (coefficient_sq_le a n)

theorem recurrence_of_equal_mass (a : ℕ → ℂ)
    (hp : Summable (pCoeff a)) (hb : Summable (fun n => ‖bCoeff a n‖^2))
    (he : (∑' n,pCoeff a n) = ∑' n,‖bCoeff a n‖^2) {n : ℕ} (hn : 0 < n) :
    (n : ℂ)*a n = a 1^n :=
  coefficient_equality_recurrence a hn (coefficient_equality_of_equal_mass a hp hb he n)

/-- Smooth Fourier decay excludes the boundary of the parameter disk. -/
theorem norm_first_lt_one_of_recurrence (a : ℕ → ℂ)
    (hrec : ∀ n : ℕ,0<n → (n : ℂ)*a n = a 1^n)
    (hdecay : Tendsto (fun n : ℕ => (n : ℂ)*a n) atTop (nhds 0)) : ‖a 1‖ < 1 := by
  by_contra hn
  have hnorm : 1 ≤ ‖a 1‖ := le_of_not_gt hn
  have hlim := hdecay.norm
  have hlower : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ ‖(n : ℂ)*a n‖ := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [hrec n (by omega),norm_pow]
    exact one_le_pow₀ hnorm
  have hle : (1 : ℝ) ≤ 0 := by
    simpa only [norm_zero] using ge_of_tendsto hlim hlower
  norm_num at hle

/-- The full reverse coefficient classification follows from the actual
exponential mass identity and Fourier decay. -/
theorem coefficients_of_equal_mass (a : ℕ → ℂ)
    (hp : Summable (pCoeff a)) (hb : Summable (fun n => ‖bCoeff a n‖^2))
    (he : (∑' n,pCoeff a n) = ∑' n,‖bCoeff a n‖^2)
    (hdecay : Tendsto (fun n : ℕ => (n : ℂ)*a n) atTop (nhds 0)) :
    ‖a 1‖ < 1 ∧ ∀ n,0<n → a n = a 1^n/(n : ℂ) := by
  have hrec : ∀ n : ℕ,0<n → (n : ℂ)*a n = a 1^n :=
    fun n hn => recurrence_of_equal_mass a hp hb he hn
  refine ⟨norm_first_lt_one_of_recurrence a hrec hdecay,?_⟩
  intro n hn
  apply (eq_div_iff (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn))).mpr
  simpa [mul_comm] using hrec n hn

#print axioms coefficients_of_equal_mass
end Legacy.BecknerOnofri.CircleMilin
