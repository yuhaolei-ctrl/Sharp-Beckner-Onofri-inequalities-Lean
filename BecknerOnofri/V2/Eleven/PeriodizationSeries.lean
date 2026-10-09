module

public import BecknerOnofri.V2.Eleven.ProfileDecay
public import BecknerOnofri.V2.Eleven.SeriesSmooth
public import BecknerOnofri.ElevenPeriodizedContinuity
public import BecknerOnofri.ElevenPeriodizedMass

@[expose] public section

/-! # Lemma 4.3, first paragraph: every differentiated periodization series converges locally
uniformly, and `ρ_*` is smooth, strictly positive, of mass one

Source: `lem:section4-periodization-entropy-identity`, proof, `eq:section4-periodization-M-test`.
The Weierstrass M-test is carried out for the series of `k`-th derivatives of the translates
`y ↦ η_{1/5}(y+n)`, `n ∈ ℤ^{11}`, with an explicit summable majorant coming from
`eq:section4-profile-derivative-decay` (`ProfileDecay.lean`).  The route differs from the existing
`Eleven.periodizedProfile_smooth`, which proves smoothness from exponential Fourier decay; here the
differentiated series themselves are shown to converge. -/

noncomputable section
open scoped ContDiff
open BecknerOnofri.HighDim BecknerOnofri.HighDim.Eleven
open Legacy.TorusEndpoint.GreenMultiplierSummability

namespace BecknerOnofri.V2.Eleven

/-- The lattice vector `n ∈ ℤ^{11}` as an element of `ℝ^{11}`. -/
def shift11 (n : Frequency 11) : Fin 11 → ℝ := fun i => (n i : ℝ)

/-- The translate `y ↦ η_{1/5}(y + n)`. -/
def termProfile (n : Frequency 11) (y : Fin 11 → ℝ) : ℝ := euclideanProfile (y + shift11 n)

/-- The periodization on `ℝ^{11}`: `ρ_*(y) = ∑_{n ∈ ℤ^{11}} η_{1/5}(y+n)` (`eq:section4-rho-star`). -/
def periodization11 (y : Fin 11 → ℝ) : ℝ := ∑' n : Frequency 11, termProfile n y

lemma periodizedProfile_lift' (y : Fin 11 → ℝ) :
    periodizedProfile (fun i => (y i : UnitAddCircle)) = periodization11 y :=
  periodizedProfile_lift y

lemma termProfile_contDiff (n : Frequency 11) : ContDiff ℝ ∞ (termProfile n) :=
  profile_contDiff.comp (contDiff_id.add contDiff_const)

/-- The weights `(1+‖n‖)^{-22}` are summable over `ℤ^{11}`. -/
lemma shift_weight_le (n : Frequency 11) :
    (1 + ‖shift11 n‖) ^ (-22 : ℤ) ≤ 11 ^ 11 * productMajorant n := by
  set N : ℝ := ‖shift11 n‖ with hN
  have hN0 : 0 ≤ N := norm_nonneg _
  have hrad : radiusSq n ≤ 11 * N ^ 2 := by
    unfold radiusSq
    calc ∑ j : Fin 11, (n j : ℝ) ^ 2 ≤ ∑ _j : Fin 11, N ^ 2 := by
          refine Finset.sum_le_sum fun j _ => ?_
          have : |(n j : ℝ)| ≤ N := by
            simpa [shift11, Real.norm_eq_abs] using norm_le_pi_norm (shift11 n) j
          exact sq_le_sq' (by linarith [abs_nonneg (n j : ℝ), neg_abs_le (n j : ℝ)]) (le_trans (le_abs_self _) this)
      _ = 11 * N ^ 2 := by simp
  have h1 : 1 + radiusSq n ≤ 11 * (1 + N) ^ 2 := by nlinarith
  have hpos : 0 < 1 + radiusSq n := by have := radiusSq_nonneg n; positivity
  have h2 : ((1 + radiusSq n)⁻¹) ^ 11 ≤ productMajorant n := shifted_radial_inv_le_product n
  have h3 : (1 + N) ^ (-22 : ℤ) ≤ 11 ^ 11 * ((1 + radiusSq n)⁻¹) ^ 11 := by
    have hw : 0 < 1 + N := by linarith
    have e : (1 + N) ^ (-22 : ℤ) = (((1 + N) ^ 2)⁻¹) ^ 11 := by
      rw [zpow_neg, ← inv_pow, ← pow_mul]
      norm_num
    rw [e]
    have : ((1 + N) ^ 2)⁻¹ ≤ 11 * (1 + radiusSq n)⁻¹ := by
      rw [← one_div, ← div_eq_mul_inv, div_le_div_iff₀ (by positivity) hpos]
      nlinarith
    calc (((1 + N) ^ 2)⁻¹) ^ 11 ≤ (11 * (1 + radiusSq n)⁻¹) ^ 11 :=
          pow_le_pow_left₀ (by positivity) this 11
      _ = 11 ^ 11 * ((1 + radiusSq n)⁻¹) ^ 11 := mul_pow _ _ _
  calc (1 + N) ^ (-22 : ℤ) ≤ 11 ^ 11 * ((1 + radiusSq n)⁻¹) ^ 11 := h3
    _ ≤ 11 ^ 11 * productMajorant n := mul_le_mul_of_nonneg_left h2 (by positivity)

lemma summable_shift_weight :
    Summable (fun n : Frequency 11 => (1 + ‖shift11 n‖) ^ (-22 : ℤ)) :=
  Summable.of_nonneg_of_le (fun _ => (zpow_pos (one_add_norm_pos _) _).le) shift_weight_le
    ((summable_productMajorant 11).mul_left _)

/-- The M-test majorants: for all radii `R` and derivative orders `k`. -/
theorem translate_derivative_bound {R : ℝ} (hR : 0 ≤ R) (k : ℕ) :
    ∃ v : Frequency 11 → ℝ, Summable v ∧ ∀ (n : Frequency 11) (y : Fin 11 → ℝ), ‖y‖ ≤ R →
      ‖iteratedFDeriv ℝ k (termProfile n) y‖ ≤ v n := by
  obtain ⟨C, hC0, hC⟩ := profile_derivative_decay k
  refine ⟨fun n => C * (1 + R) ^ 22 * (1 + ‖shift11 n‖) ^ (-22 : ℤ),
    (summable_shift_weight.mul_left _), fun n y hy => ?_⟩
  have e : iteratedFDeriv ℝ k (termProfile n) y = iteratedFDeriv ℝ k euclideanProfile (y + shift11 n) :=
    iteratedFDeriv_comp_add_right k (shift11 n) y
  rw [e]
  refine (hC _).trans ?_
  set a := shift11 n with ha
  have hw : 0 < 1 + ‖y + a‖ := one_add_norm_pos _
  have hwa : 0 < 1 + ‖a‖ := one_add_norm_pos _
  -- `1 + ‖a‖ ≤ (1 + R)(1 + ‖y + a‖)`
  have hle : 1 + ‖a‖ ≤ (1 + R) * (1 + ‖y + a‖) := by
    have h1 : ‖a‖ ≤ ‖y + a‖ + ‖y‖ := by
      calc ‖a‖ = ‖(y + a) - y‖ := by simp
        _ ≤ ‖y + a‖ + ‖y‖ := norm_sub_le _ _
    nlinarith [norm_nonneg (y + a), norm_nonneg y]
  have hk : (1 + ‖y + a‖) ^ (-22 - (k : ℤ)) ≤ (1 + ‖y + a‖) ^ (-22 : ℤ) :=
    zpow_le_zpow_right₀ (one_le_one_add_norm _) (by omega)
  have hinv : (1 + ‖y + a‖) ^ (-22 : ℤ) ≤ (1 + R) ^ 22 * (1 + ‖a‖) ^ (-22 : ℤ) := by
    have e22 : ((-22 : ℤ)) = -((22 : ℕ) : ℤ) := by norm_num
    have e1 : (1 + ‖y + a‖) ^ (-22 : ℤ) = (((1 + ‖y + a‖))⁻¹) ^ 22 := by
      rw [e22, zpow_neg, zpow_natCast, inv_pow]
    have e2 : (1 + ‖a‖) ^ (-22 : ℤ) = (((1 + ‖a‖))⁻¹) ^ 22 := by
      rw [e22, zpow_neg, zpow_natCast, inv_pow]
    rw [e1, e2, ← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    have hR1 : 0 < 1 + R := by linarith
    calc (1 + ‖y + a‖)⁻¹ = (1 + R) * (((1 + R) * (1 + ‖y + a‖))⁻¹) := by field_simp
      _ ≤ (1 + R) * (1 + ‖a‖)⁻¹ := mul_le_mul_of_nonneg_left (inv_anti₀ hwa hle) hR1.le
  calc C * (1 + ‖y + a‖) ^ (-22 - (k : ℤ)) ≤ C * (1 + ‖y + a‖) ^ (-22 : ℤ) :=
        mul_le_mul_of_nonneg_left hk hC0
    _ ≤ C * ((1 + R) ^ 22 * (1 + ‖a‖) ^ (-22 : ℤ)) := mul_le_mul_of_nonneg_left hinv hC0
    _ = C * (1 + R) ^ 22 * (1 + ‖shift11 n‖) ^ (-22 : ℤ) := by rw [ha]; ring

/-- `eq:section4-periodization-M-test` for every derivative order, with explicit summable
majorants on every ball. -/
theorem periodization_M_test : ∀ R : ℝ, 0 ≤ R → ∀ k : ℕ, ∃ v : Frequency 11 → ℝ, Summable v ∧
    ∀ (n : Frequency 11) (y : Fin 11 → ℝ), ‖y‖ ≤ R →
      ‖iteratedFDeriv ℝ k (termProfile n) y‖ ≤ v n :=
  fun _ hR k => translate_derivative_bound hR k

/-- The periodization is `C^∞` on `ℝ^{11}`. -/
theorem periodization11_contDiff : ContDiff ℝ ∞ periodization11 :=
  (tsum_contDiff_of_local_bounds termProfile_contDiff periodization_M_test).1

/-- The `k`-th derivative of the periodization is the (locally uniformly convergent) sum of the
`k`-th derivatives of the translates. -/
theorem periodization11_iteratedFDeriv_hasSum (k : ℕ) (y : Fin 11 → ℝ) :
    HasSum (fun n : Frequency 11 => iteratedFDeriv ℝ k (termProfile n) y)
      (iteratedFDeriv ℝ k periodization11 y) :=
  tsum_iteratedFDeriv_hasSum termProfile_contDiff periodization_M_test k y

theorem periodization11_iteratedFDeriv_tendstoUniformlyOn (k : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    TendstoUniformlyOn
      (fun s : Finset (Frequency 11) => fun y => ∑ n ∈ s, iteratedFDeriv ℝ k (termProfile n) y)
      (iteratedFDeriv ℝ k periodization11) Filter.atTop (Metric.closedBall (0 : Fin 11 → ℝ) R) :=
  tsum_iteratedFDeriv_tendstoUniformlyOn termProfile_contDiff periodization_M_test k hR

/-- `ρ_*` is smooth on the torus (as a periodic function on `ℝ^{11}`). -/
theorem periodizedProfile_smooth_of_M_test : SmoothOnTorus periodizedProfile := by
  have : (fun x : Fin 11 → ℝ => periodizedProfile (fun j => (x j : UnitAddCircle))) = periodization11 :=
    funext periodizedProfile_lift'
  unfold SmoothOnTorus
  rw [this]
  exact periodization11_contDiff

/-- Lemma 4.3, first paragraph, collected: convergence of all differentiated series (M-test and
locally uniform convergence), smoothness, strict positivity, integrability and mass one of `ρ_*`. -/
theorem lemma43_regularity :
    (∀ R : ℝ, 0 ≤ R → ∀ k : ℕ, ∃ v : Frequency 11 → ℝ, Summable v ∧
      ∀ (n : Frequency 11) (y : Fin 11 → ℝ), ‖y‖ ≤ R →
        ‖iteratedFDeriv ℝ k (termProfile n) y‖ ≤ v n) ∧
    (∀ (k : ℕ) {R : ℝ}, 0 ≤ R → TendstoUniformlyOn
      (fun s : Finset (Frequency 11) => fun y => ∑ n ∈ s, iteratedFDeriv ℝ k (termProfile n) y)
      (iteratedFDeriv ℝ k periodization11) Filter.atTop (Metric.closedBall (0 : Fin 11 → ℝ) R)) ∧
    SmoothOnTorus periodizedProfile ∧ (∀ x : Torus 11, 0 < periodizedProfile x) ∧
    MeasureTheory.Integrable periodizedProfile (torusMeasure 11) ∧
    (∫ x, periodizedProfile x ∂torusMeasure 11) = 1 :=
  ⟨periodization_M_test, fun k _ hR => periodization11_iteratedFDeriv_tendstoUniformlyOn k hR,
    periodizedProfile_smooth_of_M_test, periodizedProfile_pos, periodizedProfile_integrable,
    periodizedProfile_integral⟩

end BecknerOnofri.V2.Eleven
