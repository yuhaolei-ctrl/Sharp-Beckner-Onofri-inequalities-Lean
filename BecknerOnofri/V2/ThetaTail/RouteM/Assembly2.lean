module

public import BecknerOnofri.V2.ThetaTail.RouteM.Assembly
public import BecknerOnofri.V2.ThetaTail.Defs

@[expose] public section

/-! # Route M, part M4 (B): from the modular identities to `TwelveSquareIdentity`

`twelve_square_routeM : TwelveSquareIdentity`, UNCONDITIONAL (axioms: standard three only),
proved by **Route M** (modular-form uniqueness), *not* by the Weierstrass route written in
Appendix A.1.  Differences from the written proof (all other displayed equations are proved in
the same form):

* `(d12-tail-eq:E6theta)` is `RouteM.E6_theta`, proved via `levelOne_weight_six_rank_one`
  (not DLMF 23.8.1, 23.9.2/4, 23.6.2-4, 23.3.7, 20.7.5);
* `16 η(2τ)¹² = a²b²(a²−b²)` is obtained via `CuspForm.exists_smul_discriminant_of_weight_eq_twelve`
  and Mathlib's product formula for `Δ` (not DLMF 20.4.2, 20.4.6), with the sign of the fourth
  root fixed by positivity on the imaginary axis (`theta_eta_product`);
* the theta reduction identities (DLMF 20.7.12, 20.7.14 in the manuscript) are `RouteM.Duplication`;
* the Lambert/geometric-denominator step is replaced by Mathlib's σ-series of `E₆`
  (`EisensteinSeries.q_expansion_bernoulli` + `E₆_qExpansion_coeff_one`), see `E6_qexp`;
  the standalone conversion `∑ n⁵qⁿ/(1−qⁿ) = ∑ σ₅(m)q^m` is `lambert_conversion`. -/
noncomputable section
open Complex Filter Topology SlashInvariantForm ModularForm EisensteinSeries
open UpperHalfPlane hiding I
open scoped Real MatrixGroups ModularForm ArithmeticFunction.sigma
namespace BecknerOnofri.V2.ThetaTail.RouteM

/-- `E₆(τ) = 1 − 504 ∑_{n≥1} σ₅(n) e^{2πinτ}` (Mathlib's Bernoulli form, with the constant
`2·6/B₆ = 504` read off from `E₆_qExpansion_coeff_one`). -/
theorem E6_qexp (s : ℍ) :
    (E₆ : ℍ → ℂ) s = 1 - 504 * ∑' n : ℕ+, ((ArithmeticFunction.sigma 5 n : ℕ) : ℂ) *
      cexp (2 * π * Complex.I * s) ^ (n : ℕ) := by
  have hb := EisensteinSeries.q_expansion_bernoulli (k := 6) (by norm_num) ⟨3, rfl⟩ s
  have hc := EisensteinSeries.E_qExpansion_coeff (k := 6) (by norm_num) ⟨3, rfl⟩ 1
  have h1 := ModularForm.E₆_qExpansion_coeff_one
  have h2 := hc.symm.trans h1
  simp only [one_ne_zero, ite_false, ArithmeticFunction.sigma_apply, Nat.divisors_one,
    Finset.sum_singleton] at h2
  have key : (2 * ((6 : ℕ) : ℂ) / (bernoulli 6 : ℂ)) = 504 := by
    norm_num at h2
    linear_combination h2
  have e : ((E₆ : ℍ → ℂ) s) = (E (by norm_num : 3 ≤ 6)) s := rfl
  rw [e, hb, key]
  simp [zpow_natCast]

/-! ### The imaginary-axis point `z_q = i(−log q)/π` -/

/-- the point with `e^{πi z_q} = q` -/
def zq (q : ℝ) : ℂ := Complex.I * ((-Real.log q / π : ℝ) : ℂ)

lemma zq_re (q : ℝ) : (zq q).re = 0 := by simp [zq]

lemma zq_im {q : ℝ} (h0 : 0 < q) (h1 : q < 1) : 0 < (zq q).im := by
  have : Real.log q < 0 := Real.log_neg h0 h1
  have h : 0 < -Real.log q / π := div_pos (by linarith) Real.pi_pos
  simpa [zq] using h

lemma cexp_pi_I_zq {q : ℝ} (h0 : 0 < q) : cexp (π * Complex.I * zq q) = (q : ℂ) := by
  have : (π * Complex.I * zq q : ℂ) = ((Real.log q : ℝ) : ℂ) := by
    unfold zq
    push_cast
    field_simp
    rw [Complex.I_sq]; ring
  rw [this, ← Complex.ofReal_exp, Real.exp_log h0]

lemma cexp_nat_zq {q : ℝ} (h0 : 0 < q) (k : ℕ) :
    cexp ((k : ℂ) * (π * Complex.I * zq q)) = (q : ℂ) ^ k := by
  rw [Complex.exp_nat_mul, cexp_pi_I_zq h0]

lemma cexp_int_zq {q : ℝ} (h0 : 0 < q) (k : ℤ) :
    cexp ((k : ℂ) * (π * Complex.I * zq q)) = (q : ℂ) ^ k := by
  rw [Complex.exp_int_mul, cexp_pi_I_zq h0]

/-- `ϑ₃(z_q) = θ(q)` -/
theorem jt3_zq {q : ℝ} (h0 : 0 < q) : jt3 (zq q) = ((theta q : ℝ) : ℂ) := by
  rw [jt3_eq_tsum, theta, Complex.ofReal_tsum]
  refine tsum_congr fun n => ?_
  unfold tA
  have := cexp_int_zq h0 (n ^ 2)
  push_cast at this
  rw [show π * Complex.I * (n : ℂ) ^ 2 * zq q = (n : ℂ) ^ 2 * (π * Complex.I * zq q) by ring, this]
  push_cast; rfl

/-! ### Reality on the imaginary axis -/

lemma neg_conj_of_re_zero {τ : ℂ} (h : τ.re = 0) : -(starRingEnd ℂ) τ = τ := by
  apply Complex.ext <;> simp [h]

lemma jt3_real {τ : ℂ} (h : τ.re = 0) : ∃ r : ℝ, jt3 τ = r := by
  refine Complex.conj_eq_iff_real.1 ?_
  unfold jt3
  rw [jacobiTheta₂_conj, neg_conj_of_re_zero h]
  simp

lemma jt4_real {τ : ℂ} (h : τ.re = 0) : ∃ r : ℝ, jt4 τ = r := by
  refine Complex.conj_eq_iff_real.1 ?_
  unfold jt4
  rw [jacobiTheta₂_conj, neg_conj_of_re_zero h]
  have : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by
    have e : (1 / 2 : ℂ) = (((1 / 2 : ℝ)) : ℂ) := by push_cast; ring
    rw [e, Complex.conj_ofReal]
  rw [this]

lemma jt2_real {τ : ℂ} (h : τ.re = 0) : ∃ r : ℝ, jt2 τ = r := by
  refine Complex.conj_eq_iff_real.1 ?_
  unfold jt2
  rw [jacobiTheta₂_conj, neg_conj_of_re_zero h]
  have : (starRingEnd ℂ) (τ / 2) = -(τ / 2) := by
    have h2 : (starRingEnd ℂ) τ = -τ := by apply Complex.ext <;> simp [h]
    rw [map_div₀, h2]
    simp [map_ofNat]
    ring
  rw [this, jacobiTheta₂_neg_left]

/-! ### The Euler product -/

lemma multipliable_g {q : ℝ} (h0 : 0 ≤ q) (h1 : q < 1) :
    Multipliable (fun n : ℕ => 1 - q ^ (2 * (n + 1))) := by
  have hq2 : q ^ 2 < 1 := by nlinarith
  have hsum : Summable (fun n : ℕ => -q ^ (2 * (n + 1))) := by
    have : Summable (fun n : ℕ => (q ^ 2) ^ (n + 1)) :=
      (summable_nat_add_iff 1).2 (summable_geometric_of_lt_one (sq_nonneg q) hq2)
    simpa [pow_mul] using this.neg
  have := Real.multipliable_one_add_of_summable hsum
  simpa [sub_eq_add_neg] using this

lemma ofReal_tprod_g {q : ℝ} (h0 : 0 ≤ q) (h1 : q < 1) :
    ((∏' n : ℕ, (1 - q ^ (2 * (n + 1))) : ℝ) : ℂ) =
      ∏' n : ℕ, (((1 - q ^ (2 * (n + 1)) : ℝ)) : ℂ) :=
  ((multipliable_g h0 h1).hasProd.map Complex.ofRealHom Complex.continuous_ofReal).tprod_eq.symm

lemma multipliable_gc {q : ℝ} (h0 : 0 ≤ q) (h1 : q < 1) :
    Multipliable (fun n : ℕ => (((1 - q ^ (2 * (n + 1)) : ℝ)) : ℂ)) :=
  ((multipliable_g h0 h1).hasProd.map Complex.ofRealHom Complex.continuous_ofReal).multipliable

/-- **M2 on the imaginary axis**: `16 η(2τ)¹² = ϑ₂⁴ϑ₃⁴ϑ₄⁴(2τ)` where `e^{2πiτ} = q`, i.e.
`F₂F₃F₄(z_q) = 16 q ∏_{m≥1}(1−q^{2m})¹²` (positive-real form). -/
theorem theta_eta_product {q : ℝ} (h0 : 0 < q) (h1 : q < 1) :
    F2 (zq q) * F3 (zq q) * F4 (zq q) =
      (q : ℂ) * (16 * (((∏' n : ℕ, (1 - q ^ (2 * (n + 1)))) ^ 12 : ℝ) : ℂ)) := by
  have hzim := zq_im h0 h1
  set z := zq q with hz
  set Pr : ℝ := ∏' n : ℕ, (1 - q ^ (2 * (n + 1))) with hPr
  have hH : Hfun z = 256 * ∏' n : ℕ, (1 - cexp (2 * π * Complex.I * ((n : ℂ) + 1) * z)) ^ 24 :=
    Hfun_eq_prod ⟨z, hzim⟩
  have hcexp : ∀ n : ℕ, cexp (2 * π * Complex.I * ((n : ℂ) + 1) * z) =
      (((q ^ (2 * (n + 1)) : ℝ)) : ℂ) := by
    intro n
    have := cexp_nat_zq h0 (2 * (n + 1))
    push_cast at this ⊢
    rw [← this]; congr 1; ring
  have hprod : ∏' n : ℕ, (1 - cexp (2 * π * Complex.I * ((n : ℂ) + 1) * z)) ^ 24 =
      ((Pr ^ 24 : ℝ) : ℂ) := by
    have e1 : ∀ n : ℕ, (1 - cexp (2 * π * Complex.I * ((n : ℂ) + 1) * z)) =
        (((1 - q ^ (2 * (n + 1)) : ℝ)) : ℂ) := by
      intro n; rw [hcexp n]; push_cast; ring
    simp_rw [e1]
    rw [(multipliable_gc h0.le h1).tprod_pow, ← ofReal_tprod_g h0.le h1]
    push_cast; rfl
  rw [hprod] at hH
  obtain ⟨r2, hr2⟩ := jt2_real (τ := z) (zq_re q)
  obtain ⟨r3, hr3⟩ := jt3_real (τ := z) (zq_re q)
  obtain ⟨r4, hr4⟩ := jt4_real (τ := z) (zq_re q)
  have hX : Hfun z = (((r2 * r3 * r4) ^ 8 : ℝ) : ℂ) := by
    unfold Hfun; rw [hr2, hr3, hr4]; push_cast; rfl
  rw [hX] at hH
  have hreal : (r2 * r3 * r4) ^ 8 = 256 * Pr ^ 24 := by exact_mod_cast hH
  have h4 : (r2 * r3 * r4) ^ 4 = 16 * Pr ^ 12 := by
    have hsq : ((r2 * r3 * r4) ^ 4) ^ 2 = (16 * Pr ^ 12) ^ 2 := by
      have a : ((r2 * r3 * r4) ^ 4) ^ 2 = (r2 * r3 * r4) ^ 8 := by ring
      have b : (16 * Pr ^ 12) ^ 2 = 256 * Pr ^ 24 := by ring
      rw [a, b, hreal]
    exact (sq_eq_sq₀ (by positivity) (by positivity)).1 hsq
  have : F2 z * F3 z * F4 z = cexp (π * Complex.I * z) * (jt2 z * jt3 z * jt4 z) ^ 4 := by
    unfold F2 F3 F4; ring
  rw [this, cexp_pi_I_zq h0, hr2, hr3, hr4]
  have e : ((r2 : ℂ) * r3 * r4) ^ 4 = (((r2 * r3 * r4) ^ 4 : ℝ) : ℂ) := by push_cast; rfl
  rw [e, h4]
  push_cast; ring

end BecknerOnofri.V2.ThetaTail.RouteM
