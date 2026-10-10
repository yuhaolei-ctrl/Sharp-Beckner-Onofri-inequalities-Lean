module

public import BecknerOnofri.V2.Eleven.Estimates

@[expose] public section

/-! # S029: the Bessel layer of `lem:section4-profile-fourier-transform`

The printed proof of `eq:section4-eta-fourier-transform` goes through the modified Bessel function of the
second kind: for `ξ ≠ 0`,

  `η̂(ξ) = (1/Γ(11/2)) ∫_0^∞ t^{9/2} e^{-t-π²|ξ|²/t} dt = 2(π|ξ|)^{11/2}/Γ(11/2) · K_{11/2}(2π|ξ|)`
  (`eq:section4-bessel-transform`), with `K_{n+1/2}(z) = (π/(2z))^{1/2} e^{-z} ∑_{j=0}^n (n+j)!/(j!(n-j)!(2z)^j)`
  (`eq:section4-half-integer-bessel`), and `n = 5` gives `Φ(2π|ξ|)`.

Mathlib has no `K_ν`.  Here `besselK ν z = ∫_0^∞ e^{-z cosh t} cosh(νt) dt` is *defined* by the standard
integral (DLMF 10.32.9), and DLMF 10.32.10 (`besselK_eq_integral`, for the orders and arguments used, with
the integrability hypothesis made explicit) is proved from it by the substitution `s = (z/2) e^t`.  The
half-integer formula is proved for `n = 5` only (`besselK_half_eleven`), not for general `n`. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace BecknerOnofri.V2.Reaudit.ElevenBounds

/-- The modified Bessel function of the second kind, `K_ν(z) = ∫_0^∞ e^{-z cosh t} cosh(νt) dt`
(DLMF 10.32.9), for `z > 0`. -/
def besselK (ν z : ℝ) : ℝ := ∫ t in Ioi (0 : ℝ), Real.exp (-z * Real.cosh t) * Real.cosh (ν * t)

/-- The integrand of DLMF 10.32.10: `s^{ν-1} e^{-s-z²/(4s)}`. -/
def besselKernel (ν z s : ℝ) : ℝ := s ^ (ν - 1) * Real.exp (-s - z ^ 2 / (4 * s))

/-- The integrand of the integral representation on the whole line: `e^{νt - z cosh t}`. -/
def coshKernel (ν z t : ℝ) : ℝ := Real.exp (ν * t) * Real.exp (-z * Real.cosh t)

theorem coshKernel_eq (ν z t : ℝ) : coshKernel ν z t = Real.exp (ν * t - z * Real.cosh t) := by
  rw [coshKernel, ← Real.exp_add]; ring_nf

theorem besselKernel_comp {ν z : ℝ} (hz : 0 < z) (t : ℝ) :
    besselKernel ν z (z / 2 * Real.exp t) * (z / 2 * Real.exp t) =
      (z / 2) ^ ν * coshKernel ν z t := by
  have ha : 0 < z / 2 := by positivity
  have he := Real.exp_pos t
  have h1 : (z / 2 * Real.exp t) ^ (ν - 1) * (z / 2 * Real.exp t) = (z / 2 * Real.exp t) ^ ν := by
    rw [← Real.rpow_add_one (by positivity), sub_add_cancel]
  have h2 : -(z / 2 * Real.exp t) - z ^ 2 / (4 * (z / 2 * Real.exp t)) = -z * Real.cosh t := by
    rw [Real.cosh_eq]
    field_simp
    rw [Real.exp_neg]
    field_simp
    ring
  unfold besselKernel coshKernel
  rw [h2]
  calc (z / 2 * Real.exp t) ^ (ν - 1) * Real.exp (-z * Real.cosh t) * (z / 2 * Real.exp t)
      = ((z / 2 * Real.exp t) ^ (ν - 1) * (z / 2 * Real.exp t)) * Real.exp (-z * Real.cosh t) := by ring
    _ = _ := by
      rw [h1, Real.mul_rpow ha.le he.le, ← Real.exp_mul, mul_comm t ν]
      ring


theorem image_exp_mul {a : ℝ} (ha : 0 < a) : (fun t : ℝ => a * Real.exp t) '' univ = Ioi 0 := by
  ext y
  simp only [mem_image, mem_univ, true_and, mem_Ioi]
  constructor
  · rintro ⟨t, rfl⟩
    positivity
  · intro hy
    exact ⟨Real.log (y / a), by rw [Real.exp_log (div_pos hy ha)]; field_simp⟩

theorem injective_exp_mul {a : ℝ} (ha : 0 < a) : Function.Injective (fun t : ℝ => a * Real.exp t) :=
  fun _ _ h => Real.exp_injective (mul_left_cancel₀ ha.ne' h)

theorem hasDerivWithinAt_exp_mul (a t : ℝ) :
    HasDerivWithinAt (fun t : ℝ => a * Real.exp t) (a * Real.exp t) univ t :=
  ((Real.hasDerivAt_exp t).const_mul a).hasDerivWithinAt

theorem abs_smul_besselKernel {ν z : ℝ} (hz : 0 < z) (t : ℝ) :
    |z / 2 * Real.exp t| • besselKernel ν z (z / 2 * Real.exp t) = (z / 2) ^ ν * coshKernel ν z t := by
  rw [abs_of_pos (by positivity), smul_eq_mul, mul_comm]
  exact besselKernel_comp hz t

/-- The substitution `s = (z/2)e^t`: `∫_0^∞ s^{ν-1}e^{-s-z²/(4s)} ds = (z/2)^ν ∫_ℝ e^{νt - z cosh t} dt`. -/
theorem integral_besselKernel {ν z : ℝ} (hz : 0 < z) :
    ∫ s in Ioi (0 : ℝ), besselKernel ν z s = (z / 2) ^ ν * ∫ t, coshKernel ν z t := by
  have ha : 0 < z / 2 := by positivity
  have h := integral_image_eq_integral_abs_deriv_smul (s := (univ : Set ℝ)) MeasurableSet.univ
    (fun t _ => hasDerivWithinAt_exp_mul (z / 2) t) (injective_exp_mul ha).injOn
    (besselKernel ν z)
  rw [image_exp_mul ha] at h
  rw [h, setIntegral_univ]
  simp_rw [abs_smul_besselKernel hz]
  rw [integral_const_mul]

theorem integrableOn_besselKernel_iff {ν z : ℝ} (hz : 0 < z) :
    IntegrableOn (besselKernel ν z) (Ioi 0) ↔ Integrable (coshKernel ν z) := by
  have ha : 0 < z / 2 := by positivity
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul (s := (univ : Set ℝ))
    MeasurableSet.univ (fun t _ => hasDerivWithinAt_exp_mul (z / 2) t) (injective_exp_mul ha).injOn
    (besselKernel ν z)
  rw [image_exp_mul ha] at h
  rw [h, integrableOn_univ]
  simp_rw [abs_smul_besselKernel hz]
  have hp : (z / 2) ^ ν ≠ 0 := (Real.rpow_pos_of_pos ha ν).ne'
  exact integrable_const_mul_iff (IsUnit.mk0 _ hp) _

theorem two_mul_besselK {ν z : ℝ} (hG : Integrable (coshKernel ν z)) :
    ∫ t, coshKernel ν z t = 2 * besselK ν z := by
  have h1 := integral_add_compl (measurableSet_Ioi (a := (0 : ℝ))) hG
  rw [compl_Ioi] at h1
  have h2 : ∫ t in Iic (0 : ℝ), coshKernel ν z t = ∫ t in Ioi (0 : ℝ), coshKernel ν z (-t) := by
    rw [integral_comp_neg_Ioi, neg_zero]
  have hG' : IntegrableOn (fun t => coshKernel ν z (-t)) (Ioi 0) := hG.comp_neg.integrableOn
  rw [← h1, h2, ← integral_add hG.integrableOn hG', besselK, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp only [coshKernel, Real.cosh_neg, Real.cosh_eq (ν * t), mul_neg, Real.exp_neg]
  ring

/-- **DLMF 10.32.10** (here for `K_ν` with the kernel `s^{ν-1}`, i.e. the order `-ν`; recall `K_{-ν} = K_ν`):
`K_ν(z) = ½ (z/2)^{-ν} ∫_0^∞ s^{ν-1} e^{-s-z²/(4s)} ds`, for `z > 0`, whenever the integral converges. -/
theorem besselK_eq_integral {ν z : ℝ} (hz : 0 < z)
    (hint : IntegrableOn (besselKernel ν z) (Ioi 0)) :
    besselK ν z = (1 / 2) * (z / 2) ^ (-ν) * ∫ s in Ioi (0 : ℝ), besselKernel ν z s := by
  have ha : 0 < z / 2 := by positivity
  have hG := (integrableOn_besselKernel_iff hz).mp hint
  rw [integral_besselKernel hz, two_mul_besselK hG, Real.rpow_neg ha.le]
  have hp : (z / 2) ^ ν ≠ 0 := (Real.rpow_pos_of_pos ha ν).ne'
  field_simp


/-! ## The half-integer order `11/2` -/

theorem besselKernel_half_eleven (z s : ℝ) :
    besselKernel (11 / 2) z s = s ^ ((9 : ℝ) / 2) * Real.exp (-s - z ^ 2 / (4 * s)) := by
  unfold besselKernel
  norm_num

theorem integral_besselKernel_half_eleven {z : ℝ} (hz : 0 ≤ z) :
    ∫ s in Ioi (0 : ℝ), besselKernel (11 / 2) z s =
      Real.sqrt Real.pi * Real.exp (-z) *
        (z ^ 5 + 15 * z ^ 4 + 105 * z ^ 3 + 420 * z ^ 2 + 945 * z + 945) / 32 := by
  simp_rw [besselKernel_half_eleven]
  exact ReciprocalGaussian.laplace_half_eleven hz

theorem integrableOn_besselKernel_half_eleven {z : ℝ} (hz : 0 ≤ z) :
    IntegrableOn (besselKernel (11 / 2) z) (Ioi 0) := by
  refine Integrable.of_integral_ne_zero ?_
  rw [integral_besselKernel_half_eleven hz]
  positivity

/-- The finite sum of `eq:section4-half-integer-bessel` for `n = 5`:
`∑_{j=0}^5 (5+j)!/(j!(5-j)!(2z)^j) = P(z)/z^5`. -/
theorem half_integer_sum_five {z : ℝ} (hz : 0 < z) :
    ∑ j ∈ Finset.range 6, ((Nat.factorial (5 + j) : ℕ) : ℝ) /
        ((Nat.factorial j : ℕ) * (Nat.factorial (5 - j) : ℕ) * (2 * z) ^ j) =
      (z ^ 5 + 15 * z ^ 4 + 105 * z ^ 3 + 420 * z ^ 2 + 945 * z + 945) / z ^ 5 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.factorial]
  field_simp
  ring

/-- **`eq:section4-half-integer-bessel` for `n = 5`**:
`K_{11/2}(z) = (π/(2z))^{1/2} e^{-z} ∑_{j=0}^5 (5+j)!/(j!(5-j)!(2z)^j)`, `z > 0`. -/
theorem besselK_half_eleven {z : ℝ} (hz : 0 < z) :
    besselK (11 / 2) z =
      Real.sqrt (Real.pi / (2 * z)) * Real.exp (-z) *
        ∑ j ∈ Finset.range 6, ((Nat.factorial (5 + j) : ℕ) : ℝ) /
          ((Nat.factorial j : ℕ) * (Nat.factorial (5 - j) : ℕ) * (2 * z) ^ j) := by
  have ha : 0 < z / 2 := by positivity
  rw [besselK_eq_integral hz (integrableOn_besselKernel_half_eleven hz.le),
    integral_besselKernel_half_eleven hz.le, half_integer_sum_five hz]
  have hr : (z / 2) ^ (-(11 / 2 : ℝ)) = (2 / z) ^ 5 * Real.sqrt (2 / z) := by
    rw [Real.rpow_neg ha.le, ← Real.inv_rpow ha.le, inv_div,
      show (11 / 2 : ℝ) = ((5 : ℕ) : ℝ) + 1 / 2 by norm_num,
      Real.rpow_add (by positivity), Real.rpow_natCast, ← Real.sqrt_eq_rpow]
  have hs : Real.sqrt (2 / z) = 2 * Real.sqrt (1 / (2 * z)) := by
    rw [show 2 / z = 2 ^ 2 * (1 / (2 * z)) by field_simp,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
  have hp : Real.sqrt (Real.pi / (2 * z)) = Real.sqrt Real.pi * Real.sqrt (1 / (2 * z)) := by
    rw [show Real.pi / (2 * z) = Real.pi * (1 / (2 * z)) by ring, Real.sqrt_mul Real.pi_pos.le]
  rw [hr, hs, hp]
  field_simp
  ring


/-! ## The chain `eq:section4-bessel-transform` -/

theorem gamma_eleven_half : Real.Gamma (11 / 2) = 945 * Real.sqrt Real.pi / 32 := by
  have h1 : ∀ s : ℝ, s ≠ 0 → Real.Gamma (s + 1) = s * Real.Gamma s := fun s hs => Real.Gamma_add_one hs
  have e1 := h1 (9 / 2) (by norm_num)
  have e2 := h1 (7 / 2) (by norm_num)
  have e3 := h1 (5 / 2) (by norm_num)
  have e4 := h1 (3 / 2) (by norm_num)
  have e5 := h1 (1 / 2) (by norm_num)
  norm_num at e1 e2 e3 e4 e5
  rw [Real.Gamma_one_half_eq] at e5
  rw [e1, e2, e3, e4, e5]
  ring

/-- `Φ(z) = (1/Γ(11/2)) ∫_0^∞ t^{9/2} e^{-t-z²/(4t)} dt` (the gamma-integral formula and the
half-integer Laplace evaluation), `z ≥ 0`. -/
theorem Phi_eq_laplace {z : ℝ} (hz : 0 ≤ z) :
    BecknerOnofri.V2.Eleven.Phi z =
      (1 / Real.Gamma (11 / 2)) *
        ∫ t in Ioi (0 : ℝ), t ^ ((9 : ℝ) / 2) * Real.exp (-t - z ^ 2 / (4 * t)) := by
  rw [ReciprocalGaussian.laplace_half_eleven hz, gamma_eleven_half]
  have hs : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  unfold BecknerOnofri.V2.Eleven.Phi HighDim.Eleven.fourierProfile HighDim.Eleven.fourierPolynomial
  field_simp

/-- `Φ(z) = 2(z/2)^{11/2}/Γ(11/2) · K_{11/2}(z)`, `z > 0`. -/
theorem Phi_eq_bessel {z : ℝ} (hz : 0 < z) :
    BecknerOnofri.V2.Eleven.Phi z =
      2 * (z / 2) ^ ((11 : ℝ) / 2) / Real.Gamma (11 / 2) * besselK (11 / 2) z := by
  have ha : 0 < z / 2 := by positivity
  rw [Phi_eq_laplace hz.le, besselK_eq_integral hz (integrableOn_besselKernel_half_eleven hz.le)]
  have hi : ∫ s in Ioi (0 : ℝ), besselKernel (11 / 2) z s =
      ∫ t in Ioi (0 : ℝ), t ^ ((9 : ℝ) / 2) * Real.exp (-t - z ^ 2 / (4 * t)) := by
    simp_rw [besselKernel_half_eleven]
  rw [hi]
  have hp : (z / 2) ^ ((11 : ℝ) / 2) * (z / 2) ^ (-(11 / 2 : ℝ)) = 1 := by
    rw [← Real.rpow_add ha]; norm_num
  have hg : Real.Gamma (11 / 2) ≠ 0 := by rw [gamma_eleven_half]; positivity
  calc _ = (1 / Real.Gamma (11 / 2)) * ((z / 2) ^ ((11 : ℝ) / 2) * (z / 2) ^ (-(11 / 2 : ℝ))) *
        ∫ t in Ioi (0 : ℝ), t ^ ((9 : ℝ) / 2) * Real.exp (-t - z ^ 2 / (4 * t)) := by
        rw [hp]; ring
    _ = _ := by ring

/-- **`eq:section4-bessel-transform` and `eq:section4-eta-fourier-transform`**: for `ξ ≠ 0`,
`η̂(ξ) = (1/Γ(11/2)) ∫_0^∞ t^{9/2} e^{-t-π²|ξ|²/t} dt = 2(π|ξ|)^{11/2}/Γ(11/2) · K_{11/2}(2π|ξ|) = Φ(2π|ξ|)`. -/
theorem eta_fourier_bessel (ξ : EuclideanSpace ℝ (Fin 11)) (hξ : ξ ≠ 0) :
    (∫ x : EuclideanSpace ℝ (Fin 11), StudentIntegral.phase ξ x *
        ((BecknerOnofri.V2.Eleven.etaProfile (fun i => x i) : ℝ) : ℂ)) =
        (((1 / Real.Gamma (11 / 2)) * ∫ t in Ioi (0 : ℝ),
          t ^ ((9 : ℝ) / 2) * Real.exp (-t - Real.pi ^ 2 * ‖ξ‖ ^ 2 / t) : ℝ) : ℂ) ∧
    (∫ x : EuclideanSpace ℝ (Fin 11), StudentIntegral.phase ξ x *
        ((BecknerOnofri.V2.Eleven.etaProfile (fun i => x i) : ℝ) : ℂ)) =
        ((2 * (Real.pi * ‖ξ‖) ^ ((11 : ℝ) / 2) / Real.Gamma (11 / 2) *
          besselK (11 / 2) (2 * Real.pi * ‖ξ‖) : ℝ) : ℂ) ∧
    (∫ x : EuclideanSpace ℝ (Fin 11), StudentIntegral.phase ξ x *
        ((BecknerOnofri.V2.Eleven.etaProfile (fun i => x i) : ℝ) : ℂ)) =
        ((BecknerOnofri.V2.Eleven.Phi (2 * Real.pi * ‖ξ‖) : ℝ) : ℂ) := by
  have hn : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
  have hz : 0 < 2 * Real.pi * ‖ξ‖ := by positivity
  have h := BecknerOnofri.V2.Eleven.eta_fourier ξ
  refine ⟨?_, ?_, h⟩
  · rw [h, Phi_eq_laplace hz.le]
    congr 3
    ext t
    congr 3
    ring_nf
  · rw [h, Phi_eq_bessel hz]
    congr 3
    ring_nf

end BecknerOnofri.V2.Reaudit.ElevenBounds
