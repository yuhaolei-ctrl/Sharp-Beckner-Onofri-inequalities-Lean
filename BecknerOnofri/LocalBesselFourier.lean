import BecknerOnofri.LocalFirstShell

/-! Fourier coefficients of the actual circular Gibbs density, with factorial bounds. -/
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
namespace BecknerOnofri.HighDim

def besselOrderTerm (t : ℝ) (m n : ℕ) : ℝ :=
  t ^ (n + m) * t ^ n / ((n + m).factorial * (n.factorial : ℝ))

def besselFourierTerm (t : ℝ) (m : ℕ) (p : ℕ × ℕ) (x : UnitAddCircle) : ℂ :=
  fourier (-(m : ℤ)) x * circleBesselTerm t (p.2, p.1) x

lemma besselFourierTerm_norm (t : ℝ) (m : ℕ) (p : ℕ × ℕ) (x : UnitAddCircle) :
    ‖besselFourierTerm t m p x‖ =
      (|t| ^ p.1 / (p.1.factorial : ℝ)) * (|t| ^ p.2 / (p.2.factorial : ℝ)) := by
  rw [besselFourierTerm, norm_mul, circle_fourier_norm, one_mul, circleBesselTerm_norm]
  exact mul_comm _ _

lemma besselFourierTerm_integrable (t : ℝ) (m : ℕ) (p : ℕ × ℕ) :
    Integrable (besselFourierTerm t m p) AddCircle.haarAddCircle := by
  apply Integrable.of_bound (by unfold besselFourierTerm circleBesselTerm; fun_prop)
    ((|t| ^ p.1 / (p.1.factorial : ℝ)) * (|t| ^ p.2 / (p.2.factorial : ℝ)))
  exact Filter.Eventually.of_forall (fun x => (besselFourierTerm_norm t m p x).le)

lemma besselFourierTerm_integral (t : ℝ) (m : ℕ) (p : ℕ × ℕ) :
    (∫ x, besselFourierTerm t m p x ∂AddCircle.haarAddCircle) =
      if p.2 = p.1 + m then (besselOrderTerm t m p.1 : ℂ) else 0 := by
  rcases p with ⟨n, l⟩
  have he : besselFourierTerm t m (n, l) = fun x =>
      (circleExpCoefficient t l * circleExpCoefficient t n) *
        fourier (-(m : ℤ) + ((l : ℤ) - (n : ℤ))) x := by
    funext x
    unfold besselFourierTerm circleBesselTerm
    rw [fourier_add]
    ring
  rw [he, integral_const_mul, circle_fourier_integral]
  have hz : -(m : ℤ) + ((l : ℤ) - (n : ℤ)) = 0 ↔ l = n + m := by omega
  simp only [hz]
  by_cases h : l = n + m
  · subst l
    simp only [↓reduceIte, mul_one]
    unfold circleExpCoefficient besselOrderTerm
    push_cast
    ring
  · simp [h]

lemma besselOrderTerm_hasSum_integral (t : ℝ) (m : ℕ) :
    HasSum (fun n : ℕ => (besselOrderTerm t m n : ℂ))
      (∫ x : UnitAddCircle, fourier (-(m : ℤ)) x *
        (Real.exp (2 * t * circleCosine x) : ℂ) ∂AddCircle.haarAddCircle) := by
  have hs : Summable (fun p : ℕ × ℕ =>
      ∫ x : UnitAddCircle, ‖besselFourierTerm t m p x‖ ∂AddCircle.haarAddCircle) := by
    simp_rw [besselFourierTerm_norm]
    simp only [integral_const, probReal_univ, one_smul]
    exact (Real.summable_pow_div_factorial |t|).mul_of_nonneg
      (Real.summable_pow_div_factorial |t|) (fun n => by positivity) (fun n => by positivity)
  have hi := hasSum_integral_of_summable_integral_norm (besselFourierTerm_integrable t m) hs
  have hsum (x : UnitAddCircle) : (∑' p : ℕ × ℕ, besselFourierTerm t m p x) =
      fourier (-(m : ℤ)) x * (Real.exp (2 * t * circleCosine x) : ℂ) := by
    have hh := (circleBesselTerm_hasSum t x).mul_left (fourier (-(m : ℤ)) x)
    exact ((Equiv.prodComm ℕ ℕ).hasSum_iff.mpr hh).tsum_eq
  simp_rw [hsum, besselFourierTerm_integral] at hi
  exact hi.prod_fiberwise (fun n : ℕ => hasSum_ite_eq (n + m) (besselOrderTerm t m n : ℂ))

lemma besselOrderTerm_summable (t : ℝ) (m : ℕ) : Summable (besselOrderTerm t m) :=
  Complex.summable_ofReal.mp (besselOrderTerm_hasSum_integral t m).summable

lemma besselOrderTerm_le {t : ℝ} (ht : 0 ≤ t) (m n : ℕ) :
    besselOrderTerm t m n ≤ t ^ m / (m.factorial : ℝ) * besselSeriesTerm (t ^ 2) n := by
  have hf : (n.factorial : ℝ) * (m.factorial : ℝ) ≤ ((n + m).factorial : ℝ) := by
    exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos _)
      (Nat.factorial_mul_factorial_dvd_factorial_add n m)
  unfold besselOrderTerm
  calc
    _ ≤ t ^ (n + m) * t ^ n /
        (((n.factorial : ℝ) * (m.factorial : ℝ)) * (n.factorial : ℝ)) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_right hf (by positivity))
    _ = _ := by
      unfold besselSeriesTerm
      rw [pow_add, ← pow_mul, Nat.mul_comm 2 n, pow_mul]
      field_simp

lemma circleTiltFourier_nat_eq (t : ℝ) (m : ℕ) :
    circleTiltFourier t (m : ℤ) = ((∑' n, besselOrderTerm t m n) / besselI0Two t : ℝ) := by
  unfold circleTiltFourier circleTiltDensity
  simp only [Complex.ofReal_div, ← mul_div_assoc]
  rw [integral_div, ← (besselOrderTerm_hasSum_integral t m).tsum_eq,
    ← Complex.ofReal_tsum (besselOrderTerm t m)]

lemma circleTiltFourier_nat_bound {t : ℝ} (ht : 0 ≤ t) (m : ℕ) :
    ‖circleTiltFourier t (m : ℤ)‖ ≤ t ^ m / (m.factorial : ℝ) := by
  rw [circleTiltFourier_nat_eq, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (tsum_nonneg (fun n => by unfold besselOrderTerm; positivity))
      (besselI0Two_pos t).le)]
  apply (div_le_iff₀ (besselI0Two_pos t)).mpr
  have h := (besselOrderTerm_summable t m).tsum_le_tsum (besselOrderTerm_le ht m)
    ((besselSeries_summable (sq_nonneg t)).mul_left (t ^ m / (m.factorial : ℝ)))
  simpa only [tsum_mul_left, ← besselI0Two_eq_series] using h

lemma circleTiltFourier_neg (t : ℝ) (k : ℤ) :
    circleTiltFourier t (-k) = conj (circleTiltFourier t k) := by
  unfold circleTiltFourier
  rw [← integral_conj]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by
    simp only [neg_neg, map_mul, Complex.conj_ofReal]
    rw [← fourier_neg, neg_neg])

lemma circleTiltFourier_bound {t : ℝ} (ht : 0 ≤ t) (k : ℤ) :
    ‖circleTiltFourier t k‖ ≤ t ^ k.natAbs / (k.natAbs.factorial : ℝ) := by
  rcases k with n | n
  · exact circleTiltFourier_nat_bound ht n
  · have h := circleTiltFourier_nat_bound ht (n + 1)
    change ‖circleTiltFourier t (-((n + 1 : ℕ) : ℤ))‖ ≤
      t ^ (n + 1) / ((n + 1).factorial : ℝ)
    rw [circleTiltFourier_neg, Complex.norm_conj]
    exact h

lemma firstShellTilt_fourier_bound {d : ℕ} (t : Fin d → ℝ) (ht : ∀ i, 0 ≤ t i)
    (k : Frequency d) :
    ‖fourierCoeff (firstShellTilt t) k‖ ≤
      ∏ i, t i ^ (k i).natAbs / ((k i).natAbs.factorial : ℝ) := by
  rw [firstShellTilt_fourier, norm_prod]
  exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => circleTiltFourier_bound (ht i) _)

#print axioms firstShellTilt_fourier_bound
end BecknerOnofri.HighDim
