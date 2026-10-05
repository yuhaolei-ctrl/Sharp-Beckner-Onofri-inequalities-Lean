module

public import BecknerOnofri.LocalBesselFourier
public import Legacy.TorusEndpoint.TorusHeatPositivity

@[expose] public section

/-! Summable factorial majorants for actual first-shell Gibbs Fourier coefficients. -/
noncomputable section
open scoped BigOperators
namespace BecknerOnofri.HighDim

lemma natAbs_neg_add_one (n : ℕ) : (-(n + 1 : ℤ)).natAbs = n + 1 := by
  change (-((n + 1 : ℕ) : ℤ)).natAbs = n + 1
  simp only [Int.natAbs_neg, Int.natAbs_natCast]

def circleFourierMajorant (t : ℝ) (k : ℤ) : ℝ :=
  besselSeriesTerm (t ^ 2) k.natAbs

def firstShellFourierMajorant {d : ℕ} (t : Fin d → ℝ) (k : Frequency d) : ℝ :=
  ∏ i, circleFourierMajorant (t i) (k i)

lemma circleFourierMajorant_nonneg (t : ℝ) (k : ℤ) :
    0 ≤ circleFourierMajorant t k := besselSeriesTerm_nonneg (sq_nonneg t) _

lemma circleFourierMajorant_summable (t : ℝ) : Summable (circleFourierMajorant t) := by
  apply Summable.of_nat_of_neg_add_one
  · simpa only [circleFourierMajorant, Int.natAbs_natCast, natAbs_neg_add_one] using besselSeries_summable (sq_nonneg t)
  · simpa only [circleFourierMajorant, Int.natAbs_natCast, natAbs_neg_add_one] using
      (summable_nat_add_iff 1).mpr (besselSeries_summable (sq_nonneg t))

lemma circleFourierMajorant_tsum (t : ℝ) :
    (∑' k : ℤ, circleFourierMajorant t k) = 2 * besselI0Two t - 1 := by
  have hs := besselSeries_summable (sq_nonneg t)
  have htail := (summable_nat_add_iff 1).mpr hs
  have he := tsum_of_nat_of_neg_add_one
    (f := circleFourierMajorant t) (by simpa only [circleFourierMajorant, Int.natAbs_natCast, natAbs_neg_add_one] using hs)
    (by simpa only [circleFourierMajorant, Int.natAbs_natCast, natAbs_neg_add_one] using htail)
  have hsplit := hs.tsum_eq_zero_add
  simp only [circleFourierMajorant, Int.natAbs_natCast, natAbs_neg_add_one] at he
  rw [besselI0Two_eq_series]
  norm_num [besselSeriesTerm] at hsplit
  dsimp [circleFourierMajorant, besselSeriesTerm] at he ⊢
  linarith

lemma besselI0Two_le_exp (t : ℝ) : besselI0Two t ≤ Real.exp (t ^ 2) := by
  rw [besselI0Two_eq_series, Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  apply (besselSeries_summable (sq_nonneg t)).tsum_le_tsum _
    (Real.summable_pow_div_factorial (t ^ 2))
  intro n
  unfold besselSeriesTerm
  have hfac : (1 : ℝ) ≤ n.factorial := by exact_mod_cast Nat.factorial_pos n
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  nlinarith

lemma circleFourierMajorant_tsum_le (t : ℝ) :
    (∑' k : ℤ, circleFourierMajorant t k) ≤ Real.exp (2 * t ^ 2) := by
  rw [circleFourierMajorant_tsum, show 2 * t ^ 2 = t ^ 2 + t ^ 2 by ring, Real.exp_add]
  nlinarith [besselI0Two_le_exp t, sq_nonneg (Real.exp (t ^ 2) - 1)]

lemma firstShellFourierMajorant_nonneg {d : ℕ} (t : Fin d → ℝ) (k : Frequency d) :
    0 ≤ firstShellFourierMajorant t k :=
  Finset.prod_nonneg (fun _ _ => circleFourierMajorant_nonneg _ _)

lemma firstShellFourierMajorant_summable {d : ℕ} (t : Fin d → ℝ) :
    Summable (firstShellFourierMajorant t) := by
  have hs (i : Fin d) : Summable (fun k : ℤ => ‖(circleFourierMajorant (t i) k : ℂ)‖) := by
    simpa only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (circleFourierMajorant_nonneg _ _)] using circleFourierMajorant_summable (t i)
  have h := Legacy.TorusEndpoint.TorusHeatPositivity.finite_product_summable_norm d
    (fun i k => (circleFourierMajorant (t i) k : ℂ)) hs
  simp only [← Complex.ofReal_prod, Complex.norm_real, Real.norm_eq_abs] at h
  change Summable (fun k => |firstShellFourierMajorant t k|) at h
  simpa only [abs_of_nonneg (firstShellFourierMajorant_nonneg _ _)] using h

lemma firstShellFourierMajorant_tsum {d : ℕ} (t : Fin d → ℝ) :
    (∑' k : Frequency d, firstShellFourierMajorant t k) =
      ∏ i, ∑' k : ℤ, circleFourierMajorant (t i) k := by
  have hs (i : Fin d) : Summable (fun k : ℤ => ‖(circleFourierMajorant (t i) k : ℂ)‖) := by
    simpa only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (circleFourierMajorant_nonneg _ _)] using circleFourierMajorant_summable (t i)
  have h := Legacy.TorusEndpoint.TorusHeatPositivity.finite_product_tsum d
    (fun i k => (circleFourierMajorant (t i) k : ℂ)) hs
  simp only [← Complex.ofReal_prod, ← Complex.ofReal_tsum] at h
  exact Complex.ofReal_injective h

lemma firstShellFourierMajorant_tsum_le {d : ℕ} (t : Fin d → ℝ) :
    (∑' k : Frequency d, firstShellFourierMajorant t k) ≤ Real.exp (2 * ∑ i, t i ^ 2) := by
  rw [firstShellFourierMajorant_tsum, Finset.mul_sum, Real.exp_sum]
  exact Finset.prod_le_prod₀
    (fun _ _ => tsum_nonneg (circleFourierMajorant_nonneg _))
    (fun i _ => circleFourierMajorant_tsum_le (t i))

lemma firstShellTilt_fourier_sq_bound {d : ℕ} (t : Fin d → ℝ) (ht : ∀ i, 0 ≤ t i)
    (k : Frequency d) :
    ‖fourierCoeff (firstShellTilt t) k‖ ^ 2 ≤ firstShellFourierMajorant t k := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (firstShellTilt_fourier_bound t ht k) 2
  apply h.trans_eq
  rw [← Finset.prod_pow]
  unfold firstShellFourierMajorant
  apply Finset.prod_congr rfl
  intro i _
  unfold circleFourierMajorant besselSeriesTerm
  rw [div_pow]
  congr 1
  rw [← pow_mul, ← pow_mul, Nat.mul_comm]

#print axioms firstShellFourierMajorant_tsum_le
#print axioms firstShellTilt_fourier_sq_bound
end BecknerOnofri.HighDim
