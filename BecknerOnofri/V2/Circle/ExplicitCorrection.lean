module

public import Mathlib.Tactic
public import BecknerOnofri.CircleRemainder
public import BecknerOnofri.CircleRateEntropy
public import BecknerOnofri.CircleMomentTransport
public import BecknerOnofri.CircleDensityParseval
public import BecknerOnofri.V2.Circle.ExplicitAlgebra
public import BecknerOnofri.V2.Circle.RationalWeights
public import BecknerOnofri.V2.Circle.InverseManuscript
public import BecknerOnofri.V2.Circle.PoissonC3

@[expose] public section

/-! # Lemma 5.16: circle entropy with an explicit correction (`lem:section5-circle-explicit-bound`)

For a strictly positive even `C^3` probability density `p` on the circle with first cosine moment
`t = r_1 >= 0` (so `t < 1`),
`Ent(p) >= 2 I_B(t) + psi(t) + r_2^2/40 + 2 r_3^2/15 + (27/40) sum_{n>=4} r_n^2/n`,
with NO convexity hypothesis on the logarithmic cosine profile.

Proof chain (see `workers/Circle/LEMMA516_PLAN.md`):
`Ent >= I(t) >= I_-(t)` (`entropy_ge_rate` via the Gibbs variational principle, then
`Iminus_le_rate_t`), the remainder `Ent - sum r_n^2/n >= sum w_n(t)(r_{n+1} - t r_n)^2`
(`poisson_c3_remainder`: the manuscript's Poisson regularization of the smooth case, which applies
`CirclePoisson.smooth_circle_remainder` only to the smoothed densities), the Parseval split
`energy_series_split_three`, the weights `w_j >= L_j` (`weight_one_ge`, `weight_two_ge`) and the
algebra `explicit_algebra`.

Only the old convexity-free declarations `smooth_circle_remainder` (through `PoissonC3`), `rate_le_circle_entropy`,
`density_parseval`, `smooth_fisher_lower_bound`, `moment_eq_cosine_integral`,
`integral_torus_circle` and the Bessel series modules are used. -/
noncomputable section
open MeasureTheory Set
open BecknerOnofri.HighDim BecknerOnofri.HighDim.CirclePoisson BecknerOnofri.HighDim.CircleScalar
namespace BecknerOnofri.V2.Circle

theorem energy_series_summable' (r : ℕ → ℝ)
    (hr : Summable (fun n : ℕ => (r (n+1))^2)) :
    Summable (fun n : ℕ => (r (n+1))^2/(n+1:ℝ)) := by
  apply Summable.of_nonneg_of_le (fun n => by positivity) _ hr
  intro n
  exact div_le_self (sq_nonneg _) (by linarith [Nat.cast_nonneg (α:=ℝ) n])

/-- `∑_{n≥1} r_n²/n = r₁² + r₂²/2 + r₃²/3 + ∑_{n≥4} r_n²/n`. -/
theorem energy_series_split_three (r : ℕ → ℝ)
    (hr : Summable (fun n : ℕ => (r (n+1))^2)) :
    (∑' n : ℕ,(r (n+1))^2/(n+1:ℝ)) = (r 1)^2 + (r 2)^2/2 + (r 3)^2/3 +
      ∑' n : ℕ,(r (n+4))^2/(n+4:ℝ) := by
  have h := (energy_series_summable' r hr).sum_add_tsum_nat_add 3
  norm_num [Finset.sum_range_succ,Nat.cast_add,add_assoc] at h
  linarith [h]


/-- Gibbs step (`d12-circle-eq:cramer`): `Ent(p) ≥ I(t)` for the actual circle density, with the
first moment prescribed; no convexity of the log-cosine profile is used. -/
theorem entropy_ge_rate (p : Torus 1 → ℝ) (hp : Continuous p) (hpos : ∀ x, 0 < p x)
    (hm : (∫ x, p x ∂torusMeasure 1) = 1) :
    rate (moment p 1) ≤ ∫ x, p x * Real.log (p x) ∂torusMeasure 1 := by
  let q : UnitAddCircle → ℝ := fun z => p (fun _ => z)
  have hq : Continuous q := hp.comp (continuous_pi (fun _ => continuous_id))
  have hqpos (z : UnitAddCircle) : 0 < q z := hpos _
  have hmass : (∫ z, q z ∂AddCircle.haarAddCircle) = 1 := (integral_torus_circle p).symm.trans hm
  have hi : Integrable q AddCircle.haarAddCircle := hq.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hent : Integrable (fun z => q z * Real.log (q z)) AddCircle.haarAddCircle :=
    (hq.mul (hq.log (fun z => (hqpos z).ne'))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hmean : (∫ z, q z * (fourier 1 z).re ∂AddCircle.haarAddCircle) = moment p 1 := by
    simpa only [Nat.cast_one] using (moment_eq_cosine_integral p hp 1).symm
  have h := rate_le_circle_entropy q (moment p 1)
    (Filter.Eventually.of_forall (fun z => (hqpos z).le)) hmass hi hent hmean
  have hE := integral_torus_circle (fun x => p x * Real.log (p x))
  rw [hE]
  exact h


/-- **Lemma 5.16** (`lem:section5-circle-explicit-bound`), for every strictly positive even `C³`
probability density on the circle with first cosine moment `t = r₁ ≥ 0` (then `t < 1`
automatically).  No convexity hypothesis on `log p` as a function of `cos`.
`moment p n = r_n`; entropy is `∫ p log p` for the normalized Haar measure. -/
theorem circle_entropy_explicit (p : Torus 1 → ℝ) (hp : Continuous p)
    (hpos : ∀ x, 0 < p x) (he : ∀ x, p (-x) = p x) (hm : (∫ x, p x ∂torusMeasure 1) = 1)
    (hsmooth : ContDiff ℝ 3 (fun x : ℝ => p (fun _ => (x : UnitAddCircle))))
    (ht : 0 ≤ moment p 1) :
    2 * Spin.binaryCost (moment p 1) + psi (moment p 1) + (1 / 40) * (moment p 2) ^ 2 +
      (2 / 15) * (moment p 3) ^ 2 + (27 / 40) * (∑' n : ℕ, (moment p (n + 4)) ^ 2 / (n + 4 : ℝ)) ≤
        ∫ x, p x * Real.log (p x) ∂torusMeasure 1 := by
  have hsq : (moment p 1) ^ 2 < 1 := (CircleFisher.smooth_fisher_lower_bound p hp hpos he hm hsmooth).1
  have ht1 : moment p 1 < 1 := by nlinarith
  obtain ⟨hS, hRem⟩ := poisson_c3_remainder p hp hpos he hm hsmooth
  let A : ℕ → ℝ := fun n => weight (n + 1) (moment p 1) *
    (moment p (n + 2) - moment p 1 * moment p (n + 1)) ^ 2
  have hnonneg (n : ℕ) : 0 ≤ A n := by
    apply mul_nonneg _ (sq_nonneg _)
    unfold weight
    exact tsum_nonneg (fun j => by positivity)
  have hfirst := hS.sum_le_tsum ({0, 1} : Finset ℕ) (fun n _ => hnonneg n)
  have hfirst' : weight 1 (moment p 1) * (moment p 2 - moment p 1 * moment p 1) ^ 2 +
      weight 2 (moment p 1) * (moment p 3 - moment p 1 * moment p 2) ^ 2 ≤ ∑' n, A n := by
    simpa [A] using hfirst
  have hr : Summable (fun n : ℕ => (moment p (n + 1)) ^ 2) := by
    simpa only [moment, Nat.cast_add, Nat.cast_one] using (CircleOuter.density_parseval p hp he hm).1
  have hsplit := energy_series_split_three (moment p) hr
  change _ ≤ (∫ x, p x * Real.log (p x) ∂torusMeasure 1) -
    ∑' n : ℕ, (moment p (n + 1)) ^ 2 / (n + 1 : ℝ) at hRem
  rw [hsplit] at hRem
  have hIm := Iminus_le_rate_t ht ht1
  have hG := entropy_ge_rate p hp hpos hm
  have hw1 := weight_one_ge ht ht1
  have hw2 := weight_two_ge ht ht1
  have key := explicit_algebra (t := moment p 1) (a := moment p 2) (b := moment p 3)
    (Ent := ∫ x, p x * Real.log (p x) ∂torusMeasure 1)
    (T := ∑' n : ℕ, (moment p (n + 4)) ^ 2 / (n + 4 : ℝ))
    (w1 := weight 1 (moment p 1)) (w2 := weight 2 (moment p 1)) ht ht1 hw1 hw2 (hIm.trans hG)
    (by nlinarith [hfirst', hRem])
  linarith [key]

end BecknerOnofri.V2.Circle
