module

public import Mathlib.Tactic
public import BecknerOnofri.CircleRemainder
public import BecknerOnofri.CirclePoissonInitial
public import BecknerOnofri.CircleFisherBound
public import BecknerOnofri.CircleDensityParseval

@[expose] public section

/-! # The `C^3` extension of the Poisson remainder by Poisson regularization (Lemma 5.14)

The manuscript proves `Ent(p) - sum r_n^2/n >= sum_n w_n(t)(r_{n+1} - t r_n)^2` for smooth
positive even densities and extends it to strictly positive even normalized `C^3` densities by the
approximation `p_r = P_r * p` (`r < 1`): moments `r^j r_j`, `t_r = r t`, `min p <= p_r <= max p`,
`Ent(p_r) -> Ent(p)`; finite partial sums first (`r -> 1`), then `N -> infinity`.

This module formalizes exactly that passage (RECON decision point 1, manuscript route).  The
repository's `smooth_circle_remainder` is applied only to the smoothed densities
`p_s = torusFlow s p` (`s > 0`, `r = e^{-s}`), never to `p` itself; the facts used about `p`
are continuity, positivity, evenness, mass one, `|t| < 1`, and the Fourier decay that `C^3` gives.

* `weight_continuousAt`: `w_n` is continuous on `|t| < 1`;
* `poisson_c3_remainder`: the `C^3` remainder, same statement as `smooth_circle_remainder`. -/
noncomputable section
open MeasureTheory Set Filter Topology
open BecknerOnofri.HighDim BecknerOnofri.HighDim.CirclePoisson BecknerOnofri.HighDim.CircleScalar
namespace BecknerOnofri.V2.Circle

/-- `w_n(t) = ∑_j t^{2j}/(n+j+1)` is continuous at every `t` with `t² < 1`. -/
theorem weight_continuousAt (n : ℕ) {t : ℝ} (ht : t ^ 2 < 1) : ContinuousAt (weight n) t := by
  have habs : |t| < 1 := by
    have := sq_lt_one_iff_abs_lt_one t |>.mp ht
    exact this
  set ρ := (|t| + 1) / 2 with hρ
  have hρ1 : ρ < 1 := by rw [hρ]; linarith
  have hρ0 : 0 ≤ ρ := by rw [hρ]; positivity
  have hnhds : Icc (-ρ) ρ ∈ 𝓝 t := by
    apply Icc_mem_nhds
    · have := neg_abs_le t; rw [hρ]; linarith [abs_nonneg t]
    · have := le_abs_self t; rw [hρ]; linarith [abs_nonneg t]
  have hgeo : Summable (fun j : ℕ => (ρ ^ 2) ^ j) :=
    summable_geometric_of_lt_one (by positivity) (by nlinarith)
  have hcont : ContinuousOn (fun x : ℝ => ∑' j : ℕ, x ^ (2 * j) / (n + j + 1 : ℝ)) (Icc (-ρ) ρ) := by
    apply continuousOn_tsum (u := fun j : ℕ => (ρ ^ 2) ^ j)
    · intro j; fun_prop
    · exact hgeo
    · intro j x hx
      have hx2 : |x| ≤ ρ := abs_le.mpr ⟨hx.1, hx.2⟩
      rw [Real.norm_eq_abs, abs_div, abs_pow, abs_of_pos (by positivity : (0:ℝ) < n + j + 1),
        pow_mul]
      have h1 : |x| ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ (abs_nonneg x) hx2 2
      have h2 : (|x| ^ 2) ^ j ≤ (ρ ^ 2) ^ j := pow_le_pow_left₀ (by positivity) h1 j
      have h3 : (1 : ℝ) ≤ n + j + 1 := by
        have : (0:ℝ) ≤ n + j := by positivity
        linarith
      calc (|x| ^ 2) ^ j / (n + j + 1 : ℝ) ≤ (|x| ^ 2) ^ j := div_le_self (by positivity) h3
        _ ≤ _ := h2
  exact (hcont.continuousAt hnhds)

/-- **Lemma 5.14 for `C^3` densities, by Poisson regularization** (manuscript route). -/
theorem poisson_c3_remainder (p : Torus 1 → ℝ) (hp : Continuous p)
    (hpos : ∀ x, 0 < p x) (he : ∀ x, p (-x) = p x) (hm : (∫ x, p x ∂torusMeasure 1) = 1)
    (hsmooth : ContDiff ℝ 3 (fun x : ℝ => p (fun _ => (x : UnitAddCircle)))) :
    Summable (fun n : ℕ => weight (n + 1) (moment p 1) *
      (moment p (n + 2) - moment p 1 * moment p (n + 1)) ^ 2) ∧
    (∑' n : ℕ, weight (n + 1) (moment p 1) *
      (moment p (n + 2) - moment p 1 * moment p (n + 1)) ^ 2) ≤
      (∫ x, p x * Real.log (p x) ∂torusMeasure 1) - ∑' n : ℕ, (moment p (n + 1)) ^ 2 / (n + 1 : ℝ) := by
  have ht2 : (moment p 1) ^ 2 < 1 :=
    (CircleFisher.smooth_fisher_lower_bound p hp hpos he hm hsmooth).1
  have hw : Summable (fun k => CircleOuter.linearWeight k *
      ‖UnitAddTorus.mFourierCoeff (fun x => (p x : ℂ)) k‖) :=
    CircleRegularity.torus_weighted_summable (fun x => (p x : ℂ))
      (Complex.ofRealCLM.contDiff.comp hsmooth)
  have hr : Summable (fun n : ℕ => (moment p (n + 1)) ^ 2) := by
    simpa only [moment, Nat.cast_add, Nat.cast_one] using
      (CircleOuter.density_parseval p hp he hm).1
  -- the regularized moments `r_n(s) = e^{-ns} r_n`
  obtain ⟨rs, hrs⟩ : ∃ rs : ℝ → ℕ → ℝ, ∀ s n, rs s n = Real.exp (-(n : ℝ) * s) * moment p n :=
    ⟨fun s n => Real.exp (-(n : ℝ) * s) * moment p n, fun _ _ => rfl⟩
  let A : ℝ → ℕ → ℝ := fun s n =>
    weight (n + 1) (rs s 1) * (rs s (n + 2) - rs s 1 * rs s (n + 1)) ^ 2
  let B : ℝ → ℕ → ℝ := fun s n => (rs s (n + 1)) ^ 2 / (n + 1 : ℝ)
  have hAnn (s : ℝ) (n : ℕ) : 0 ≤ A s n := by
    apply mul_nonneg _ (sq_nonneg _)
    unfold weight
    exact tsum_nonneg (fun j => div_nonneg (by rw [pow_mul]; exact pow_nonneg (sq_nonneg _) _)
      (by positivity))
  have hBnn (s : ℝ) (n : ℕ) : 0 ≤ B s n := by simp only [B]; positivity
  have hBsum (s : ℝ) (hs : 0 ≤ s) : Summable (B s) := by
    apply Summable.of_nonneg_of_le (hBnn s) _ hr
    intro n
    have h1 : (1 : ℝ) ≤ n + 1 := by have : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith
    have he1 : Real.exp (-((n + 1 : ℕ) : ℝ) * s) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : (0:ℝ) ≤ ((n + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
      nlinarith
    have he0 := (Real.exp_pos (-((n + 1 : ℕ) : ℝ) * s)).le
    have hsq : (rs s (n + 1)) ^ 2 ≤ (moment p (n + 1)) ^ 2 := by
      rw [hrs]
      have := mul_le_mul_of_nonneg_right he1 (sq_nonneg (moment p (n + 1)))
      nlinarith [sq_nonneg (moment p (n + 1)), mul_nonneg he0 he0]
    exact (div_le_self (sq_nonneg _) h1).trans hsq
  -- regularized remainder for finite partial sums
  have hfin (s : ℝ) (hs : 0 < s) (N : ℕ) :
      ∑ n ∈ Finset.range N, (A s n + B s n) ≤
        ∫ x, torusFlow s p x * Real.log (torusFlow s p x) ∂torusMeasure 1 := by
    have hmom (k : ℕ) : moment (torusFlow s p) k = rs s k := by
      rw [hrs]; exact torus_flow_real_coefficient s hs p hp k
    obtain ⟨hS, hle⟩ := smooth_circle_remainder (torusFlow s p) (torus_flow_continuous s hs p hp)
      (torus_flow_positive p hp hpos s hs) (torus_flow_even p he s)
      ((torus_flow_mass s hs p hp).trans hm) (torus_flow_contDiff p hp hw s hs 3)
    simp only [hmom] at hS hle
    have h1 : ∑ n ∈ Finset.range N, A s n ≤ ∑' n, A s n :=
      hS.sum_le_tsum _ (fun n _ => hAnn s n)
    have h2 : ∑ n ∈ Finset.range N, B s n ≤ ∑' n, B s n :=
      (hBsum s hs.le).sum_le_tsum _ (fun n _ => hBnn s n)
    rw [Finset.sum_add_distrib]
    change ∑' n, A s n ≤ _ - ∑' n, B s n at hle
    linarith
  -- continuity in `s` at `0`
  have hrsc (n : ℕ) : Continuous (fun s => rs s n) := by
    simp_rw [hrs]; fun_prop
  have hrs0 (k : ℕ) : rs 0 k = moment p k := by simp [hrs]
  have hAc (n : ℕ) : ContinuousAt (fun s => A s n) 0 := by
    have hw0 : ContinuousAt (weight (n + 1)) ((fun s => rs s 1) 0) :=
      weight_continuousAt _ (by show (rs 0 1) ^ 2 < 1; rw [hrs0]; exact ht2)
    have h1 : ContinuousAt (fun s => weight (n + 1) (rs s 1)) 0 :=
      ContinuousAt.comp (f := fun s => rs s 1) (x := 0) hw0 (hrsc 1).continuousAt
    exact h1.mul (((hrsc (n + 2)).sub ((hrsc 1).mul (hrsc (n + 1)))).pow 2).continuousAt
  have hBc (n : ℕ) : ContinuousAt (fun s => B s n) 0 :=
    (((hrsc (n + 1)).pow 2).div_const _).continuousAt
  have hent := entropy_tendsto_initial p hp hpos hw
  have hfin0 (N : ℕ) : ∑ n ∈ Finset.range N, (A 0 n + B 0 n) ≤
      ∫ x, p x * Real.log (p x) ∂torusMeasure 1 := by
    have hlim : Tendsto (fun s => ∑ n ∈ Finset.range N, (A s n + B s n)) (𝓝[>] 0)
        (𝓝 (∑ n ∈ Finset.range N, (A 0 n + B 0 n))) :=
      (tendsto_finsetSum _ (fun n _ => ((hAc n).add (hBc n)).tendsto)).mono_left
        nhdsWithin_le_nhds
    refine le_of_tendsto_of_tendsto hlim (hent.mono_left (nhdsWithin_mono 0 Ioi_subset_Ici_self)) ?_
    exact eventually_nhdsWithin_of_forall (fun s hs => hfin s hs N)
  have hA0 (n : ℕ) : A 0 n = weight (n + 1) (moment p 1) *
      (moment p (n + 2) - moment p 1 * moment p (n + 1)) ^ 2 := by simp only [A, hrs0]
  have hB0 (n : ℕ) : B 0 n = (moment p (n + 1)) ^ 2 / (n + 1 : ℝ) := by simp only [B, hrs0]
  have hf0 (n : ℕ) : 0 ≤ A 0 n + B 0 n := add_nonneg (hAnn 0 n) (hBnn 0 n)
  have hsumf : Summable (fun n => A 0 n + B 0 n) := summable_of_sum_range_le hf0 hfin0
  have hsA : Summable (A 0) :=
    Summable.of_nonneg_of_le (hAnn 0) (fun n => by linarith [hBnn 0 n]) hsumf
  have hsB : Summable (B 0) :=
    Summable.of_nonneg_of_le (hBnn 0) (fun n => by linarith [hAnn 0 n]) hsumf
  have htot := Real.tsum_le_of_sum_range_le hf0 hfin0
  rw [hsA.tsum_add hsB] at htot
  have hAfun : A 0 = fun n => weight (n + 1) (moment p 1) *
      (moment p (n + 2) - moment p 1 * moment p (n + 1)) ^ 2 := funext hA0
  have hBfun : B 0 = fun n => (moment p (n + 1)) ^ 2 / (n + 1 : ℝ) := funext hB0
  rw [hAfun] at hsA
  rw [hAfun, hBfun] at htot
  exact ⟨hsA, by linarith⟩

end BecknerOnofri.V2.Circle
