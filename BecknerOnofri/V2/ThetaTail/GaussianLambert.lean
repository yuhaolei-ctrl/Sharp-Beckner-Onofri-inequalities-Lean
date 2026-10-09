module

public import BecknerOnofri.V2.ThetaTail.TwelveBound

@[expose] public section

/-! # `G(η)` bounded by Lambert series, assuming the twelve-square identity

HONESTLY CONDITIONAL on `TwelveSquareIdentity`:

`G_le_lambert_of_twelveSquare`:
`G(η) ≤ 8 ∑σ₅(m)e^{-mη}/m⁶ − (1/8) ∑σ₅(m)e^{-4mη}/m⁶ − ∑_{s=1}^{12} d_s e^{-sη}`,

the Lambert form of `(d12-tail-eq:Glog)`: apply the identity in the Mellin formula, bound the
eta-product term, integrate the Lambert series termwise (absolute convergence). -/
noncomputable section
open Finset Filter Topology MeasureTheory Set
namespace BecknerOnofri.V2.ThetaTail

/-- `Λ(x) = ∑_{m≥1} σ₅(m) x^m / m⁶` -/
def lambertSum (x : ℝ) : ℝ := ∑' m : ℕ+, sigma5 m * x ^ (m : ℕ) / ((m : ℕ) : ℝ) ^ 6

lemma summable_lam {η b : ℝ} (hη : 0 < η) (hb : 0 < b) :
    Summable (fun m : ℕ+ => sigma5 m * Real.exp (-η * (b * (m : ℕ))) / (b * (m : ℕ)) ^ 6) := by
  have hg : Summable (fun n : ℕ => Real.exp (-η * b) ^ n) :=
    summable_geometric_of_lt_one (Real.exp_pos _).le
      (Real.exp_lt_one_iff.2 (by nlinarith))
  have hg' : Summable (fun m : ℕ+ => Real.exp (-η * b) ^ (m : ℕ)) := hg.subtype _
  refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_) (hg'.mul_left (1 / b ^ 6))
  · exact div_nonneg (mul_nonneg (sigma5_nonneg _) (Real.exp_pos _).le) (by positivity)
  · have hm : (1 : ℝ) ≤ (m : ℕ) := by exact_mod_cast m.pos
    have hs := sigma5_le (m : ℕ)
    have e : Real.exp (-η * (b * (m : ℕ))) = Real.exp (-η * b) ^ (m : ℕ) := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    rw [e, mul_pow]
    have hm0 : (0 : ℝ) < ((m : ℕ) : ℝ) ^ 6 := by positivity
    have hb6 : (0 : ℝ) < b ^ 6 := by positivity
    rw [div_le_iff₀ (by positivity)]
    calc sigma5 m * Real.exp (-η * b) ^ (m : ℕ)
        ≤ ((m : ℕ) : ℝ) ^ 6 * Real.exp (-η * b) ^ (m : ℕ) :=
          mul_le_mul_of_nonneg_right hs (by positivity)
      _ = 1 / b ^ 6 * Real.exp (-η * b) ^ (m : ℕ) * (b ^ 6 * ((m : ℕ) : ℝ) ^ 6) := by
          field_simp

lemma lam1_eq (η : ℝ) :
    ∑' m : ℕ+, sigma5 m * Real.exp (-η * (1 * (m : ℕ))) / (1 * (m : ℕ)) ^ 6
      = lambertSum (Real.exp (-η)) := by
  unfold lambertSum
  refine tsum_congr fun m => ?_
  rw [← Real.exp_nat_mul]; congr 3 <;> ring

lemma lam4_eq (η : ℝ) :
    ∑' m : ℕ+, sigma5 m * Real.exp (-η * (4 * (m : ℕ))) / (4 * (m : ℕ)) ^ 6
      = lambertSum (Real.exp (-(4 * η))) / 4096 := by
  unfold lambertSum
  rw [← tsum_div_const]
  refine tsum_congr fun m => ?_
  rw [← Real.exp_nat_mul]
  have : -η * (4 * ((m : ℕ) : ℝ)) = ((m : ℕ) : ℝ) * (-(4 * η)) := by ring
  rw [this]
  rw [mul_pow]
  have : (0 : ℝ) < ((m : ℕ) : ℝ) ^ 6 := by positivity
  field_simp
  norm_num

/-- `∑_m σ₅(m) e^{-s b m}` -/
def lamA (b s : ℝ) : ℝ := ∑' m : ℕ+, sigma5 m * Real.exp (-s * (b * (m : ℕ)))

/-- `∑_{t=1}^{12} t⁶ d_t e^{-st}` -/
def polyD (s : ℝ) : ℝ := ∑ t ∈ Icc 1 12, dCoeffR t * (t : ℝ) ^ 6 * Real.exp (-s * t)

lemma exp_neg_pow (s : ℝ) (n : ℕ) : Real.exp (-s) ^ n = Real.exp (-s * n) := by
  rw [← Real.exp_nat_mul]; congr 1; ring

/-- pointwise bound for `θ^{12} − (1+2q)^{12}` (twelve-square identity + eta-product bound) -/
theorem heat_le_of_twelveSquare (hT : TwelveSquareIdentity) {s : ℝ} (hs : 0 < s) :
    theta (Real.exp (-s)) ^ 12 - (1 + 2 * Real.exp (-s)) ^ 12
      ≤ 8 * lamA 1 s - 512 * lamA 4 s - polyD s := by
  set q := Real.exp (-s) with hq
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have h := hT q hq0 hq1
  have hA1 : ∑' m : ℕ+, sigma5 m * q ^ (m : ℕ) = lamA 1 s := by
    unfold lamA; refine tsum_congr fun m => ?_
    rw [hq, exp_neg_pow]; congr 2; ring
  have hA4 : ∑' m : ℕ+, sigma5 m * q ^ (4 * (m : ℕ)) = lamA 4 s := by
    unfold lamA; refine tsum_congr fun m => ?_
    rw [hq, exp_neg_pow]; congr 2; push_cast; ring
  have hP := eulerProd_bounds hq0.le hq1
  have hq2 := q_mul_one_sub_sq_pow_le q hq0.le hq1.le
  have hpoly : polyD s = (1 + 2 * q) ^ 12 - 1 - 16 * (q - 12 * q ^ 3 + 66 * q ^ 5) := by
    rw [poly_eq_dsum q]
    unfold polyD
    refine sum_congr rfl fun t _ => ?_
    rw [hq, exp_neg_pow]
  rw [hA1, hA4] at h
  rw [hpoly]
  have : q * ∏' m : ℕ+, (1 - q ^ (2 * (m : ℕ))) ^ 12 ≤ q * (1 - q ^ 2) ^ 12 :=
    mul_le_mul_of_nonneg_left hP.2 hq0.le
  nlinarith [h, this, hq2]

theorem G_le_lambert_of_twelveSquare (hT : TwelveSquareIdentity) {η : ℝ} (hη : 0 < η) :
    G η ≤ 8 * lambertSum (Real.exp (-η)) - lambertSum (Real.exp (-(4 * η))) / 8
      - ∑ t ∈ Finset.Icc 1 12, dCoeffR t * Real.exp (-η * t) := by
  obtain ⟨I1, V1⟩ := lambert_integral η 1 one_pos (fun m : ℕ+ => sigma5 m) (fun m => sigma5_nonneg _)
    (summable_lam hη one_pos)
  obtain ⟨I4, V4⟩ := lambert_integral η 4 (by norm_num) (fun m : ℕ+ => sigma5 m) (fun m => sigma5_nonneg _)
    (summable_lam hη (by norm_num))
  have It : ∀ t ∈ Finset.Icc 1 12, Integrable (fun s : ℝ => (dCoeffR t * (t : ℝ) ^ 6) *
      ((s - η) ^ 5 * Real.exp (-s * t))) (volume.restrict (Ioi η)) := by
    intro t ht
    have : (0 : ℝ) < t := by
      have := (Finset.mem_Icc.1 ht).1; exact_mod_cast this
    exact (integrableOn_pow_five_exp this η).const_mul _
  have hBeq : ∀ s : ℝ, (s - η) ^ 5 * (8 * lamA 1 s - 512 * lamA 4 s - polyD s)
      = 8 * ((s - η) ^ 5 * ∑' m : ℕ+, sigma5 m * Real.exp (-s * (1 * (m : ℕ))))
        - 512 * ((s - η) ^ 5 * ∑' m : ℕ+, sigma5 m * Real.exp (-s * (4 * (m : ℕ))))
        - ∑ t ∈ Finset.Icc 1 12, (dCoeffR t * (t : ℝ) ^ 6) * ((s - η) ^ 5 * Real.exp (-s * t)) := by
    intro s
    unfold lamA polyD
    rw [mul_sub, mul_sub, Finset.mul_sum]
    have : ∀ t ∈ Finset.Icc 1 12, (s - η) ^ 5 * (dCoeffR t * (t : ℝ) ^ 6 * Real.exp (-s * t))
        = (dCoeffR t * (t : ℝ) ^ 6) * ((s - η) ^ 5 * Real.exp (-s * t)) := fun t _ => by ring
    rw [Finset.sum_congr rfl this]
    ring
  have I1' : Integrable (fun s : ℝ => 8 * ((s - η) ^ 5 * ∑' m : ℕ+, sigma5 m * Real.exp (-s * (1 * (m : ℕ)))))
      (volume.restrict (Ioi η)) := I1.const_mul 8
  have I4' : Integrable (fun s : ℝ => 512 * ((s - η) ^ 5 * ∑' m : ℕ+, sigma5 m * Real.exp (-s * (4 * (m : ℕ)))))
      (volume.restrict (Ioi η)) := I4.const_mul 512
  have I14 : Integrable (fun s : ℝ => 8 * ((s - η) ^ 5 * ∑' m : ℕ+, sigma5 m * Real.exp (-s * (1 * (m : ℕ))))
        - 512 * ((s - η) ^ 5 * ∑' m : ℕ+, sigma5 m * Real.exp (-s * (4 * (m : ℕ)))))
      (volume.restrict (Ioi η)) := I1'.sub I4'
  have IP : Integrable (fun s : ℝ => ∑ t ∈ Finset.Icc 1 12, (dCoeffR t * (t : ℝ) ^ 6) *
      ((s - η) ^ 5 * Real.exp (-s * t))) (volume.restrict (Ioi η)) := integrable_finsetSum _ It
  have IB : Integrable (fun s : ℝ => (s - η) ^ 5 * (8 * lamA 1 s - 512 * lamA 4 s - polyD s))
      (volume.restrict (Ioi η)) := by
    simp_rw [hBeq]
    exact I14.sub IP
  have VB : ∫ s in Ioi η, (s - η) ^ 5 * (8 * lamA 1 s - 512 * lamA 4 s - polyD s)
      = 8 * (120 * lambertSum (Real.exp (-η))) - 512 * (120 * (lambertSum (Real.exp (-(4 * η))) / 4096))
        - ∑ t ∈ Finset.Icc 1 12, 120 * (dCoeffR t * Real.exp (-η * t)) := by
    simp_rw [hBeq]
    rw [integral_sub I14 IP, integral_sub I1' I4', integral_const_mul, integral_const_mul,
      integral_finsetSum _ It, V1, V4, lam1_eq, lam4_eq]
    congr 1
    refine sum_congr rfl fun t ht => ?_
    have htpos : (0 : ℝ) < t := by
      have := (Finset.mem_Icc.1 ht).1; exact_mod_cast this
    rw [integral_const_mul, integral_pow_five_exp htpos η]
    field_simp
  -- main comparison
  have hmain : ∫ s in Ioi η, (s - η) ^ 5 *
        (theta (Real.exp (-s)) ^ 12 - (1 + 2 * Real.exp (-s)) ^ 12)
      ≤ ∫ s in Ioi η, (s - η) ^ 5 * (8 * lamA 1 s - 512 * lamA 4 s - polyD s) := by
    refine integral_mono_of_nonneg ?_ IB ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      have hs0 : 0 < s := hη.trans hs
      have hnn : 0 ≤ theta (Real.exp (-s)) ^ 12 - (1 + 2 * Real.exp (-s)) ^ 12 :=
        (hasSum_heat_off_cube hs0).nonneg (fun k => Set.indicator_nonneg
          (fun _ _ => (Real.exp_pos _).le) k)
      exact mul_nonneg (pow_nonneg (sub_nonneg.2 (le_of_lt hs)) 5) hnn
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      have hs0 : 0 < s := hη.trans hs
      exact mul_le_mul_of_nonneg_left (heat_le_of_twelveSquare hT hs0)
        (pow_nonneg (sub_nonneg.2 (le_of_lt hs)) 5)
  rw [G_eq_mellin hη]
  rw [VB] at hmain
  have e : ∑ t ∈ Finset.Icc 1 12, 120 * (dCoeffR t * Real.exp (-η * t))
      = 120 * ∑ t ∈ Finset.Icc 1 12, dCoeffR t * Real.exp (-η * t) := by rw [Finset.mul_sum]
  rw [e] at hmain
  linarith

end BecknerOnofri.V2.ThetaTail
