module

public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import BecknerOnofri.V2.ThetaTail.RationalCertificates

@[expose] public section

/-! # Real-analytic soundness of the exponential certificates (Appendix B.1)

* `E_M(z) ≤ e^{-z}` for odd `M` and `z ≥ 0` ("Taylor's integral remainder");
* `e^z ≤ ∑_{k≤M} z^k/k! + z^{M+1}/(M+1)!/(1 - z/(M+2))` for `0 ≤ z < M+2`. -/
noncomputable section
open Finset Filter
namespace BecknerOnofri.V2.ThetaTail

/-- real version of `E_M`. -/
def expAltR (M : ℕ) (z : ℝ) : ℝ := ∑ k ∈ range (M + 1), (-z) ^ k / (k.factorial : ℝ)

theorem hasDerivAt_expAltR (M : ℕ) (z : ℝ) :
    HasDerivAt (expAltR (M + 1)) (-expAltR M z) z := by
  unfold expAltR
  have h : (fun w : ℝ => ∑ k ∈ range (M + 1 + 1), (-w) ^ k / (k.factorial : ℝ))
      = fun w => ∑ k ∈ range (M + 1), (-w) ^ (k + 1) / ((k + 1).factorial : ℝ) + 1 := by
    ext w
    rw [sum_range_succ' (fun k => (-w) ^ k / (k.factorial : ℝ))]
    simp
  show HasDerivAt (fun w : ℝ => ∑ k ∈ range (M + 1 + 1), (-w) ^ k / (k.factorial : ℝ)) _ z
  rw [h]
  have hk : ∀ k ∈ range (M + 1),
      HasDerivAt (fun w : ℝ => (-w) ^ (k + 1) / ((k + 1).factorial : ℝ))
        (-((-z) ^ k / (k.factorial : ℝ))) z := by
    intro k _
    have h1 : HasDerivAt (fun w : ℝ => -w) (-1) z := (hasDerivAt_id z).neg
    have h2 := (h1.fun_pow (k + 1)).div_const ((k + 1).factorial : ℝ)
    convert h2 using 1
    have hf : ((k + 1).factorial : ℝ) = (k + 1) * k.factorial := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hk0 : (k.factorial : ℝ) ≠ 0 := by positivity
    simp only [Nat.add_sub_cancel]
    rw [hf]
    push_cast
    field_simp
  have := (HasDerivAt.fun_sum hk).add_const 1
  convert this using 1
  simp [sum_neg_distrib]

theorem expAltR_cases (M : ℕ) : ∀ z : ℝ, 0 ≤ z →
    (Odd M → expAltR M z ≤ Real.exp (-z)) ∧ (Even M → Real.exp (-z) ≤ expAltR M z) := by
  induction M with
  | zero =>
    intro z hz
    refine ⟨fun h => by simp at h, fun _ => ?_⟩
    have : Real.exp (-z) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    simpa [expAltR] using this
  | succ M ih =>
    intro z hz
    -- g z = exp(-z) - E_{M+1}(z)
    have hderiv : ∀ w : ℝ, HasDerivAt (fun w => Real.exp (-w) - expAltR (M + 1) w)
        (-Real.exp (-w) + expAltR M w) w := by
      intro w
      have h1 : HasDerivAt (fun w : ℝ => Real.exp (-w)) (-Real.exp (-w)) w := by
        have := (Real.hasDerivAt_exp (-w)).comp w (hasDerivAt_id w).neg
        simpa [Function.comp_def] using this
      have := h1.sub (hasDerivAt_expAltR M w)
      convert this using 1; ring
    have hcont : Continuous (fun w : ℝ => Real.exp (-w) - expAltR (M + 1) w) :=
      continuous_iff_continuousAt.2 fun w => (hderiv w).continuousAt
    have g0 : Real.exp (-0 : ℝ) - expAltR (M + 1) 0 = 0 := by
      simp [expAltR, Finset.sum_range_succ', zero_pow]
    rcases Nat.even_or_odd M with hM | hM
    · -- E_M ≥ exp(-z), derivative ≥ 0, g ≥ 0, so E_{M+1} ≤ exp(-z)
      have hmono : MonotoneOn (fun w : ℝ => Real.exp (-w) - expAltR (M + 1) w) (Set.Ici 0) := by
        apply monotoneOn_of_deriv_nonneg (convex_Ici 0) hcont.continuousOn
          (fun w _ => (hderiv w).differentiableAt.differentiableWithinAt)
        intro w hw
        rw [(hderiv w).deriv]
        have := (ih w (by simpa using interior_subset hw)).2 hM
        linarith
      have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hz) hz
      simp only at this
      rw [g0] at this
      exact ⟨fun _ => by linarith, fun h => absurd h (by simpa using hM.add_one)⟩
    · have hmono : AntitoneOn (fun w : ℝ => Real.exp (-w) - expAltR (M + 1) w) (Set.Ici 0) := by
        apply antitoneOn_of_deriv_nonpos (convex_Ici 0) hcont.continuousOn
          (fun w _ => (hderiv w).differentiableAt.differentiableWithinAt)
        intro w hw
        rw [(hderiv w).deriv]
        have := (ih w (by simpa using interior_subset hw)).1 hM
        linarith
      have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hz) hz
      simp only at this
      rw [g0] at this
      exact ⟨fun h => absurd h (by simpa using hM.add_one), fun _ => by linarith⟩

theorem expAltR_le_exp_neg (M : ℕ) (hM : Odd M) (z : ℝ) (hz : 0 ≤ z) :
    expAltR M z ≤ Real.exp (-z) := (expAltR_cases M z hz).1 hM

/-- `E_M` (rational) is below `exp(-z)` for odd `M`. -/
theorem expAlt_le_exp_neg (M : ℕ) (hM : Odd M) (z : ℚ) (hz : 0 ≤ z) :
    ((expAlt M z : ℚ) : ℝ) ≤ Real.exp (-(z : ℝ)) := by
  have := expAltR_le_exp_neg M hM (z : ℝ) (by exact_mod_cast hz)
  unfold expAlt
  unfold expAltR at this
  push_cast
  exact this

/-- upper bound for the exponential. -/
theorem exp_le_expUpper (M : ℕ) (z : ℝ) (h0 : 0 ≤ z) (h1 : z < M + 2) :
    Real.exp z ≤ (∑ k ∈ range (M + 1), z ^ k / (k.factorial : ℝ))
      + z ^ (M + 1) / ((M + 1).factorial : ℝ) / (1 - z / ((M : ℝ) + 2)) := by
  have hr0 : 0 ≤ z / ((M : ℝ) + 2) := by positivity
  have hr1 : z / ((M : ℝ) + 2) < 1 := by
    rw [div_lt_one (by positivity)]; exact h1
  have hs : HasSum (fun n : ℕ => z ^ n / (n.factorial : ℝ)) (Real.exp z) := by
    have := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) z
    simpa [Real.exp_eq_exp_ℝ] using this
  have hsplit := hs.summable.sum_add_tsum_nat_add (M + 1)
  rw [hs.tsum_eq] at hsplit
  have hgeo : HasSum (fun j : ℕ => z ^ (M + 1) / ((M + 1).factorial : ℝ) * (z / ((M : ℝ) + 2)) ^ j)
      (z ^ (M + 1) / ((M + 1).factorial : ℝ) / (1 - z / ((M : ℝ) + 2))) := by
    have := (hasSum_geometric_of_lt_one hr0 hr1).mul_left (z ^ (M + 1) / ((M + 1).factorial : ℝ))
    simpa [div_eq_mul_inv] using this
  have hT : ∑' i : ℕ, z ^ (i + (M + 1)) / ((i + (M + 1)).factorial : ℝ)
      ≤ z ^ (M + 1) / ((M + 1).factorial : ℝ) / (1 - z / ((M : ℝ) + 2)) := by
    rw [← hgeo.tsum_eq]
    refine Summable.tsum_le_tsum (fun j => ?_) (hs.summable.comp_injective (add_left_injective (M + 1))) hgeo.summable
    -- z^(j+M+1)/(j+M+1)! ≤ z^(M+1)/(M+1)! (z/(M+2))^j
    have hf : ((M + 1).factorial : ℝ) * ((M : ℝ) + 2) ^ j ≤ ((j + (M + 1)).factorial : ℝ) := by
      have := Nat.factorial_mul_pow_le_factorial (m := M + 1) (n := j)
      rw [add_comm j (M + 1)]
      exact_mod_cast (by simpa using this : (M + 1).factorial * (M + 2) ^ j ≤ (M + 1 + j).factorial)
    have hpos : (0 : ℝ) < ((M + 1).factorial : ℝ) * ((M : ℝ) + 2) ^ j := by positivity
    calc z ^ (j + (M + 1)) / ((j + (M + 1)).factorial : ℝ)
        ≤ z ^ (j + (M + 1)) / (((M + 1).factorial : ℝ) * ((M : ℝ) + 2) ^ j) :=
          div_le_div_of_nonneg_left (by positivity) hpos hf
      _ = _ := by
          rw [div_pow, pow_add]; field_simp
  linarith

theorem exp_lt_five_of_exp85 : Real.exp (8 / 5) < 5 := by
  have h := exp_le_expUpper 8 (8 / 5) (by norm_num) (by norm_num)
  have hq : expUpper 8 (8 / 5) < 5 := exp85_upper
  have hc : ((expUpper 8 (8 / 5) : ℚ) : ℝ) < 5 := by exact_mod_cast hq
  unfold expUpper at hc
  push_cast at hc
  linarith

end BecknerOnofri.V2.ThetaTail
