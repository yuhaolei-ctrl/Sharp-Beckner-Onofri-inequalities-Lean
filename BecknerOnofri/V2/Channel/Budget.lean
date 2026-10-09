module

public import BecknerOnofri.V2.Channel.ConditionalExplicit
public import BecknerOnofri.V2.Channel.CountLaw
public import BecknerOnofri.SpinEntropyChain
public import BecknerOnofri.ConditionalJensen
public import BecknerOnofri.ConditionalExpectations

@[expose] public section

/-!
# Entropy chain rule, Jensen, and the discrete comparison (work package G10, part (d))

Source: proof of Proposition 5.12(i), from `eq:section5-channel-chain-and-Jensen` to
`eq:section5-channel-discrete-entropy`.

* `entropy_chain_rule_full` (old, generic): `Ent(ρ) = Σ_i E[Ent(p_i(·|x_{<i}))]`.
* `integrate_budget`: integration of the pointwise Lemma 5.16 inequality against the joint density,
  Jensen for squares (`E[r_{i,n}²] ≥ E[r_{i,n}]²`) and Jensen for the convex `ψ` on `[0,1]`
  (`E ψ(t_i) ≥ ψ(E t_i)`); the infinite Fourier sum is handled by finite partial sums `s` with
  nonnegative terms.
* `nonneg_budget_limit`: passage from all partial sums to the series by monotone convergence.
* `channel_entropy_core`: the assembled inequality `eq:section5-channel-continuous-entropy` together
  with the discrete comparison `eq:section5-channel-discrete-entropy`
  (`Spin.channel_entropy_le_conditional`: conditional independence of the current spin and the
  earlier spins given the earlier positions, the tower property and conditional Jensen for `I_B`).
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Function
open scoped BigOperators ContDiff
namespace BecknerOnofri.V2.Channel
open BecknerOnofri.HighDim BecknerOnofri.HighDim.ConditionalEntropy BecknerOnofri.HighDim.EntropyShearer
open BecknerOnofri.HighDim.Spin (binaryCost conditional_binaryCost_bounded)

theorem bounded_comp_Icc' {d : ℕ} {u : Torus d → ℝ} (hu : BoundedMeasurable u)
    {a b : ℝ} (hr : ∀ x, u x ∈ Icc a b) (ψ : ℝ → ℝ) (hc : ContinuousOn ψ (Icc a b)) :
    BoundedMeasurable (fun x => ψ (u x)) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hc.norm
  exact ⟨hc.domRestrict.measurable.comp (hu.1.subtype_mk (h := hr)), C,
    fun x => hC (mem_image_of_mem (fun y => ‖ψ y‖) (hr x))⟩

theorem nonneg_budget_limit (g : ℕ → ℝ) (hg : ∀ n, 0 ≤ g n)
    (A B c : ℝ) (hc : 0 < c) (hb : ∀ s : Finset ℕ, A + c * ∑ n ∈ s, g n ≤ B) :
    Summable g ∧ A + c * ∑' n, g n ≤ B := by
  have hsum (s : Finset ℕ) : (∑ n ∈ s, g n) ≤ (B - A) / c := by
    apply (le_div_iff₀ hc).mpr
    have h := hb s
    nlinarith
  refine ⟨summable_of_sum_le hg hsum, ?_⟩
  have h := (le_div_iff₀ hc).mp (Real.tsum_le_of_sum_le hg hsum)
  nlinarith

/-- Integration of the pointwise bound against the joint density, for one coordinate and a finite
set `s` of higher harmonics. -/
theorem integrate_budget {f : Torus 12 → ℝ} (hf : PositiveBounded f)
    (hm : (∫ x, f x ∂torusMeasure 12) = 1) (i : Fin 12) (s : Finset ℕ)
    (hr : ∀ x, conditionalCosineMoment f i 1 x ∈ Icc (0 : ℝ) 1)
    (hb : ∀ x,
      2 * binaryCost (conditionalCosineMoment f i 1 x) +
      BecknerOnofri.V2.Circle.psi (conditionalCosineMoment f i 1 x) +
      (1 / 40) * (conditionalCosineMoment f i 2 x) ^ 2 +
      (2 / 15) * (conditionalCosineMoment f i 3 x) ^ 2 +
      (27 / 40) * (∑ n ∈ s, (conditionalCosineMoment f i (n + 4) x) ^ 2 / ((n : ℝ) + 4)) ≤
        conditionalEntropy f i x) :
    2 * (∫ x, f x * binaryCost (conditionalCosineMoment f i 1 x) ∂torusMeasure 12) +
      BecknerOnofri.V2.Circle.psi (∫ x, f x * (fourier 1 (x i)).re ∂torusMeasure 12) +
      (1 / 40) * (∫ x, f x * (fourier 2 (x i)).re ∂torusMeasure 12) ^ 2 +
      (2 / 15) * (∫ x, f x * (fourier 3 (x i)).re ∂torusMeasure 12) ^ 2 +
      (27 / 40) * (∑ n ∈ s,
        (∫ x, f x * (fourier ((n + 4 : ℕ) : ℤ) (x i)).re ∂torusMeasure 12) ^ 2 / ((n : ℝ) + 4)) ≤
        ∫ x, f x * conditionalEntropy f i x ∂torusMeasure 12 := by
  let ψ := BecknerOnofri.V2.Circle.psi
  let R := fun n => conditionalCosineMoment f i n
  let B := fun x => f x * binaryCost (R 1 x)
  let P := fun x => f x * ψ (R 1 x)
  let Q := fun n x => f x * (R n x) ^ 2
  have hψc : ContinuousOn ψ (Icc (0 : ℝ) 1) := BecknerOnofri.V2.Circle.psi_continuousOn
  have hψv : ConvexOn ℝ (Icc (0 : ℝ) 1) ψ := BecknerOnofri.V2.Circle.psi_convexOn
  have hB : Integrable B (torusMeasure 12) :=
    (hf.bounded.mul (conditional_binaryCost_bounded hf i)).integrable
  have hP : Integrable P (torusMeasure 12) :=
    (hf.bounded.mul (bounded_comp_Icc' (conditional_moment_bounded hf i 1) hr ψ hψc)).integrable
  have hQ (n : ℕ) : Integrable (Q n) (torusMeasure 12) := by
    simpa only [Q, R, pow_two] using
      (hf.bounded.mul ((conditional_moment_bounded hf i n).mul
        (conditional_moment_bounded hf i n))).integrable
  have hsum : Integrable (fun x => ∑ n ∈ s, Q (n + 4) x / ((n : ℝ) + 4)) (torusMeasure 12) :=
    integrable_finsetSum s (fun n _ => (hQ (n + 4)).div_const _)
  have hent := (hf.bounded.mul (conditional_entropy_bounded hf i)).integrable
  have hmult (x : Torus 12) :
      2 * B x + P x + (1 / 40) * Q 2 x + (2 / 15) * Q 3 x +
        (27 / 40) * (∑ n ∈ s, Q (n + 4) x / ((n : ℝ) + 4)) ≤ f x * conditionalEntropy f i x := by
    have h := mul_le_mul_of_nonneg_left (hb x) (hf.pos x).le
    dsimp only [B, P, Q, R, ψ]
    have ht : (∑ n ∈ s, f x * (conditionalCosineMoment f i (n + 4) x) ^ 2 / ((n : ℝ) + 4)) =
        f x * (∑ n ∈ s, (conditionalCosineMoment f i (n + 4) x) ^ 2 / ((n : ℝ) + 4)) := by
      simp only [Finset.mul_sum, mul_div_assoc]
    rw [ht]
    nlinarith
  have hI1 : Integrable (fun x => 2 * B x + P x) (torusMeasure 12) := (hB.const_mul 2).add hP
  have hI2 : Integrable (fun x => 2 * B x + P x + (1 / 40) * Q 2 x) (torusMeasure 12) :=
    hI1.add ((hQ 2).const_mul _)
  have hI3 : Integrable (fun x => 2 * B x + P x + (1 / 40) * Q 2 x + (2 / 15) * Q 3 x)
      (torusMeasure 12) := hI2.add ((hQ 3).const_mul _)
  have hI4 : Integrable (fun x => 2 * B x + P x + (1 / 40) * Q 2 x + (2 / 15) * Q 3 x +
      (27 / 40) * (∑ n ∈ s, Q (n + 4) x / ((n : ℝ) + 4))) (torusMeasure 12) :=
    hI3.add (hsum.const_mul _)
  have h := integral_mono hI4 hent hmult
  rw [integral_add hI3 (hsum.const_mul _), integral_add hI2 ((hQ 3).const_mul _),
    integral_add hI1 ((hQ 2).const_mul _), integral_add (hB.const_mul 2) hP] at h
  simp only [integral_const_mul] at h
  rw [integral_finsetSum s (fun n _ => (hQ (n + 4)).div_const _)] at h
  simp only [integral_div] at h
  have hψ := conditional_moment_jensen hf hm i 1 hr ψ hψc hψv
  have h2 := conditional_moment_full_square hf hm i 2
  have h3 := conditional_moment_full_square hf hm i 3
  have ht : (∑ n ∈ s, (∫ x, f x * (fourier ((n + 4 : ℕ) : ℤ) (x i)).re ∂torusMeasure 12) ^ 2 /
        ((n : ℝ) + 4)) ≤ ∑ n ∈ s, (∫ x, Q (n + 4) x ∂torusMeasure 12) / ((n : ℝ) + 4) := by
    apply Finset.sum_le_sum
    intro n _
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact conditional_moment_full_square hf hm i (n + 4)
  dsimp only [B, P, Q, R] at h
  norm_num only [Nat.cast_one, Nat.cast_ofNat] at hψ h2 h3
  dsimp only [Q, R] at ht
  linarith

end BecknerOnofri.V2.Channel
