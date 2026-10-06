module

public import BecknerOnofri.SelectedChannelEntropy
public import BecknerOnofri.SelectedSpinEntropy
public import BecknerOnofri.SelectedEntropyGap
public import BecknerOnofri.JensenRemainder

@[expose] public section

/-!
# Proposition 5.12(i): conditional entropy with a Jensen remainder

The one-coordinate estimates of Lemma 5.15–5.17 are integrated against the density. In place
of convexity of `ψ`, Lemma 5.18 gives
`E ψ(t_i) ≥ ψ(t) + η(t) (E I_B(t_i) - I_B(t))`, and the discrete entropy chain rule bounds
`∑_i E I_B(t_i)` below by the spin relative entropy (eq:section5-global-channel-entropy).
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set
open scoped BigOperators

namespace BecknerOnofri.HighDim.ConditionalEntropy
open EntropyShearer

/-- Lemma 5.18 integrated against a probability density, with `S` the conditional mean. -/
theorem conditional_jensen_remainder {d : ℕ} {f : Torus d → ℝ}
    (hf : PositiveBounded f) (hm : (∫ x, f x ∂torusMeasure d) = 1) (i : Fin d)
    (hr : ∀ x, conditionalCosineMoment f i 1 x ∈ Ico (0 : ℝ) 1) :
    Spin.psi (∫ x, f x * (fourier 1 (x i)).re ∂torusMeasure d) +
      Spin.eta (∫ x, f x * (fourier 1 (x i)).re ∂torusMeasure d) *
        ((∫ x, f x * Spin.binaryCost (conditionalCosineMoment f i 1 x) ∂torusMeasure d) -
          Spin.binaryCost (∫ x, f x * (fourier 1 (x i)).re ∂torusMeasure d)) ≤
      ∫ x, f x * Spin.psi (conditionalCosineMoment f i 1 x) ∂torusMeasure d := by
  have htower := conditional_moment_full_tower hf i 1
  norm_num only [Nat.cast_one] at htower
  rw [← htower]
  set S := conditionalCosineMoment f i 1
  set t := ∫ x, f x * S x ∂torusMeasure d
  have hS := conditional_moment_bounded hf i 1
  have hSI : ∀ x, S x ∈ Icc (0 : ℝ) 1 := fun x => ⟨(hr x).1, (hr x).2.le⟩
  have hfS : Integrable (fun x => f x * S x) (torusMeasure d) := (hf.bounded.mul hS).integrable
  have hpsi : Integrable (fun x => f x * Spin.psi (S x)) (torusMeasure d) :=
    (hf.bounded.mul (bounded_comp_Icc hS hSI _
      (by unfold Spin.psi; fun_prop : Continuous Spin.psi).continuousOn)).integrable
  have hbin : Integrable (fun x => f x * Spin.binaryCost (S x)) (torusMeasure d) :=
    (hf.bounded.mul (bounded_comp_Icc hS hSI _ Spin.binaryCost_continuous.continuousOn)).integrable
  have hfi : Integrable f (torusMeasure d) := hf.bounded.integrable
  -- `0 ≤ t < 1`
  have ht0 : 0 ≤ t := integral_nonneg (fun x => mul_nonneg (hf.pos x).le (hr x).1)
  have ht1 : t < 1 := by
    have hpos : 0 < ∫ x, f x * (1 - S x) ∂torusMeasure d := by
      rw [integral_pos_iff_support_of_nonneg (fun x => mul_nonneg (hf.pos x).le
        (sub_nonneg.mpr (hr x).2.le)) ((hfi.sub hfS).congr (by
          filter_upwards with x; simp; ring))]
      have : Function.support (fun x => f x * (1 - S x)) = univ := by
        ext x
        simp only [Function.mem_support, mem_univ, iff_true]
        exact (mul_pos (hf.pos x) (sub_pos.mpr (hr x).2)).ne'
      rw [this]
      simp
    have he : (∫ x, f x * (1 - S x) ∂torusMeasure d) = 1 - t := by
      rw [show (fun x => f x * (1 - S x)) = fun x => f x - f x * S x by ext x; ring,
        integral_sub hfi hfS, hm]
    linarith
  -- integrate the pointwise remainder
  have hgap : 0 ≤ ∫ x, f x * Spin.jensenGap t (S x) ∂torusMeasure d :=
    integral_nonneg (fun x => mul_nonneg (hf.pos x).le
      (Spin.jensenGap_nonneg ht0 ht1 (hr x).1 (hr x).2.le))
  set c := Spin.psi t - Spin.psiSlope t * t - Spin.eta t * (Spin.binaryCost t -
    Spin.binaryCostSlope t * t)
  set k := Spin.psiSlope t - Spin.eta t * Spin.binaryCostSlope t
  have hexp : (fun x => f x * Spin.jensenGap t (S x)) = fun x =>
      (f x * Spin.psi (S x) - Spin.eta t * (f x * Spin.binaryCost (S x)) - c * f x) -
        k * (f x * S x) := by
    ext x
    simp only [c, k]
    unfold Spin.jensenGap
    ring
  have h1 : Integrable (fun x => f x * Spin.psi (S x) - Spin.eta t * (f x * Spin.binaryCost (S x)))
      (torusMeasure d) := hpsi.sub (hbin.const_mul _)
  have h2 : Integrable (fun x => f x * Spin.psi (S x) - Spin.eta t * (f x * Spin.binaryCost (S x)) -
      c * f x) (torusMeasure d) := h1.sub (hfi.const_mul _)
  rw [hexp, integral_sub h2 (hfS.const_mul _), integral_sub h1 (hfi.const_mul _),
    integral_sub hpsi (hbin.const_mul _), integral_const_mul, integral_const_mul,
    integral_const_mul, hm] at hgap
  simp only [c, k] at hgap
  nlinarith

/-- The one-coordinate budget integrated against the density, with the Jensen remainder. -/
theorem integrate_conditional_budget_eta {f : Torus 12 → ℝ} (hf : PositiveBounded f)
    (hm : (∫ x, f x ∂torusMeasure 12) = 1) (i : Fin 12) (s : Finset ℕ)
    (hr : ∀ x, conditionalCosineMoment f i 1 x ∈ Ico (0 : ℝ) 1)
    (hb : ∀ x,
      2 * Spin.binaryCost (conditionalCosineMoment f i 1 x) +
      Spin.psi (conditionalCosineMoment f i 1 x) +
      (21/1000) * (conditionalCosineMoment f i 2 x)^2 +
      (67/100) * (∑ n ∈ s, (conditionalCosineMoment f i (n+3) x)^2 / (n+3 : ℝ)) ≤
        conditionalEntropy f i x) :
    2 * (∫ x, f x * Spin.binaryCost (conditionalCosineMoment f i 1 x) ∂torusMeasure 12) +
      (Spin.psi (∫ x, f x * (fourier 1 (x i)).re ∂torusMeasure 12) +
        Spin.eta (∫ x, f x * (fourier 1 (x i)).re ∂torusMeasure 12) *
          ((∫ x, f x * Spin.binaryCost (conditionalCosineMoment f i 1 x) ∂torusMeasure 12) -
            Spin.binaryCost (∫ x, f x * (fourier 1 (x i)).re ∂torusMeasure 12))) +
      (21/1000) * (∫ x, f x * (fourier 2 (x i)).re ∂torusMeasure 12)^2 +
      (67/100) * (∑ n ∈ s, (∫ x, f x * (fourier (n+3 : ℤ) (x i)).re ∂torusMeasure 12)^2 /
        (n+3 : ℝ)) ≤
        ∫ x, f x * conditionalEntropy f i x ∂torusMeasure 12 := by
  have hpc : ContinuousOn Spin.psi (Icc (0 : ℝ) 1) :=
    (by unfold Spin.psi; fun_prop : Continuous Spin.psi).continuousOn
  -- the convex-ψ budget with ψ replaced by itself, then Jensen replaced by the remainder
  let R := fun n => conditionalCosineMoment f i n
  let B := fun x => f x * Spin.binaryCost (R 1 x)
  let P := fun x => f x * Spin.psi (R 1 x)
  let Q := fun n x => f x * (R n x)^2
  have hrI : ∀ x, R 1 x ∈ Icc (0 : ℝ) 1 := fun x => ⟨(hr x).1, (hr x).2.le⟩
  have hB : Integrable B (torusMeasure 12) :=
    (hf.bounded.mul (Spin.conditional_binaryCost_bounded hf i)).integrable
  have hP : Integrable P (torusMeasure 12) :=
    (hf.bounded.mul (bounded_comp_Icc (conditional_moment_bounded hf i 1) hrI _ hpc)).integrable
  have hQ (n : ℕ) : Integrable (Q n) (torusMeasure 12) := by
    simpa only [Q, R, pow_two] using
      (hf.bounded.mul ((conditional_moment_bounded hf i n).mul
        (conditional_moment_bounded hf i n))).integrable
  have hsum : Integrable (fun x => ∑ n ∈ s, Q (n+3) x / (n+3 : ℝ)) (torusMeasure 12) :=
    integrable_finsetSum s (fun n _ => (hQ (n+3)).div_const _)
  have hent := (hf.bounded.mul (conditional_entropy_bounded hf i)).integrable
  have hmult (x : Torus 12) :
      2 * B x + P x + (21/1000) * Q 2 x +
      (67/100) * (∑ n ∈ s, Q (n+3) x / (n+3 : ℝ)) ≤ f x * conditionalEntropy f i x := by
    have h := mul_le_mul_of_nonneg_left (hb x) (hf.pos x).le
    dsimp only [B, P, Q, R]
    have ht : (∑ n ∈ s, f x * (conditionalCosineMoment f i (n+3) x)^2 / (n+3 : ℝ)) =
        f x * (∑ n ∈ s, (conditionalCosineMoment f i (n+3) x)^2 / (n+3 : ℝ)) := by
      simp only [Finset.mul_sum, mul_div_assoc]
    rw [ht]
    nlinarith
  have h := integral_mono (((hB.const_mul 2).add hP).add ((hQ 2).const_mul (21/1000)) |>.add
    (hsum.const_mul (67/100))) hent hmult
  simp only [Pi.add_apply] at h
  rw [integral_add (f := fun x => 2 * B x + P x + (21/1000) * Q 2 x)
    (g := fun x => (67/100) * ∑ n ∈ s, Q (n+3) x / (n+3 : ℝ))
    (((hB.const_mul 2).add hP).add ((hQ 2).const_mul (21/1000))) (hsum.const_mul (67/100)),
    integral_add (f := fun x => 2 * B x + P x) (g := fun x => (21/1000) * Q 2 x)
      ((hB.const_mul 2).add hP) ((hQ 2).const_mul (21/1000)),
    integral_add (f := fun x => 2 * B x) (g := P) (hB.const_mul 2) hP] at h
  simp only [integral_const_mul] at h
  rw [integral_finsetSum s (fun n _ => (hQ (n+3)).div_const _)] at h
  simp only [integral_div] at h
  have hψ := conditional_jensen_remainder hf hm i hr
  have h2 := conditional_moment_full_square hf hm i 2
  have ht : (∑ n ∈ s, (∫ x, f x * (fourier (n+3 : ℤ) (x i)).re ∂torusMeasure 12)^2 / (n+3 : ℝ)) ≤
      ∑ n ∈ s, (∫ x, Q (n+3) x ∂torusMeasure 12) / (n+3 : ℝ) := by
    apply Finset.sum_le_sum
    intro n _
    apply div_le_div_of_nonneg_right _ (by positivity)
    simpa only [Nat.cast_add, Nat.cast_ofNat] using conditional_moment_full_square hf hm i (n+3)
  dsimp only [B, P, Q, R] at h
  norm_num only [Nat.cast_one, Nat.cast_ofNat] at h2
  dsimp only [Q, R] at ht
  linarith

end BecknerOnofri.HighDim.ConditionalEntropy

namespace BecknerOnofri.HighDim.SelectedNumericalModel
open Legacy.BecknerOnofri.TorusSobolev ConditionalEntropy

/-- Proposition 5.12(i) for the selected density, finite truncation of the tail sums. -/
theorem selected_channel_entropy_eta_finite {u : TorusL2 12} (hu : Selected u)
    (hminor : ∀ t ∈ Ico (0 : ℝ) 1, Spin.psi t ≤ CircleScalar.gamma t) (s : Finset ℕ) :
    2 * Spin.relativeEntropy (Spin.countLaw (Spin.channelLaw (spinDensity hu))) Spin.reference +
      12 * Spin.psi (Spin.mean (Spin.countLaw (Spin.channelLaw (spinDensity hu)))) +
      Spin.eta (Spin.mean (Spin.countLaw (Spin.channelLaw (spinDensity hu)))) *
        (Spin.relativeEntropy (Spin.countLaw (Spin.channelLaw (spinDensity hu))) Spin.reference -
          12 * Spin.binaryCost (Spin.mean (Spin.countLaw (Spin.channelLaw (spinDensity hu))))) +
      (21/1000) * (∑ i : Fin 12,
        (∫ x, (spinDensity hu).value x * (fourier 2 (x i)).re ∂torusMeasure 12)^2) +
      (67/100) * (∑ i : Fin 12, ∑ n ∈ s,
        (∫ x, (spinDensity hu).value x * (fourier (n+3 : ℤ) (x i)).re ∂torusMeasure 12)^2 /
          (n+3 : ℝ)) ≤
      entropy (spinDensity hu) := by
  set t := Spin.mean (Spin.countLaw (Spin.channelLaw (spinDensity hu)))
  have hi (i : Fin 12) := integrate_conditional_budget_eta (spinDensity_positiveBounded hu)
    (spinDensity hu).mass i s (selected_conditional_mean_range hu i)
    (fun x => selected_conditional_gamma_finite hu Spin.psi hminor i x s)
  simp only [density_axis_mean hu] at hi
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hi i)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat, Finset.sum_sub_distrib] at h
  rw [← entropy_chain_rule_full (spinDensity_positiveBounded hu) (spinDensity hu).mass] at h
  have hspin := selected_spin_entropy hu
  have heta : 0 ≤ Spin.eta t := Spin.eta_nonneg (selected_spin_mean_range hu).1
    (selected_spin_mean_range hu).2
  have hmul := mul_le_mul_of_nonneg_left hspin heta
  unfold entropy
  nlinarith

end BecknerOnofri.HighDim.SelectedNumericalModel
