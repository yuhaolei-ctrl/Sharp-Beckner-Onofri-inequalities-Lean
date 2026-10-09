module

public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Tactic

@[expose] public section

/-!
# Coherent jets: families of normalized derivatives

A *coherent jet* on a set `S ⊆ ℝ` is a family `A : ℝ → ℝ⟦X⟧` of formal power series whose `k`-th
coefficient `A_k(t)` satisfies `A_k'(t) = (k+1) A_{k+1}(t)` at every `t ∈ S`
(equivalently `d/dt (A t) = d⁄dX (A t)` coefficientwise).  Thus `A_k = A_0^{(k)} / k!`.
We prove that coherence is preserved by `+`, `-`, constants, scalar multiples, products,
reciprocals (where the constant coefficient does not vanish) and logarithms (where it does not
vanish), and the first-order and order-`n` mean value (Lagrange) theorems for coherent jets.
-/

namespace BecknerOnofri.V2.Interval

open PowerSeries Finset

/-- `A` has series derivative `A'` at `t`: every coefficient function is differentiable. -/
def HasSD (A : ℝ → ℝ⟦X⟧) (A' : ℝ⟦X⟧) (t : ℝ) : Prop :=
  ∀ n, HasDerivAt (fun s => coeff n (A s)) (coeff n A') t

/-- Coherence on a set. -/
def Coh (S : Set ℝ) (A : ℝ → ℝ⟦X⟧) : Prop := ∀ t ∈ S, HasSD A (d⁄dX (A t)) t

namespace HasSD

theorem add {A B : ℝ → ℝ⟦X⟧} {A' B' : ℝ⟦X⟧} {t : ℝ} (hA : HasSD A A' t) (hB : HasSD B B' t) :
    HasSD (fun s => A s + B s) (A' + B') t := fun n => by
  simpa only [map_add] using (hA n).fun_add (hB n)

theorem neg {A : ℝ → ℝ⟦X⟧} {A' : ℝ⟦X⟧} {t : ℝ} (hA : HasSD A A' t) :
    HasSD (fun s => -A s) (-A') t := fun n => by
  simpa only [map_neg] using (hA n).fun_neg

theorem sub {A B : ℝ → ℝ⟦X⟧} {A' B' : ℝ⟦X⟧} {t : ℝ} (hA : HasSD A A' t) (hB : HasSD B B' t) :
    HasSD (fun s => A s - B s) (A' - B') t := fun n => by
  simpa only [map_sub] using (hA n).fun_sub (hB n)

theorem const (φ : ℝ⟦X⟧) (t : ℝ) : HasSD (fun _ => φ) 0 t := fun n => by
  simpa using hasDerivAt_const t (coeff n φ)

theorem smul {A : ℝ → ℝ⟦X⟧} {A' : ℝ⟦X⟧} {t : ℝ} (c : ℝ) (hA : HasSD A A' t) :
    HasSD (fun s => C c * A s) (C c * A') t := fun n => by
  simpa [coeff_C_mul] using (hA n).const_mul c

theorem mul {A B : ℝ → ℝ⟦X⟧} {A' B' : ℝ⟦X⟧} {t : ℝ} (hA : HasSD A A' t) (hB : HasSD B B' t) :
    HasSD (fun s => A s * B s) (A' * B t + A t * B') t := fun n => by
  have : ∀ s, coeff n (A s * B s) =
      ∑ p ∈ antidiagonal n, coeff p.1 (A s) * coeff p.2 (B s) := fun s => coeff_mul n _ _
  simp only [this]
  have h := HasDerivAt.fun_sum (u := antidiagonal n) (x := t)
    (A := fun p s => coeff p.1 (A s) * coeff p.2 (B s))
    (A' := fun p => coeff p.1 A' * coeff p.2 (B t) + coeff p.1 (A t) * coeff p.2 B')
    (fun p _ => (hA p.1).mul (hB p.2))
  convert h using 1
  rw [map_add, coeff_mul, coeff_mul, sum_add_distrib]

theorem deriv {A : ℝ → ℝ⟦X⟧} {A' : ℝ⟦X⟧} {t : ℝ} (hA : HasSD A A' t) :
    HasSD (fun s => d⁄dX (A s)) (d⁄dX A') t := fun n => by
  simp only [coeff_derivative]
  exact (hA (n + 1)).mul_const _

theorem congr_eventually {A B : ℝ → ℝ⟦X⟧} {A' : ℝ⟦X⟧} {t : ℝ} (hA : HasSD A A' t)
    (h : ∀ᶠ s in nhds t, B s = A s) : HasSD B A' t := fun n =>
  (hA n).congr_of_eventuallyEq (h.mono fun s hs => by simp [hs])

theorem unique {A : ℝ → ℝ⟦X⟧} {A' A'' : ℝ⟦X⟧} {t : ℝ} (h1 : HasSD A A' t) (h2 : HasSD A A'' t) :
    A' = A'' := by
  ext n
  exact (h1 n).unique (h2 n)

theorem hasDerivAt_const0 {A : ℝ → ℝ⟦X⟧} {A' : ℝ⟦X⟧} {t : ℝ} (hA : HasSD A A' t) :
    HasDerivAt (fun s => constantCoeff (A s)) (constantCoeff A') t := by
  have := hA 0
  simpa only [coeff_zero_eq_constantCoeff_apply] using this

theorem continuousAt {A : ℝ → ℝ⟦X⟧} {A' : ℝ⟦X⟧} {t : ℝ} (hA : HasSD A A' t) (n : ℕ) :
    ContinuousAt (fun s => coeff n (A s)) t := (hA n).continuousAt

end HasSD

namespace Coh

theorem add {S : Set ℝ} {A B : ℝ → ℝ⟦X⟧} (hA : Coh S A) (hB : Coh S B) :
    Coh S (fun s => A s + B s) := fun t ht => by
  simpa [map_add] using (hA t ht).add (hB t ht)

theorem neg {S : Set ℝ} {A : ℝ → ℝ⟦X⟧} (hA : Coh S A) : Coh S (fun s => -A s) := fun t ht => by
  simpa [map_neg] using (hA t ht).neg

theorem smul {S : Set ℝ} {A : ℝ → ℝ⟦X⟧} (c : ℝ) (hA : Coh S A) :
    Coh S (fun s => C c * A s) := fun t ht => by
  have := (hA t ht).smul c
  convert this using 1
  rw [Derivation.leibniz]
  simp

theorem const {S : Set ℝ} (c : ℝ) : Coh S (fun _ => C c) := fun t _ => by
  simpa using HasSD.const (C c) t

theorem var {S : Set ℝ} : Coh S (fun s => C s + X) := fun t _ n => by
  rcases n with _ | _ | n
  · simpa [coeff_derivative] using hasDerivAt_id' t
  · simpa [coeff_derivative] using hasDerivAt_const t (1 : ℝ)
  · simpa [coeff_derivative, coeff_C, coeff_X] using hasDerivAt_const t (0 : ℝ)

theorem mul {S : Set ℝ} {A B : ℝ → ℝ⟦X⟧} (hA : Coh S A) (hB : Coh S B) :
    Coh S (fun s => A s * B s) := fun t ht => by
  have := (hA t ht).mul (hB t ht)
  convert this using 1
  rw [Derivation.leibniz]
  simp only [smul_eq_mul]
  ring

theorem deriv {S : Set ℝ} {A : ℝ → ℝ⟦X⟧} (hA : Coh S A) : Coh S (fun s => d⁄dX (A s)) :=
  fun t ht => (hA t ht).deriv

/-- Coefficient-wise form of coherence. -/
theorem hasDerivAt {S : Set ℝ} {A : ℝ → ℝ⟦X⟧} (hA : Coh S A) {t : ℝ} (ht : t ∈ S) (k : ℕ) :
    HasDerivAt (fun s => coeff k (A s)) (coeff (k + 1) (A t) * (k + 1)) t := by
  simpa [coeff_derivative] using hA t ht k

end Coh

/-! ### Reciprocal -/

theorem hasSD_inv {A : ℝ → ℝ⟦X⟧} {A' : ℝ⟦X⟧} {t : ℝ} (hA : HasSD A A' t)
    (h0 : constantCoeff (A t) ≠ 0) :
    HasSD (fun s => (A s)⁻¹) (-((A t)⁻¹) ^ 2 * A') t := by
  -- constant coefficient stays nonzero near `t`
  have hcont : ContinuousAt (fun s => constantCoeff (A s)) t := by
    exact hA.hasDerivAt_const0.continuousAt
  have hev : ∀ᶠ s in nhds t, constantCoeff (A s) ≠ 0 := hcont.eventually_ne h0
  -- differentiability of all coefficients of the inverse, by strong induction
  have hdiff : ∀ n, DifferentiableAt ℝ (fun s => coeff n (A s)⁻¹) t := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      have hfun : (fun s => coeff n (A s)⁻¹) = fun s =>
          if n = 0 then (constantCoeff (A s))⁻¹
          else -(constantCoeff (A s))⁻¹ *
            ∑ x ∈ antidiagonal n, if x.2 < n then coeff x.1 (A s) * coeff x.2 (A s)⁻¹ else 0 := by
        funext s; exact coeff_inv n (A s)
      rw [hfun]
      by_cases hn : n = 0
      · simp only [hn, ite_true]
        exact hA.hasDerivAt_const0.differentiableAt.inv h0
      · simp only [hn, ite_false]
        have h1 : DifferentiableAt ℝ (fun s => constantCoeff (A s)) t :=
          hA.hasDerivAt_const0.differentiableAt
        refine (h1.inv h0).neg.mul ?_
        refine DifferentiableAt.fun_sum fun x hx => ?_
        by_cases hlt : x.2 < n
        · simp only [hlt, ite_true]
          exact (hA x.1).differentiableAt.mul (ih x.2 hlt)
        · simp only [hlt, ite_false]
          exact differentiableAt_const _
  -- the series of derivatives
  set B' : ℝ⟦X⟧ := PowerSeries.mk fun n => deriv (fun s => coeff n (A s)⁻¹) t with hB'
  have hB : HasSD (fun s => (A s)⁻¹) B' t := fun n => by
    simpa [hB'] using (hdiff n).hasDerivAt
  -- differentiate `A s * (A s)⁻¹ = 1`
  have hprod := hA.mul hB
  have hone : HasSD (fun s => A s * (A s)⁻¹) 0 t := by
    have := HasSD.const (1 : ℝ⟦X⟧) t
    refine this.congr_eventually ?_
    filter_upwards [hev] with s hs
    exact PowerSeries.mul_inv_cancel _ hs
  have hE := hprod.unique hone
  have hI : (A t)⁻¹ * A t = 1 := PowerSeries.inv_mul_cancel _ h0
  have : B' = -((A t)⁻¹) ^ 2 * A' := by
    linear_combination ((A t)⁻¹) * hE - B' * hI
  rw [← this]
  exact hB

/-- Reciprocal of a coherent jet whose constant coefficient does not vanish on `S`. -/
theorem Coh.inv {S : Set ℝ} {A : ℝ → ℝ⟦X⟧} (hA : Coh S A)
    (h0 : ∀ t ∈ S, constantCoeff (A t) ≠ 0) : Coh S (fun s => (A s)⁻¹) := fun t ht => by
  have := hasSD_inv (hA t ht) (h0 t ht)
  show HasSD (fun s => (A s)⁻¹) (d⁄dX ((A t)⁻¹)) t
  rw [derivative_inv']
  exact this


/-! ### Logarithm -/

/-- The jet of `log φ`: coefficient `0` is `log φ₀`, and `d⁄dX (logSeries φ) = φ' φ⁻¹`. -/
noncomputable def logSeries (φ : ℝ⟦X⟧) : ℝ⟦X⟧ :=
  PowerSeries.mk fun n =>
    if n = 0 then Real.log (constantCoeff φ) else coeff (n - 1) (d⁄dX φ * φ⁻¹) / n

theorem coeff_logSeries_zero (φ : ℝ⟦X⟧) : coeff 0 (logSeries φ) = Real.log (constantCoeff φ) := by
  simp [logSeries]

theorem coeff_logSeries_succ (φ : ℝ⟦X⟧) (n : ℕ) :
    coeff (n + 1) (logSeries φ) = coeff n (d⁄dX φ * φ⁻¹) / (n + 1) := by
  simp [logSeries]

theorem derivative_logSeries (φ : ℝ⟦X⟧) : d⁄dX (logSeries φ) = d⁄dX φ * φ⁻¹ := by
  ext n
  rw [coeff_derivative, coeff_logSeries_succ]
  field_simp

theorem Coh.log {S : Set ℝ} {A : ℝ → ℝ⟦X⟧} (hA : Coh S A)
    (h0 : ∀ t ∈ S, constantCoeff (A t) ≠ 0) : Coh S (fun s => logSeries (A s)) := by
  intro t ht n
  have hψ : Coh S (fun s => d⁄dX (A s) * (A s)⁻¹) := (hA.deriv).mul (hA.inv h0)
  have hψt := hψ t ht
  show HasDerivAt (fun s => coeff n (logSeries (A s))) (coeff n (d⁄dX (logSeries (A t)))) t
  rw [derivative_logSeries]
  rcases n with _ | n
  · have h1 := (hA.hasDerivAt ht 0).log (by rw [coeff_zero_eq_constantCoeff_apply]; exact h0 t ht)
    simp only [coeff_logSeries_zero]
    rw [coeff_zero_eq_constantCoeff_apply, map_mul, constantCoeff_inv]
    simp only [coeff_zero_eq_constantCoeff_apply] at h1
    convert h1 using 1
    have hc : constantCoeff (d⁄dX (A t)) = coeff 1 (A t) := by
      rw [← coeff_zero_eq_constantCoeff_apply, coeff_derivative]; simp
    rw [hc]
    simp [div_eq_mul_inv]
  · simp only [coeff_logSeries_succ]
    have h1 := (hψt n).div_const ((n : ℝ) + 1)
    beta_reduce at h1
    rw [coeff_derivative] at h1
    convert h1 using 1
    have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
    field_simp

/-! ### Mean value and Taylor theorems for coherent jets -/

theorem Coh.mvt {lo hi : ℝ} {A : ℝ → ℝ⟦X⟧} (hA : Coh (Set.Icc lo hi) A) {m t : ℝ}
    (hm : m ∈ Set.Icc lo hi) (ht : t ∈ Set.Icc lo hi) (k : ℕ) :
    ∃ ξ ∈ Set.Icc lo hi,
      coeff k (A t) - coeff k (A m) = coeff (k + 1) (A ξ) * (k + 1) * (t - m) := by
  have hd : ∀ s ∈ Set.Icc lo hi,
      HasDerivAt (fun s => coeff k (A s)) (coeff (k + 1) (A s) * (k + 1)) s :=
    fun s hs => hA.hasDerivAt hs k
  have hcont : ContinuousOn (fun s => coeff k (A s)) (Set.Icc lo hi) :=
    fun s hs => (hd s hs).continuousAt.continuousWithinAt
  rcases lt_trichotomy m t with h | h | h
  · obtain ⟨c, hc, hce⟩ := exists_hasDerivAt_eq_slope (fun s => coeff k (A s))
      (fun s => coeff (k + 1) (A s) * (k + 1)) h
      (hcont.mono (Set.Icc_subset_Icc hm.1 ht.2))
      (fun s hs => hd s ⟨hm.1.trans hs.1.le, hs.2.le.trans ht.2⟩)
    refine ⟨c, ⟨hm.1.trans hc.1.le, hc.2.le.trans ht.2⟩, ?_⟩
    rw [hce]; field_simp [(sub_pos.mpr h).ne']
  · subst h; exact ⟨m, hm, by simp⟩
  · obtain ⟨c, hc, hce⟩ := exists_hasDerivAt_eq_slope (fun s => coeff k (A s))
      (fun s => coeff (k + 1) (A s) * (k + 1)) h
      (hcont.mono (Set.Icc_subset_Icc ht.1 hm.2))
      (fun s hs => hd s ⟨ht.1.trans hs.1.le, hs.2.le.trans hm.2⟩)
    refine ⟨c, ⟨ht.1.trans hc.1.le, hc.2.le.trans hm.2⟩, ?_⟩
    have hne : m - t ≠ 0 := (sub_pos.mpr h).ne'
    have : coeff k (A m) - coeff k (A t) = coeff (k + 1) (A c) * (k + 1) * (m - t) := by
      rw [hce]; field_simp
    linarith

/-- Partial Taylor polynomial in the "backward" form `Σ_{k<n} g_k(s) (t-s)^k`. -/
theorem hasDerivAt_taylorSum {A : ℝ → ℝ⟦X⟧} {S : Set ℝ} (hA : Coh S A) {s : ℝ} (hs : s ∈ S)
    (t : ℝ) (n : ℕ) :
    HasDerivAt (fun s => ∑ k ∈ range (n + 1), coeff k (A s) * (t - s) ^ k)
      (coeff (n + 1) (A s) * (n + 1) * (t - s) ^ n) s := by
  induction n with
  | zero =>
    simp only [zero_add, range_one, sum_singleton, pow_zero, mul_one, Nat.cast_zero]
    simpa using hA.hasDerivAt hs 0
  | succ n ih =>
    have h1 : HasDerivAt (fun s => coeff (n + 1) (A s) * (t - s) ^ (n + 1))
        (coeff (n + 2) (A s) * ((n + 1 : ℕ) + 1) * (t - s) ^ (n + 1)
          - coeff (n + 1) (A s) * (n + 1) * (t - s) ^ n) s := by
      have hp : HasDerivAt (fun s => (t - s) ^ (n + 1)) (-((n + 1 : ℕ) * (t - s) ^ n)) s := by
        have := ((hasDerivAt_id s).const_sub t).fun_pow (n + 1)
        simpa using this
      have := (hA.hasDerivAt hs (n + 1)).mul hp
      convert this using 1
      push_cast; ring
    have := ih.add h1
    simp only [sum_range_succ _ (n + 1)]
    convert this using 1
    push_cast; ring

theorem sum_pow_zero_end (a : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ range (n + 1), a k * (0 : ℝ) ^ k = a 0 := by
  rw [sum_range_succ']
  simp

/-- Lagrange form of Taylor's theorem for a coherent jet on an interval. -/
theorem Coh.taylor {lo hi : ℝ} {A : ℝ → ℝ⟦X⟧} (hA : Coh (Set.Icc lo hi) A) {m t : ℝ}
    (hm : m ∈ Set.Icc lo hi) (ht : t ∈ Set.Icc lo hi) (n : ℕ) :
    ∃ ξ ∈ Set.Icc lo hi,
      coeff 0 (A t) = ∑ k ∈ range (n + 1), coeff k (A m) * (t - m) ^ k
        + coeff (n + 1) (A ξ) * (t - m) ^ (n + 1) := by
  set f : ℝ → ℝ := fun s => ∑ k ∈ range (n + 1), coeff k (A s) * (t - s) ^ k with hf
  set f' : ℝ → ℝ := fun s => coeff (n + 1) (A s) * (n + 1) * (t - s) ^ n with hf'
  set g : ℝ → ℝ := fun s => (t - s) ^ (n + 1) with hg
  set g' : ℝ → ℝ := fun s => -(((n : ℝ) + 1) * (t - s) ^ n) with hg'
  have hfd : ∀ s ∈ Set.Icc lo hi, HasDerivAt f (f' s) s := fun s hs =>
    hasDerivAt_taylorSum hA hs t n
  have hgd : ∀ s, HasDerivAt g (g' s) s := fun s => by
    have := ((hasDerivAt_id s).const_sub t).fun_pow (n + 1)
    simpa [hg, hg'] using this
  have hfc : ContinuousOn f (Set.Icc lo hi) := fun s hs => (hfd s hs).continuousAt.continuousWithinAt
  have hgc : ContinuousOn g (Set.Icc lo hi) := fun s _ => (hgd s).continuousAt.continuousWithinAt
  have hft : f t = coeff 0 (A t) := by
    simp only [hf, sub_self]; exact sum_pow_zero_end (fun k => coeff k (A t)) n
  have hgt : g t = 0 := by simp [hg]
  have hfm : f m = ∑ k ∈ range (n + 1), coeff k (A m) * (t - m) ^ k := rfl
  have hgm : g m = (t - m) ^ (n + 1) := rfl
  rcases lt_trichotomy m t with h | h | h
  · obtain ⟨c, hc, hce⟩ := exists_ratio_hasDerivAt_eq_ratio_slope f f' h
      (hfc.mono (Set.Icc_subset_Icc hm.1 ht.2))
      (fun s hs => hfd s ⟨hm.1.trans hs.1.le, hs.2.le.trans ht.2⟩) g g'
      (hgc.mono (Set.Icc_subset_Icc hm.1 ht.2)) (fun s _ => hgd s)
    refine ⟨c, ⟨hm.1.trans hc.1.le, hc.2.le.trans ht.2⟩, ?_⟩
    have hN : ((n : ℝ) + 1) * (t - c) ^ n ≠ 0 := by
      have : 0 < t - c := sub_pos.mpr hc.2
      positivity
    simp only [hf', hg', hft, hgt, hgm] at hce
    have : (t - m) ^ (n + 1) * coeff (n + 1) (A c) = coeff 0 (A t) - f m := by
      apply mul_right_cancel₀ hN
      linear_combination -hce
    linarith
  · subst h
    refine ⟨m, hm, ?_⟩
    simp only [sub_self]
    rw [sum_pow_zero_end (fun k => coeff k (A m)) n]
    simp
  · obtain ⟨c, hc, hce⟩ := exists_ratio_hasDerivAt_eq_ratio_slope f f' h
      (hfc.mono (Set.Icc_subset_Icc ht.1 hm.2))
      (fun s hs => hfd s ⟨ht.1.trans hs.1.le, hs.2.le.trans hm.2⟩) g g'
      (hgc.mono (Set.Icc_subset_Icc ht.1 hm.2)) (fun s _ => hgd s)
    refine ⟨c, ⟨ht.1.trans hc.1.le, hc.2.le.trans hm.2⟩, ?_⟩
    have hN : ((n : ℝ) + 1) * (t - c) ^ n ≠ 0 := by
      have : t - c ≠ 0 := (sub_neg.mpr hc.1).ne
      positivity
    simp only [hf', hg', hft, hgt, hgm] at hce
    have : (t - m) ^ (n + 1) * coeff (n + 1) (A c) = coeff 0 (A t) - f m := by
      apply mul_right_cancel₀ hN
      linear_combination hce
    linarith

end BecknerOnofri.V2.Interval
