module

public import Legacy.TorusEndpoint.SpectralEntropy
public import Legacy.TorusEndpoint.FiniteConeTotal
public import Mathlib.Topology.Algebra.InfiniteSum.Constructions

@[expose] public section

/-!
# Full-spectrum versus half-cone reindexing

The actual finite-lattice sign trichotomy supplies the reindexing.
The spectral weight a is always a denominator weight. The last entropy
bound retains the half-cone exponential-integral hypothesis explicitly.
No physical Green-kernel assertion is made.
-/

open MeasureTheory
open scoped BigOperators ComplexConjugate

namespace Legacy.TorusEndpoint

abbrev NonzeroFrequency (d : ℕ) := {k : Frequency d // k ≠ 0}

theorem positive_frequency_ne_zero {d : ℕ} (k : PositiveFrequency d) :
    k.val ≠ (0 : Frequency d) := by
  intro h
  apply FiniteCone.positive_ne_zero k.property
  exact h

def positivePairToNonzero {d : ℕ} :
    PositiveFrequency d ⊕ PositiveFrequency d → NonzeroFrequency d
  | Sum.inl k => ⟨k.val, positive_frequency_ne_zero k⟩
  | Sum.inr k => ⟨-k.val, neg_ne_zero.mpr (positive_frequency_ne_zero k)⟩

theorem positivePairToNonzero_injective {d : ℕ} :
    Function.Injective (positivePairToNonzero (d := d)) := by
  intro p q h
  have hv := congrArg Subtype.val h
  cases p with
  | inl i =>
    cases q with
    | inl j =>
      apply congrArg Sum.inl
      apply Subtype.ext
      exact hv
    | inr j =>
      have hn : ¬ FiniteCone.LexPositive (-j.val) :=
        FiniteCone.positive_not_neg j.property
      apply False.elim
      apply hn
      change i.val = -j.val at hv
      rw [← hv]
      exact i.property
  | inr i =>
    cases q with
    | inl j =>
      have hn : ¬ FiniteCone.LexPositive (-i.val) :=
        FiniteCone.positive_not_neg i.property
      apply False.elim
      apply hn
      change -i.val = j.val at hv
      rw [hv]
      exact j.property
    | inr j =>
      apply congrArg Sum.inr
      apply Subtype.ext
      exact neg_injective hv

theorem positivePairToNonzero_surjective {d : ℕ}
    (h_total : ∀ k : Frequency d, k ≠ 0 →
      FiniteCone.LexPositive k ∨ FiniteCone.LexPositive (-k)) :
    Function.Surjective (positivePairToNonzero (d := d)) := by
  intro k
  rcases h_total k.val k.property with hp | hn
  · exact ⟨Sum.inl ⟨k.val, hp⟩, rfl⟩
  · refine ⟨Sum.inr ⟨-k.val, hn⟩, ?_⟩
    apply Subtype.ext
    exact neg_neg k.val

noncomputable def positivePairEquivNonzero {d : ℕ}
    (h_total : ∀ k : Frequency d, k ≠ 0 →
      FiniteCone.LexPositive k ∨ FiniteCone.LexPositive (-k)) :
    (PositiveFrequency d ⊕ PositiveFrequency d) ≃ NonzeroFrequency d :=
  Equiv.ofBijective positivePairToNonzero
    ⟨positivePairToNonzero_injective, positivePairToNonzero_surjective h_total⟩

theorem full_spectral_reindex {d : ℕ}
    (h_total : ∀ k : Frequency d, k ≠ 0 →
      FiniteCone.LexPositive k ∨ FiniteCone.LexPositive (-k))
    (rho : ProbabilityDensity d) (a : Frequency d → ℝ)
    (h_even : ∀ k : Frequency d, k ≠ 0 → a (-k) = a k)
    (h_half : Summable (fun k : PositiveFrequency d =>
      ‖densityFourier rho.value k.val‖^2 / a k.val)) :
    Summable (fun k : NonzeroFrequency d =>
      ‖densityFourier rho.value k.val‖^2 / a k.val) ∧
    (∑' k : NonzeroFrequency d, ‖densityFourier rho.value k.val‖^2 / a k.val) =
      2 * (∑' k : PositiveFrequency d, ‖densityFourier rho.value k.val‖^2 / a k.val) := by
  let e := positivePairEquivNonzero h_total
  let F : NonzeroFrequency d → ℝ := fun k =>
    ‖densityFourier rho.value k.val‖^2 / a k.val
  let G : PositiveFrequency d → ℝ := fun k =>
    ‖densityFourier rho.value k.val‖^2 / a k.val
  have h_pointwise : ∀ p : PositiveFrequency d ⊕ PositiveFrequency d,
      F (e p) = Sum.elim G G p := by
    intro p
    cases p with
    | inl k => rfl
    | inr k =>
      change ‖densityFourier rho.value (-k.val)‖^2 / a (-k.val) =
        ‖densityFourier rho.value k.val‖^2 / a k.val
      rw [densityFourier_norm_neg, h_even k.val (positive_frequency_ne_zero k)]
  have h_sum : Summable (Sum.elim G G) :=
    Summable.sum (Sum.elim G G) h_half h_half
  have h_reindexed : Summable (F ∘ e) :=
    h_sum.congr (fun p => (h_pointwise p).symm)
  refine ⟨e.summable_iff.mp h_reindexed, ?_⟩
  change (∑' k, F k) = 2 * ∑' k, G k
  calc
    (∑' k, F k) = ∑' p, F (e p) := (e.tsum_eq F).symm
    _ = ∑' p, Sum.elim G G p := tsum_congr h_pointwise
    _ = (∑' k, G k) + ∑' k, G k :=
      Summable.tsum_sum (f := Sum.elim G G) h_half h_half
    _ = 2 * ∑' k, G k := by ring

/-- For an even denominator weight, a summable half-spectrum gives a
summable nonzero full spectrum and its exact factor of two. -/
theorem full_spectral_summable_and_eq_twice {d : ℕ}
    (rho : ProbabilityDensity d) (a : Frequency d → ℝ)
    (h_even : ∀ k : Frequency d, k ≠ 0 → a (-k) = a k)
    (h_half : Summable (fun k : PositiveFrequency d =>
      ‖densityFourier rho.value k.val‖^2 / a k.val)) :
    Summable (fun k : NonzeroFrequency d =>
      ‖densityFourier rho.value k.val‖^2 / a k.val) ∧
    (∑' k : NonzeroFrequency d, ‖densityFourier rho.value k.val‖^2 / a k.val) =
      2 * (∑' k : PositiveFrequency d, ‖densityFourier rho.value k.val‖^2 / a k.val) := by
  exact full_spectral_reindex
    (fun k hk => FiniteCone.positive_or_negative_of_ne_zero hk) rho a h_even h_half

/-- All finite half-cone exponential estimates imply the actual full
spectral entropy bound. No prior spectral summability is assumed here. -/
theorem full_spectral_summable_and_entropy_bound {d : ℕ}
    (rho : ProbabilityDensity d) (h_entropy : rho.FiniteEntropy)
    (a : Frequency d → ℝ)
    (h_a : ∀ k : Frequency d, k ≠ 0 → 0 < a k)
    (h_even : ∀ k : Frequency d, k ≠ 0 → a (-k) = a k)
    (h_exp : ∀ s : Finset (Frequency d),
      (∀ k ∈ s, FiniteCone.LexPositive k) → ∀ c : Frequency d → ℂ,
      Real.log (∫ x, Real.exp (2 * (fourierPolynomial s c x).re) ∂torusMeasure d) ≤
        ∑ k ∈ s, a k * ‖c k‖^2) :
    Summable (fun k : NonzeroFrequency d =>
      ‖densityFourier rho.value k.val‖^2 / a k.val) ∧
    (∑' k : NonzeroFrequency d, ‖densityFourier rho.value k.val‖^2 / a k.val) ≤
      2 * densityEntropy rho.value := by
  have haP : ∀ k, FiniteCone.LexPositive k → 0 < a k := by
    intro k hk
    exact h_a k (FiniteCone.positive_ne_zero hk)
  obtain ⟨h_half, h_bound⟩ := positive_spectral_summable_and_tsum_le
    rho h_entropy a haP h_exp
  obtain ⟨h_full, h_twice⟩ := full_spectral_summable_and_eq_twice rho a h_even h_half
  refine ⟨h_full, ?_⟩
  rw [h_twice]
  exact mul_le_mul_of_nonneg_left h_bound (by norm_num)

end Legacy.TorusEndpoint
