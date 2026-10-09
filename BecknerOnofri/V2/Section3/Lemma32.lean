module

public import BecknerOnofri.V2.Section3.CircleBound

@[expose] public section

/-! # Lemma 3.2 (`lem:circle-entropy`) in the manuscript form (G04)

`Ent(r) ≥ ∑_{n ≥ 1} |r̂(n)|² / n` for every `r ∈ 𝒫_ac(𝕋)`.  The repository's circle entropy bound
(`Legacy.D10.CircleEntropy.entropy_bound`) is a statement about the sum over both signs of the frequency, with
weight `1/|k|`; here it is folded to the positive half-line by the conjugate symmetry of Fourier
coefficients of a real density, and extended to infinite entropy (where the right side is `⊤`). -/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology

namespace BecknerOnofri.V2.Section3
open BecknerOnofri.HighDim BecknerOnofri.V2.Vocab

/-- The positive-frequency Fourier weights of a circle density. -/
def circleTerm (r : ProbabilityDensity 1) (n : ℕ) : ℝ :=
  ‖fourierCoeff r.value (fun _ => (n : ℤ) + 1)‖ ^ 2 / ((n : ℝ) + 1)

theorem circleTerm_nonneg (r : ProbabilityDensity 1) (n : ℕ) : 0 ≤ circleTerm r n :=
  div_nonneg (sq_nonneg _) (by positivity)

/-- **Lemma 3.2, finite entropy.** -/
theorem lemma_3_2_finite (r : ProbabilityDensity 1) (hr : r.FiniteEntropy) :
    Summable (circleTerm r) ∧ ∑' n, circleTerm r n ≤ (torusEntropy r.value).toReal := by
  obtain ⟨hsum, hbound⟩ := Legacy.D10.CircleEntropy.entropy_bound (Bridge.density r) hr
  set g : ℤ → ℝ := fun m =>
    |(m : ℝ)|⁻¹ * ‖Legacy.TorusEndpoint.densityFourier (Bridge.density r).value (fun _ => m)‖ ^ 2
    with hg
  have hinj : Function.Injective
      (fun k : Legacy.TorusEndpoint.NonzeroFrequency 1 => k.val 0) := by
    intro a b h
    apply Subtype.ext
    funext i
    have : i = 0 := Subsingleton.elim _ _
    subst this
    exact h
  have hsupp : Function.support g ⊆ Set.range
      (fun k : Legacy.TorusEndpoint.NonzeroFrequency 1 => k.val 0) := by
    intro m hm
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact hm (by simp [hg])
    refine ⟨⟨fun _ => m, fun h => hm0 (by simpa using congrFun h 0)⟩, rfl⟩
  have hcomp : (g ∘ fun k : Legacy.TorusEndpoint.NonzeroFrequency 1 => k.val 0) =
      fun k : Legacy.TorusEndpoint.NonzeroFrequency 1 =>
        Legacy.D10.CircleEntropy.weight k.val *
          ‖Legacy.TorusEndpoint.densityFourier (Bridge.density r).value k.val‖ ^ 2 := by
    funext k
    have hk : (fun _ : Fin 1 => k.val 0) = k.val := by
      funext i
      have : i = 0 := Subsingleton.elim _ _
      subst this; rfl
    simp only [Function.comp, hg, hk, Legacy.D10.CircleEntropy.weight]
  have hsumZ : Summable g := by
    rw [← Function.Injective.summable_iff hinj (fun m hm => ?_)]
    · rw [hcomp]; exact hsum
    · by_contra h
      exact hm (hsupp (Function.mem_support.mpr h))
  have htsumZ : ∑' m, g m =
      ∑' k : Legacy.TorusEndpoint.NonzeroFrequency 1,
        Legacy.D10.CircleEntropy.weight k.val *
          ‖Legacy.TorusEndpoint.densityFourier (Bridge.density r).value k.val‖ ^ 2 := by
    rw [← hcomp]
    exact (Function.Injective.tsum_eq hinj hsupp).symm
  -- evenness of `g`
  have heven : ∀ m : ℤ, g (-m) = g m := by
    intro m
    have h := Legacy.TorusEndpoint.densityFourier_norm_neg (Bridge.density r) (fun _ => m)
    have h' : (-(fun _ : Fin 1 => m)) = fun _ => -m := by funext i; rfl
    rw [h'] at h
    simp only [hg, Int.cast_neg, abs_neg]
    rw [h]
  -- the positive-frequency terms
  have hpos : (fun n : ℕ => g ((n : ℤ) + 1)) = circleTerm r := by
    funext n
    simp only [hg, circleTerm]
    have : |(((n : ℤ) + 1 : ℤ) : ℝ)|⁻¹ = 1 / ((n : ℝ) + 1) := by
      push_cast
      rw [abs_of_nonneg (by positivity)]
      simp
    rw [this]
    change _ = ‖fourierCoeff r.value _‖ ^ 2 / _
    rw [one_div, ← div_eq_inv_mul]
    rfl
  have hsumN : Summable (circleTerm r) := by
    rw [← hpos]
    exact hsumZ.comp_injective (i := fun n : ℕ => (n : ℤ) + 1) (fun a b h => by simpa using h)
  refine ⟨hsumN, ?_⟩
  have hneg : (fun n : ℕ => g (-((n : ℤ) + 1))) = circleTerm r := by
    rw [← hpos]; funext n; exact heven _
  have hsplit := tsum_of_nat_of_neg_add_one
    (hsumZ.comp_injective (i := fun n : ℕ => (n : ℤ)) (fun a b h => by simpa using h))
    (hsumZ.comp_injective (i := fun n : ℕ => -((n : ℤ) + 1)) (fun a b h => by simpa using h))
  have h0 : g 0 = 0 := by simp [hg]
  have hsN : Summable (fun n : ℕ => g (n : ℤ)) :=
    hsumZ.comp_injective (i := fun n : ℕ => (n : ℤ)) (fun a b h => by simpa using h)
  have hnat : ∑' n : ℕ, g (n : ℤ) = ∑' n : ℕ, circleTerm r n := by
    rw [hsN.tsum_eq_zero_add]
    have h1 : ∀ n : ℕ, g (((n + 1 : ℕ) : ℤ)) = circleTerm r n := fun n => by
      rw [← congrFun hpos n]; push_cast; rfl
    simp only [h1, h0, Nat.cast_zero, zero_add]
  have hsplit' : ∑' m, g m = 2 * ∑' n, circleTerm r n := by
    have e1 : ∑' n : ℕ, g (-((n : ℤ) + 1)) = ∑' n, circleTerm r n := by rw [hneg]
    rw [hsplit]
    rw [hnat, e1]; ring
  have hb : ∑' k : Legacy.TorusEndpoint.NonzeroFrequency 1,
        Legacy.D10.CircleEntropy.weight k.val *
          ‖Legacy.TorusEndpoint.densityFourier (Bridge.density r).value k.val‖ ^ 2 ≤
        2 * Legacy.TorusEndpoint.densityEntropy (Bridge.density r).value := hbound
  rw [← htsumZ, hsplit'] at hb
  have h2 := entropy_real_eq_legacy r hr (Bridge.density r) (Filter.EventuallyEq.rfl)
  rw [h2]
  linarith

/-- **Lemma 3.2 (`lem:circle-entropy`).**  For every probability density `r` on the circle,
`∑_{n ≥ 1} |r̂(n)|² / n ≤ Ent r` in `[0, ∞]` (the right side is `⊤` for infinite entropy). -/
theorem lemma_3_2 (r : ProbabilityDensity 1) :
    ∑' n : ℕ, ENNReal.ofReal (circleTerm r n) ≤ torusEntropy r.value := by
  by_cases hr : r.FiniteEntropy
  · obtain ⟨hs, hle⟩ := lemma_3_2_finite r hr
    rw [← ENNReal.ofReal_tsum_of_nonneg (circleTerm_nonneg r) hs]
    rw [← ENNReal.ofReal_toReal ((torusEntropy_density_ne_top_iff r).2 hr)]
    exact ENNReal.ofReal_le_ofReal hle
  · rw [torusEntropy_density_eq_top r hr]
    exact le_top

#print axioms lemma_3_2_finite
#print axioms lemma_3_2

end BecknerOnofri.V2.Section3
