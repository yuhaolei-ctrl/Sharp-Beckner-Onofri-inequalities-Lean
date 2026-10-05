module

public import Legacy.TorusEndpoint.FiniteAtomEuler
public import Legacy.TorusEndpoint.GlobalCoefficientCriterion

@[expose] public section

/-! The circle entropy inequality, proved from the actual exponential
coefficients. The finite coefficient estimate is proved here by the Euler
recurrence; it is not supplied as an analytic hypothesis. -/

open scoped BigOperators
open Legacy.TorusEndpoint Legacy.TorusEndpoint.FiniteCone
open Legacy.TorusEndpoint.FiniteAtomCoefficients Legacy.TorusEndpoint.FiniteAtomCriterion

namespace Legacy.D10.CircleEntropy

noncomputable def weight (k : Frequency 1) : ℝ := |(k 0 : ℝ)|⁻¹

theorem positive_coordinate (k : Frequency 1) (hk : LexPositive k) : 0 < k 0 := by
  obtain ⟨j, hj, _⟩ := hk
  have hj0 : j = 0 := Subsingleton.elim _ _
  simpa [hj0] using hj

theorem coordinate_injective : Function.Injective (fun k : Frequency 1 => k 0) := by
  intro k l h
  funext j
  have hj : j = 0 := Subsingleton.elim _ _
  simpa [hj] using h

theorem generated_coordinate_nonneg (atoms : List (Frequency 1))
    (hpos : ∀ k ∈ atoms, LexPositive k) {k : Frequency 1}
    (hk : Generated atoms k) : 0 ≤ k 0 := by
  obtain ⟨xs, hxs, rfl⟩ := hk
  have he := Legacy.TorusEndpoint.D3AxisCoefficient.sumVec_coordinate xs 0
  rw [he]
  apply List.sum_nonneg
  intro z hz
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hz
  exact (positive_coordinate x (hpos x (hxs x hx))).le

theorem coefficient_negative (atoms : List (Frequency 1)) (w k : Frequency 1)
    (hpos : ∀ x ∈ atoms, LexPositive x)
    (hw : ∀ x ∈ atoms, 0 < eval w x) (hk : k 0 < 0) :
    coefficient atoms w weight 1 k = 0 := by
  apply coefficient_zero_of_not_generated atoms w weight 1 k hw
  intro hg
  exact (not_le_of_gt hk) (generated_coordinate_nonneg atoms hpos hg)

theorem atom_factor (k : Frequency 1) (hk : LexPositive k) :
    (k 0 : ℝ) * weight k = 1 := by
  have hp : (0 : ℝ) < k 0 := Int.cast_pos.mpr (positive_coordinate k hk)
  simp [weight, abs_of_pos hp, ne_of_gt hp]

theorem coefficient_cap (atoms : List (Frequency 1)) (w : Frequency 1)
    (hpos : ∀ x ∈ atoms, LexPositive x)
    (hw : ∀ x ∈ atoms, 0 < eval w x)
    (n : ℕ) : ∀ k : Frequency 1, k 0 = n → coefficient atoms w weight 1 k ≤ 1 := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro k hk
    by_cases hn : n = 0
    · have hk0 : k = zero := coordinate_injective (by simpa [hn, zero] using hk)
      rw [hk0, coefficient_zero atoms w weight 1 hw]
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    let active := atoms.toFinset.filter (fun x => x 0 ≤ (n : ℤ))
    have he := Legacy.TorusEndpoint.FiniteAtomEuler.coefficient_euler_coordinate
      atoms w k weight 0 hw
    have hsplit : (∑ x ∈ atoms.toFinset,
        (x 0 : ℝ) * weight x * coefficient atoms w weight 1 (remainder k x)) =
        ∑ x ∈ active, coefficient atoms w weight 1 (remainder k x) := by
      rw [show active = atoms.toFinset.filter (fun x => x 0 ≤ (n : ℤ)) from rfl,
        Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro x hx
      have hxp := hpos x (List.mem_toFinset.mp hx)
      rw [atom_factor x hxp, one_mul]
      split_ifs with hxn
      · rfl
      · exact coefficient_negative atoms w _ hpos hw (by dsimp [remainder]; omega)
    rw [hsplit] at he
    have hsum : (∑ x ∈ active, coefficient atoms w weight 1 (remainder k x)) ≤
        (active.card : ℝ) := by
      calc
        _ ≤ ∑ _x ∈ active, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro x hx
          obtain ⟨hxa, hxn⟩ := Finset.mem_filter.mp hx
          have hxp := positive_coordinate x (hpos x (List.mem_toFinset.mp hxa))
          have hm : 0 ≤ k 0 - x 0 := by omega
          apply ih ((k 0 - x 0).toNat) (by omega) (remainder k x)
          dsimp [remainder]
          exact (Int.toNat_of_nonneg hm).symm
        _ = _ := by simp
    have hcard : active.card ≤ n := by
      have hinj : Set.InjOn (fun x : Frequency 1 => (x 0 - 1).toNat) (↑active) := by
        intro x hx y hy heq
        have hxp := positive_coordinate x (hpos x
          (List.mem_toFinset.mp (Finset.mem_filter.mp hx).1))
        have hyp := positive_coordinate y (hpos y
          (List.mem_toFinset.mp (Finset.mem_filter.mp hy).1))
        apply coordinate_injective
        change x 0 = y 0
        change (x 0 - 1).toNat = (y 0 - 1).toNat at heq
        omega
      have hmap : Set.MapsTo (fun x : Frequency 1 => (x 0 - 1).toNat)
          (↑active) (↑(Finset.range n)) := by
        intro x hx
        obtain ⟨hxa, hxn⟩ := Finset.mem_filter.mp hx
        have hxp := positive_coordinate x (hpos x (List.mem_toFinset.mp hxa))
        apply Finset.mem_range.mpr
        change (x 0 - 1).toNat < n
        omega
      simpa using Finset.card_le_card_of_injOn _ hmap hinj
    have hc : (active.card : ℝ) ≤ n := Nat.cast_le.mpr hcard
    have hnr : (0 : ℝ) < n := Nat.cast_pos.mpr hnpos
    have hkn : (k 0 : ℝ) = (n : ℝ) := by exact_mod_cast hk
    rw [hkn] at he
    nlinarith

theorem global_coefficient_cap : GlobalFiniteAtomCap weight := by
  intro atoms hpos w hw k _ hg
  have hk := generated_coordinate_nonneg atoms hpos hg
  exact coefficient_cap atoms w hpos hw (k 0).toNat k (Int.toNat_of_nonneg hk).symm

/-- Circle entropy controls the complete nonzero Fourier sum with weight
`1 / |k|`. Equivalently the positive-frequency sum is bounded by entropy. -/
theorem entropy_bound (rho : ProbabilityDensity 1) (hrho : rho.FiniteEntropy) :
    Summable (fun k : NonzeroFrequency 1 =>
      weight k.val * ‖densityFourier rho.value k.val‖ ^ 2) ∧
    (∑' k : NonzeroFrequency 1,
      weight k.val * ‖densityFourier rho.value k.val‖ ^ 2) ≤
      2 * densityEntropy rho.value := by
  apply full_spectral_entropy_of_global_coefficient_cap rho hrho weight
  · intro k hk
    have hkn : k 0 ≠ 0 := by
      intro he
      exact hk (coordinate_injective he)
    unfold weight
    exact inv_pos.mpr (abs_pos.mpr (Int.cast_ne_zero.mpr hkn))
  · intro k _
    simp [weight]
  · exact global_coefficient_cap

end Legacy.D10.CircleEntropy
