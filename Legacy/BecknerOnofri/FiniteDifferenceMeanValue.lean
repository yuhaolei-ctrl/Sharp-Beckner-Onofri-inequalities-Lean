import Legacy.BecknerOnofri.FiniteDifferenceCalculus
import Legacy.BecknerOnofri.FiniteDifferenceRecurrence
import Mathlib.Analysis.SpecificLimits.Basic

/-! A rectangular finite difference is a genuine mixed derivative at an intermediate point. -/
noncomputable section
open Finset Set Filter
open scoped BigOperators Topology
namespace Legacy.BecknerOnofri.FiniteDifferences

/-- Iterating the real mean value theorem gives a precise mixed-derivative witness. -/
theorem rectangularDifference_meanValue {d : ℕ} (is : List (Fin d))
    {D : List (Fin d) → Space d → ℝ} (hD : IsCoordinateJet D)
    {h : ℝ} (hh : 0 < h) (x : Space d) (hx : Fits (directionIndex is) h x) :
    ∃ y : Space d,
      (∀ k, x k ≤ y k ∧ y k ≤ x k + (directionIndex is k : ℝ)*h) ∧
      rectangularDifference (directionIndex is) h (D []) x = h^is.length * D is y := by
  induction is generalizing D x with
  | nil =>
    refine ⟨x, ?_, ?_⟩
    · intro k; simp
    · simp
  | cons i is ih =>
    obtain ⟨t, ht, htEq⟩ := coordinate_mvt hD (directionIndex is) i hh x hx
    obtain ⟨y, hy, hyEq⟩ := ih (hD.prepend i) (Function.update x i t)
      (hx.update i (mem_Icc_of_Ioo ht))
    refine ⟨y, ?_, ?_⟩
    · intro k
      have hk := hy k
      by_cases hki : k = i
      · subst k
        simp only [Function.update_self] at hk
        simp only [directionIndex_cons, Finsupp.add_apply, Finsupp.single_eq_same,
          Nat.cast_add, Nat.cast_one]
        constructor <;> linarith [ht.1, ht.2, hk.1, hk.2]
      · simpa [Function.update_of_ne hki, Finsupp.single_eq_of_ne hki] using hk
    · rw [directionIndex_cons, rectangularDifference_succ]
      have he : rectangularDifference (directionIndex is) h (D []) (translate x i h) -
          rectangularDifference (directionIndex is) h (D []) x =
          h * rectangularDifference (directionIndex is) h (D [i]) (Function.update x i t) := by
        have hh0 := hh.ne'
        exact (eq_div_iff hh0).mp htEq |>.symm.trans (mul_comm _ _)
      rw [he, hyEq]
      simp only [List.length_cons, pow_succ]
      ring

theorem rectangularDifference_meanValue_multiindex {d : ℕ} (a : Index d)
    {D : List (Fin d) → Space d → ℝ} (hD : IsCoordinateJet D)
    {h : ℝ} (hh : 0 < h) (x : Space d) (hx : Fits a h x) :
    ∃ y : Space d, (∀ k, x k ≤ y k ∧ y k ≤ x k + (a k : ℝ)*h) ∧
      rectangularDifference a h (D []) x = h^degree a * D (directions a) y := by
  simpa only [directionIndex_directions, length_directions] using
    rectangularDifference_meanValue (directions a) hD hh x (by simpa using hx)

theorem rectangularDifference_nonneg_jet {d : ℕ} (a : Index d)
    {D : List (Fin d) → Space d → ℝ} (hD : IsCoordinateJet D)
    (hpos : ∀ is x, x ∈ closedCube d → 0 ≤ D is x)
    {h : ℝ} (hh : 0 < h) (x : Space d) (hx : Fits a h x) :
    0 ≤ rectangularDifference a h (D []) x := by
  obtain ⟨y, hy, he⟩ := rectangularDifference_meanValue_multiindex a hD hh x hx
  rw [he]
  apply mul_nonneg (pow_nonneg hh.le _)
  apply hpos
  constructor <;> intro k
  · exact (hx.1 k).trans (hy k).1
  · exact (hy k).2.trans (hx.2 k)

/-- The normalized finite difference converges to the actual iterated coordinate derivative. -/
theorem scaledDifference_tendsto_jet {d : ℕ} (a : Index d)
    {D : List (Fin d) → Space d → ℝ} (hD : IsCoordinateJet D)
    {ι : Type*} {l : Filter ι} {h : ι → ℝ}
    (hl : Tendsto h l (𝓝 0)) (hgood : ∀ᶠ z in l, 0 < h z ∧ Fits a (h z) 0) :
    Tendsto (fun z => rectangularDifference a (h z) (D []) 0 / (h z)^degree a)
      l (𝓝 (D (directions a) 0)) := by
  have hex : ∀ z, ∃ y : Space d, (0 < h z ∧ Fits a (h z) 0) →
      (∀ k, 0 ≤ y k ∧ y k ≤ (a k : ℝ)*h z) ∧
      rectangularDifference a (h z) (D []) 0 = (h z)^degree a * D (directions a) y := by
    intro z
    by_cases hz : 0 < h z ∧ Fits a (h z) 0
    · obtain ⟨y, hy, he⟩ := rectangularDifference_meanValue_multiindex a hD hz.1 0 hz.2
      exact ⟨y, fun _ => ⟨by simpa using hy, he⟩⟩
    · exact ⟨0, fun hh => (hz hh).elim⟩
  choose y hy using hex
  have hybounds : ∀ᶠ z in l, ∀ k, 0 ≤ y z k ∧ y z k ≤ (a k : ℝ)*h z := by
    filter_upwards [hgood] with z hz
    exact (hy z hz).1
  have hyl : Tendsto y l (𝓝 (0 : Space d)) := by
    apply tendsto_pi_nhds.mpr
    intro k
    apply squeeze_zero' (hybounds.mono fun z hz => (hz k).1)
      (hybounds.mono fun z hz => (hz k).2)
    simpa using hl.const_mul (a k : ℝ)
  have hycube : ∀ᶠ z in l, y z ∈ closedCube d := by
    filter_upwards [hgood, hybounds] with z hz hb
    constructor <;> intro k
    · exact (hb k).1
    · have hk := hz.2.2 k
      simpa using (hb k).2.trans (by simpa using hk)
  have hlim := (hD.continuous (directions a) 0 (by simp [closedCube])).tendsto.comp
    (tendsto_nhdsWithin_iff.mpr ⟨hyl, hycube⟩)
  apply hlim.congr'
  filter_upwards [hgood] with z hz
  rw [(hy z hz).2]
  exact (mul_div_cancel_left₀ _ (pow_ne_zero _ hz.1.ne')).symm

theorem index_le_degree {d : ℕ} (a : Index d) (i : Fin d) : a i ≤ degree a :=
  Finset.single_le_sum (fun k _ => Nat.zero_le (a k)) (Finset.mem_univ i)

theorem fits_zero_inverse {d : ℕ} (a : Index d) {m : ℕ} (hm : 0 < m)
    (ha : ∀ i, a i ≤ m) : Fits a (1 / (m : ℝ)) 0 := by
  constructor
  · intro i; simp
  · intro i
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    have ha' : (a i : ℝ) ≤ m := by exact_mod_cast ha i
    simpa only [Pi.zero_apply, zero_add, mul_one_div] using (div_le_one hm').mpr ha'

theorem eventually_fits_zero_inverse {d : ℕ} (a : Index d) :
    ∀ᶠ m : ℕ in atTop, 0 < 1/(m : ℝ) ∧ Fits a (1/(m : ℝ)) 0 := by
  filter_upwards [eventually_ge_atTop (degree a + 1)] with m hm
  have hm0 : 0 < m := by omega
  constructor
  · positivity
  · exact fits_zero_inverse a hm0 (fun i => (index_le_degree a i).trans (by omega))

theorem scaledDifference_tendsto_nat_jet {d : ℕ} (a : Index d)
    {D : List (Fin d) → Space d → ℝ} (hD : IsCoordinateJet D) :
    Tendsto (fun m : ℕ => rectangularDifference a (1/(m : ℝ)) (D []) 0 /
      (1/(m : ℝ))^degree a) atTop (𝓝 (D (directions a) 0)) :=
  scaledDifference_tendsto_jet a hD tendsto_one_div_atTop_nhds_zero_nat
    (eventually_fits_zero_inverse a)

#print axioms rectangularDifference_meanValue_multiindex
#print axioms rectangularDifference_nonneg_jet
#print axioms scaledDifference_tendsto_nat_jet

end Legacy.BecknerOnofri.FiniteDifferences
