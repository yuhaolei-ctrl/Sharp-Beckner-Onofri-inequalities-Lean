module

public import BecknerOnofri.V2.Interval.Certificate

@[expose] public section

/-!
# The scalar certificate of Lemma `d12-spin-lem:scalar`

Conditional on (i) the successful run of `Row.checkCell` on all cells (`hcheck`), (ii) the vanishing
at `0` of the jets of the first row's `f` and `𝒱` (`hzf`, `hzv`, from the origin analysis) and
(iii) the identification of the programs' registers with the manuscript's functions (`hf`, `hV`,
`he`), the three scalar inequalities hold on `[0, 99/100]`.
-/

namespace BecknerOnofri.V2.Interval

open PowerSeries Finset

/-- The raw program (first row) with its output registers. -/
def P1 : Prog × Outs := familyProg true
/-- The normalised program (second and third row) with its output registers. -/
def P2 : Prog × Outs := familyProg false

theorem row1_valid : row1.Valid := ⟨by decide, by decide, by decide⟩
theorem row2_valid : row2.Valid := ⟨by decide, by decide, by decide⟩
theorem row3_valid : row3.Valid := ⟨by decide, by decide, by decide⟩

theorem row1_small : row1.small = true := rfl
theorem row2_small : row2.small = false := rfl
theorem row3_small : row3.small = false := rfl

/-- Soundness of the first row (`[0, 1/8]`). -/
theorem row1_sound (hcheck : ∀ k < row1.count, row1.checkCell k = true)
    (hzf : ∀ n < 4, coeff n (chain P1.1 P1.2.f 0) = 0)
    (hzv : ∀ n < 4, coeff n (chain P1.1 P1.2.v 0) = 0) :
    ∀ t : ℝ, 0 ≤ t → t ≤ 1 / 8 →
      (t ^ 4 / 2 ≤ regVal P1.1 P1.2.f t ∧ (0 < t → t ^ 4 / 10 < regVal P1.1 P1.2.f t)) ∧
      (regVal P1.1 P1.2.v t ≤ (1 / 50 - 3 / 400) * t ^ 4 ∧
        (0 < t → regVal P1.1 P1.2.v t < t ^ 4 / 50)) ∧
      ∀ i ∈ P1.2.e, 6 / 25 < regVal P1.1 i t := by
  have ha : ((row1.aN : ℤ) : ℝ) / (row1.aD : ℝ) = 0 := by norm_num [row1]
  have hb : ((row1.bN : ℤ) : ℝ) / (row1.bD : ℝ) = 1 / 8 := by norm_num [row1]
  have hm0 : (1 : ℝ) / 10 + (row1.m0.1 : ℝ) / row1.m0.2 = 1 / 2 := by norm_num [row1]
  have hm1 : (1 : ℝ) / 50 - (row1.m1.1 : ℝ) / row1.m1.2 = 1 / 50 - 3 / 400 := by norm_num [row1]
  have hm2 : (row1.m2.1 : ℝ) / row1.m2.2 = 6 / 25 := by norm_num [row1]
  have key := Row.small_taylor row1_valid (by decide) row1_small (by decide) (by decide)
    (by decide) hcheck (by rw [ha]; exact hzf) (by rw [ha]; exact hzv)
  rw [ha, hb, hm0, hm1, hm2] at key
  intro t h1 h2
  obtain ⟨⟨f1, f2⟩, ⟨v1, v2⟩, he⟩ := key t h1 h2
  simp only [sub_zero] at f1 f2 v1 v2
  have f1' : 1 / 2 * t ^ 4 ≤ regVal P1.1 P1.2.f t := f1
  have f2' : 0 < t → 1 / 2 * t ^ 4 < regVal P1.1 P1.2.f t := f2
  have v1' : regVal P1.1 P1.2.v t ≤ (1 / 50 - 3 / 400) * t ^ 4 := v1
  have v2' : 0 < t → regVal P1.1 P1.2.v t < (1 / 50 - 3 / 400) * t ^ 4 := v2
  refine ⟨⟨by linarith [f1'], fun ht => ?_⟩, ⟨v1', fun ht => ?_⟩, he⟩
  · have := f2' ht
    have h4 : 0 < t ^ 4 := by positivity
    linarith
  · have := v2' ht
    have h4 : 0 < t ^ 4 := by positivity
    linarith

/-- Soundness of the second and third rows (`[1/8, 99/100]`). -/
theorem row23_sound (hc2 : ∀ k < row2.count, row2.checkCell k = true)
    (hc3 : ∀ k < row3.count, row3.checkCell k = true) :
    ∀ t : ℝ, 1 / 8 ≤ t → t ≤ 99 / 100 →
      1 / 100 < regVal P2.1 P2.2.f t ∧ 7 / 1000 < regVal P2.1 P2.2.v t ∧
        ∀ i ∈ P2.2.e, 7 / 250 < regVal P2.1 i t := by
  intro t h1 h2
  rcases le_total t (7 / 8) with h | h
  · have ha : ((row2.aN : ℤ) : ℝ) / (row2.aD : ℝ) = 1 / 8 := by norm_num [row2]
    have hb : ((row2.bN : ℤ) : ℝ) / (row2.bD : ℝ) = 7 / 8 := by norm_num [row2]
    have hm0 : (row2.m0.1 : ℝ) / row2.m0.2 = 1 / 100 := by norm_num [row2]
    have hm1 : (row2.m1.1 : ℝ) / row2.m1.2 = 7 / 1000 := by norm_num [row2]
    have hm2 : (row2.m2.1 : ℝ) / row2.m2.2 = 9 / 100 := by norm_num [row2]
    have key := Row.big_pointwise row2_valid (by decide) row2_small (by decide) (by decide)
      (by decide) hc2 (t := t) ⟨by rw [ha]; exact h1, by rw [hb]; exact h⟩
    rw [hm0, hm1, hm2] at key
    obtain ⟨k0, k1, k2⟩ := key
    exact ⟨k0, k1, fun i hi => lt_trans (by norm_num : (7 / 250 : ℝ) < 9 / 100) (k2 i hi)⟩
  · have ha : ((row3.aN : ℤ) : ℝ) / (row3.aD : ℝ) = 7 / 8 := by norm_num [row3]
    have hb : ((row3.bN : ℤ) : ℝ) / (row3.bD : ℝ) = 99 / 100 := by norm_num [row3]
    have hm0 : (row3.m0.1 : ℝ) / row3.m0.2 = 1 / 50 := by norm_num [row3]
    have hm1 : (row3.m1.1 : ℝ) / row3.m1.2 = 1 / 100 := by norm_num [row3]
    have hm2 : (row3.m2.1 : ℝ) / row3.m2.2 = 7 / 250 := by norm_num [row3]
    have key := Row.big_pointwise row3_valid (by decide) row3_small (by decide) (by decide)
      (by decide) hc3 (t := t) ⟨by rw [ha]; exact h, by rw [hb]; exact h2⟩
    rw [hm0, hm1, hm2] at key
    obtain ⟨k0, k1, k2⟩ := key
    exact ⟨lt_trans (by norm_num : (1 / 100 : ℝ) < 1 / 50) k0,
      lt_trans (by norm_num : (7 / 1000 : ℝ) < 1 / 100) k1, k2⟩

theorem P1_e_length : P1.2.e.length = 13 := by decide +kernel
theorem P2_e_length : P2.2.e.length = 13 := by decide +kernel

theorem getD_mem_of_lt {l : List ℕ} {j : ℕ} (h : j < l.length) : l.getD j 0 ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  exact List.getElem_mem h

theorem mem_iff_getD {l : List ℕ} {i : ℕ} (h : i ∈ l) : ∃ j < l.length, l.getD j 0 = i := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem h
  refine ⟨j, hj, ?_⟩
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  rfl

/-- **Conditional scalar certificate** (Lemma `d12-spin-lem:scalar`, eq. `d12-spin-eq:three`).

Hypotheses (remaining obligations, see the report):
* `hc1 hc2 hc3`: `Row.checkCell` succeeds on all `32 + 64 + 64` cells (a finite computation);
* `hzf hzv`: the jets of the programs' `f` and `𝒱` registers at `0` vanish up to order three;
* `hf1 hV1 he1 hf2 hV2 he2`: the program registers equal the manuscript's functions
  (first row: `f`, `𝒱`, `e_j + 1/4`; other rows: `f/t⁴ - 1/10`, `1/50 - 𝒱/t⁴`, `e_j + 1/4`). -/
theorem scalar_certificate (f V : ℝ → ℝ) (e : ℕ → ℝ → ℝ)
    (hc1 : ∀ k < row1.count, row1.checkCell k = true)
    (hc2 : ∀ k < row2.count, row2.checkCell k = true)
    (hc3 : ∀ k < row3.count, row3.checkCell k = true)
    (hzf : ∀ n < 4, coeff n (chain P1.1 P1.2.f 0) = 0)
    (hzv : ∀ n < 4, coeff n (chain P1.1 P1.2.v 0) = 0)
    (hf1 : ∀ t, 0 ≤ t → t ≤ 1 / 8 → regVal P1.1 P1.2.f t = f t)
    (hV1 : ∀ t, 0 ≤ t → t ≤ 1 / 8 → regVal P1.1 P1.2.v t = V t)
    (he1 : ∀ t, 0 ≤ t → t ≤ 1 / 8 → ∀ j < 13, regVal P1.1 (P1.2.e.getD j 0) t = e j t + 1 / 4)
    (hf2 : ∀ t, 1 / 8 ≤ t → t ≤ 99 / 100 → regVal P2.1 P2.2.f t = f t / t ^ 4 - 1 / 10)
    (hV2 : ∀ t, 1 / 8 ≤ t → t ≤ 99 / 100 → regVal P2.1 P2.2.v t = 1 / 50 - V t / t ^ 4)
    (he2 : ∀ t, 1 / 8 ≤ t → t ≤ 99 / 100 → ∀ j < 13,
      regVal P2.1 (P2.2.e.getD j 0) t = e j t + 1 / 4) :
    ∀ t : ℝ, 0 ≤ t → t ≤ 99 / 100 →
      (t ^ 4 / 10 ≤ f t ∧ (0 < t → t ^ 4 / 10 < f t)) ∧
      (V t ≤ t ^ 4 / 50 ∧ (0 < t → V t < t ^ 4 / 50)) ∧ ∀ j < 13, -(1 / 4) ≤ e j t := by
  intro t h0 h99
  rcases le_total t (1 / 8) with h | h
  · obtain ⟨⟨f1, f2⟩, ⟨v1, v2⟩, he⟩ := row1_sound hc1 hzf hzv t h0 h
    have h4 : 0 ≤ t ^ 4 := by positivity
    rw [hf1 t h0 h] at f1 f2
    rw [hV1 t h0 h] at v1 v2
    refine ⟨⟨by linarith, f2⟩, ⟨by linarith, v2⟩, fun j hj => ?_⟩
    have := he _ (getD_mem_of_lt (by rw [P1_e_length]; exact hj))
    rw [he1 t h0 h j hj] at this
    linarith
  · obtain ⟨k0, k1, k2⟩ := row23_sound hc2 hc3 t h h99
    have ht : 0 < t := lt_of_lt_of_le (by norm_num) h
    have h4 : 0 < t ^ 4 := by positivity
    rw [hf2 t h h99] at k0
    rw [hV2 t h h99] at k1
    refine ⟨⟨?_, fun _ => ?_⟩, ⟨?_, fun _ => ?_⟩, fun j hj => ?_⟩
    · have : 11 / 100 < f t / t ^ 4 := by linarith
      rw [lt_div_iff₀ h4] at this
      linarith
    · have : 11 / 100 < f t / t ^ 4 := by linarith
      rw [lt_div_iff₀ h4] at this
      linarith
    · have : V t / t ^ 4 < 1 / 50 := by linarith
      rw [div_lt_iff₀ h4] at this
      linarith
    · have : V t / t ^ 4 < 1 / 50 := by linarith
      rw [div_lt_iff₀ h4] at this
      linarith
    · have := k2 _ (getD_mem_of_lt (by rw [P2_e_length]; exact hj))
      rw [he2 t h h99 j hj] at this
      linarith

end BecknerOnofri.V2.Interval
