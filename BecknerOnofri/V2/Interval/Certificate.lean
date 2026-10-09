module

public import BecknerOnofri.V2.Interval.CheckSound

@[expose] public section

/-!
# From the cell checker to the scalar inequalities on a whole row

`Row.checkCell r k = true` for every `k < r.count` implies the margin inequalities of the row at every
point of `[aN/aD, bN/bD]`, for the real semantics (`semRun`, `jetRun`) of the straight-line
program `familyProg r.small`.  For the first row we integrate (Lagrange form of Taylor's theorem
for the coherent chains, centred at the left end point) from the vanishing of the jets at that point,
which is a hypothesis (`hzf`, `hzv`).

Nothing here identifies the program with the manuscript's formulae: that is a separate bridge
(the hypotheses `hf`, `hV`, `he` of the final theorems in `Final.lean`).
-/

namespace BecknerOnofri.V2.Interval

open PowerSeries Finset

theorem Row.cell_le (r : Row) (hstep : r.aN * r.bD ≤ r.bN * r.aD) (k : ℕ) :
    (r.cell k).lo ≤ (r.cell k).hi := by
  simp only [Row.cell]
  have h0 : 0 ≤ r.bN * r.aD - r.aN * r.bD := by omega
  nlinarith

theorem okSmallF_get {m : ℤ × ℕ} {st : RS} {i : ℕ} (h : Row.okSmallF m st i = true) :
    ∃ cj, st.get i = some cj := by
  unfold Row.okSmallF at h
  cases hg : st.get i with
  | none => rw [hg] at h; simp at h
  | some cj => exact ⟨cj, rfl⟩

theorem okSmallV_get {m : ℤ × ℕ} {st : RS} {i : ℕ} (h : Row.okSmallV m st i = true) :
    ∃ cj, st.get i = some cj := by
  unfold Row.okSmallV at h
  cases hg : st.get i with
  | none => rw [hg] at h; simp at h
  | some cj => exact ⟨cj, rfl⟩

/-- Chain of the register `i` of the program `p` (`g_k(s) = coeff k (jet of register i at s)`). -/
noncomputable def chain (p : Prog) (i : ℕ) (s : ℝ) : ℝ⟦X⟧ := (jetRun s p).getD i 0

/-- What `checkCell` certifies on one cell of a Taylor-type (second and third) row. -/
theorem checkCell_big {r : Row} (hr : r.Valid) (hstep : r.aN * r.bD ≤ r.bN * r.aD)
    (hsm : r.small = false) (hm0 : 0 < r.m0.2) (hm1 : 0 < r.m1.2) (hm2 : 0 < r.m2.2) {k : ℕ}
    (h : r.checkCell k = true) {t : ℝ} (ht : t ∈ Set.Icc (r.lo' k) (r.hi' k)) :
    (r.m0.1 : ℝ) / r.m0.2 < (semRun t (familyProg r.small).1).getD (familyProg r.small).2.f 0 ∧
    (r.m1.1 : ℝ) / r.m1.2 < (semRun t (familyProg r.small).1).getD (familyProg r.small).2.v 0 ∧
    ∀ i ∈ (familyProg r.small).2.e,
      (r.m2.1 : ℝ) / r.m2.2 < (semRun t (familyProg r.small).1).getD i 0 := by
  unfold Row.checkCell at h
  dsimp only at h
  split at h
  · exact absurd h (by simp)
  · rename_i st hst
    have hc : (r.small = true) = False := by simp [hsm]
    simp only [hc, ↓reduceIte] at h
    simp only [Bool.and_eq_true, List.all_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    have hden := r.den_pos hr k
    have hle := r.cell_le hstep k
    exact ⟨okAt_sound hden hle hst hm0 h1 ht, okAt_sound hden hle hst hm1 h2 ht,
      fun i hi => okAt_sound hden hle hst hm2 (h3 i hi) ht⟩

/-- What `checkCell` certifies on one cell of the first row. -/
theorem checkCell_small {r : Row} (hr : r.Valid) (hstep : r.aN * r.bD ≤ r.bN * r.aD)
    (hsm : r.small = true) (hm0 : 0 < r.m0.2) (hm1 : 0 < r.m1.2) (hm2 : 0 < r.m2.2) {k : ℕ}
    (h : r.checkCell k = true) :
    (Coh (Set.Icc (r.lo' k) (r.hi' k)) (chain (familyProg r.small).1 (familyProg r.small).2.f) ∧
      ∀ t ∈ Set.Icc (r.lo' k) (r.hi' k), 1 / 10 + (r.m0.1 : ℝ) / r.m0.2 <
        coeff 4 (chain (familyProg r.small).1 (familyProg r.small).2.f t)) ∧
    (Coh (Set.Icc (r.lo' k) (r.hi' k)) (chain (familyProg r.small).1 (familyProg r.small).2.v) ∧
      ∀ t ∈ Set.Icc (r.lo' k) (r.hi' k),
        coeff 4 (chain (familyProg r.small).1 (familyProg r.small).2.v t) <
          1 / 50 - (r.m1.1 : ℝ) / r.m1.2) ∧
    ∀ t ∈ Set.Icc (r.lo' k) (r.hi' k), ∀ i ∈ (familyProg r.small).2.e,
      (r.m2.1 : ℝ) / r.m2.2 < (semRun t (familyProg r.small).1).getD i 0 := by
  unfold Row.checkCell at h
  dsimp only at h
  split at h
  · exact absurd h (by simp)
  · rename_i st hst
    have hc : (r.small = true) = True := eq_true hsm
    simp only [hc, ↓reduceIte] at h
    simp only [Bool.and_eq_true, List.all_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    have hden := r.den_pos hr k
    have hle := r.cell_le hstep k
    obtain ⟨cf, hcf⟩ := okSmallF_get h1
    obtain ⟨cv, hcv⟩ := okSmallV_get h2
    exact ⟨⟨cell_coh hden hle hst hcf, fun t ht => okSmallF_sound hden hle hst hm0 h1 ht⟩,
      ⟨cell_coh hden hle hst hcv, fun t ht => okSmallV_sound hden hle hst hm1 h2 ht⟩,
      fun t ht i hi => okSmallE_sound hden hle hst hm2 (h3 i hi) ht⟩

/-! ### Gluing the cells of a row -/

/-- Pointwise coherence glues over the cells of a row. -/
theorem Row.coh_of_cells {r : Row} (hr : r.Valid) {A : ℝ → ℝ⟦X⟧}
    (hA : ∀ k < r.count, Coh (Set.Icc (r.lo' k) (r.hi' k)) A) :
    Coh (Set.Icc ((r.aN : ℝ) / r.aD) ((r.bN : ℝ) / r.bD)) A := fun t ht => by
  obtain ⟨k, hk, h1, h2⟩ := r.cover hr ht
  exact hA k hk t ⟨h1, h2⟩

theorem Row.big_pointwise {r : Row} (hr : r.Valid) (hstep : r.aN * r.bD ≤ r.bN * r.aD)
    (hsm : r.small = false) (hm0 : 0 < r.m0.2) (hm1 : 0 < r.m1.2) (hm2 : 0 < r.m2.2)
    (hcheck : ∀ k < r.count, r.checkCell k = true) {t : ℝ}
    (ht : (r.aN : ℝ) / r.aD ≤ t ∧ t ≤ (r.bN : ℝ) / r.bD) :
    (r.m0.1 : ℝ) / r.m0.2 < (semRun t (familyProg r.small).1).getD (familyProg r.small).2.f 0 ∧
    (r.m1.1 : ℝ) / r.m1.2 < (semRun t (familyProg r.small).1).getD (familyProg r.small).2.v 0 ∧
    ∀ i ∈ (familyProg r.small).2.e,
      (r.m2.1 : ℝ) / r.m2.2 < (semRun t (familyProg r.small).1).getD i 0 := by
  obtain ⟨k, hk, h1, h2⟩ := r.cover hr ht
  exact checkCell_big hr hstep hsm hm0 hm1 hm2 (hcheck k hk) ⟨h1, h2⟩

theorem Row.small_pointwise {r : Row} (hr : r.Valid) (hstep : r.aN * r.bD ≤ r.bN * r.aD)
    (hsm : r.small = true) (hm0 : 0 < r.m0.2) (hm1 : 0 < r.m1.2) (hm2 : 0 < r.m2.2)
    (hcheck : ∀ k < r.count, r.checkCell k = true) :
    (Coh (Set.Icc ((r.aN : ℝ) / r.aD) ((r.bN : ℝ) / r.bD))
        (chain (familyProg r.small).1 (familyProg r.small).2.f) ∧
      ∀ t, (r.aN : ℝ) / r.aD ≤ t → t ≤ (r.bN : ℝ) / r.bD →
        1 / 10 + (r.m0.1 : ℝ) / r.m0.2 < coeff 4 (chain (familyProg r.small).1 (familyProg r.small).2.f t)) ∧
    (Coh (Set.Icc ((r.aN : ℝ) / r.aD) ((r.bN : ℝ) / r.bD))
        (chain (familyProg r.small).1 (familyProg r.small).2.v) ∧
      ∀ t, (r.aN : ℝ) / r.aD ≤ t → t ≤ (r.bN : ℝ) / r.bD →
        coeff 4 (chain (familyProg r.small).1 (familyProg r.small).2.v t) <
          1 / 50 - (r.m1.1 : ℝ) / r.m1.2) ∧
    ∀ t, (r.aN : ℝ) / r.aD ≤ t → t ≤ (r.bN : ℝ) / r.bD → ∀ i ∈ (familyProg r.small).2.e,
      (r.m2.1 : ℝ) / r.m2.2 < (semRun t (familyProg r.small).1).getD i 0 := by
  have hc := fun k hk => checkCell_small hr hstep hsm hm0 hm1 hm2 (hcheck k hk)
  refine ⟨⟨r.coh_of_cells hr fun k hk => (hc k hk).1.1, fun t h1 h2 => ?_⟩,
    ⟨r.coh_of_cells hr fun k hk => (hc k hk).2.1.1, fun t h1 h2 => ?_⟩, fun t h1 h2 i hi => ?_⟩
  · obtain ⟨k, hk, a, b⟩ := r.cover hr ⟨h1, h2⟩
    exact (hc k hk).1.2 t ⟨a, b⟩
  · obtain ⟨k, hk, a, b⟩ := r.cover hr ⟨h1, h2⟩
    exact (hc k hk).2.1.2 t ⟨a, b⟩
  · obtain ⟨k, hk, a, b⟩ := r.cover hr ⟨h1, h2⟩
    exact (hc k hk).2.2 t ⟨a, b⟩ i hi

/-- Real value of register `i` of the program `p` at `t`. -/
noncomputable def regVal (p : Prog) (i : ℕ) (t : ℝ) : ℝ := (semRun t p).getD i 0

theorem regVal_eq_coeff0 (p : Prog) (i : ℕ) (t : ℝ) : regVal p i t = coeff 0 (chain p i t) :=
  (coeff0_jetRun t p i).symm

/-- Lagrange-Taylor integration from the left end point `a` of a coherent chain whose first four
coefficients vanish at `a` and whose fourth coefficient is bounded below by `c` on `[a, b]`. -/
theorem chain_taylor_lower {a b t c : ℝ} {A : ℝ → ℝ⟦X⟧} (hA : Coh (Set.Icc a b) A)
    (hz : ∀ n < 4, coeff n (A a) = 0) (h4 : ∀ s, a ≤ s → s ≤ b → c < coeff 4 (A s))
    (h1 : a ≤ t) (h2 : t ≤ b) :
    c * (t - a) ^ 4 ≤ coeff 0 (A t) ∧ (a < t → c * (t - a) ^ 4 < coeff 0 (A t)) := by
  have hmem : a ∈ Set.Icc a b := ⟨le_rfl, h1.trans h2⟩
  obtain ⟨ξ, hξ, hT⟩ := hA.taylor hmem ⟨h1, h2⟩ 3
  have sf : ∑ k ∈ range (3 + 1), coeff k (A a) * (t - a) ^ k = 0 :=
    sum_eq_zero fun k hk => by rw [hz k (by simpa using hk), zero_mul]
  rw [sf, zero_add] at hT
  have hx := h4 ξ hξ.1 hξ.2
  have hd4 : 0 ≤ (t - a) ^ 4 := by positivity
  refine ⟨?_, fun hlt => ?_⟩
  · rw [hT]
    exact mul_le_mul_of_nonneg_right hx.le hd4
  · rw [hT]
    have h0 : 0 < t - a := by linarith
    exact mul_lt_mul_of_pos_right hx (by positivity)

/-- Upper analogue of `chain_taylor_lower`. -/
theorem chain_taylor_upper {a b t c : ℝ} {A : ℝ → ℝ⟦X⟧} (hA : Coh (Set.Icc a b) A)
    (hz : ∀ n < 4, coeff n (A a) = 0) (h4 : ∀ s, a ≤ s → s ≤ b → coeff 4 (A s) < c)
    (h1 : a ≤ t) (h2 : t ≤ b) :
    coeff 0 (A t) ≤ c * (t - a) ^ 4 ∧ (a < t → coeff 0 (A t) < c * (t - a) ^ 4) := by
  have hmem : a ∈ Set.Icc a b := ⟨le_rfl, h1.trans h2⟩
  obtain ⟨ξ, hξ, hT⟩ := hA.taylor hmem ⟨h1, h2⟩ 3
  have sf : ∑ k ∈ range (3 + 1), coeff k (A a) * (t - a) ^ k = 0 :=
    sum_eq_zero fun k hk => by rw [hz k (by simpa using hk), zero_mul]
  rw [sf, zero_add] at hT
  have hx := h4 ξ hξ.1 hξ.2
  have hd4 : 0 ≤ (t - a) ^ 4 := by positivity
  refine ⟨?_, fun hlt => ?_⟩
  · rw [hT]
    exact mul_le_mul_of_nonneg_right hx.le hd4
  · rw [hT]
    have h0 : 0 < t - a := by linarith
    exact mul_lt_mul_of_pos_right hx (by positivity)

/-- First row: Lagrange-Taylor integration of the coherent chains from the left end point `a`,
where the jets of `f` and `𝒱` vanish to order four (hypotheses `hzf`, `hzv`). -/
theorem Row.small_taylor {r : Row} (hr : r.Valid) (hstep : r.aN * r.bD ≤ r.bN * r.aD)
    (hsm : r.small = true) (hm0 : 0 < r.m0.2) (hm1 : 0 < r.m1.2) (hm2 : 0 < r.m2.2)
    (hcheck : ∀ k < r.count, r.checkCell k = true)
    (hzf : ∀ n < 4, coeff n (chain (familyProg r.small).1 (familyProg r.small).2.f
      ((r.aN : ℝ) / r.aD)) = 0)
    (hzv : ∀ n < 4, coeff n (chain (familyProg r.small).1 (familyProg r.small).2.v
      ((r.aN : ℝ) / r.aD)) = 0) :
    ∀ t, (r.aN : ℝ) / r.aD ≤ t → t ≤ (r.bN : ℝ) / r.bD →
      ((1 / 10 + (r.m0.1 : ℝ) / r.m0.2) * (t - (r.aN : ℝ) / r.aD) ^ 4 ≤
          regVal (familyProg r.small).1 (familyProg r.small).2.f t ∧
        ((r.aN : ℝ) / r.aD < t → (1 / 10 + (r.m0.1 : ℝ) / r.m0.2) * (t - (r.aN : ℝ) / r.aD) ^ 4 <
          regVal (familyProg r.small).1 (familyProg r.small).2.f t)) ∧
      (regVal (familyProg r.small).1 (familyProg r.small).2.v t ≤
          (1 / 50 - (r.m1.1 : ℝ) / r.m1.2) * (t - (r.aN : ℝ) / r.aD) ^ 4 ∧
        ((r.aN : ℝ) / r.aD < t → regVal (familyProg r.small).1 (familyProg r.small).2.v t <
          (1 / 50 - (r.m1.1 : ℝ) / r.m1.2) * (t - (r.aN : ℝ) / r.aD) ^ 4)) ∧
      ∀ i ∈ (familyProg r.small).2.e, (r.m2.1 : ℝ) / r.m2.2 < regVal (familyProg r.small).1 i t := by
  obtain ⟨⟨cf, hf4⟩, ⟨cv, hv4⟩, he⟩ := Row.small_pointwise hr hstep hsm hm0 hm1 hm2 hcheck
  intro t h1 h2
  have F := chain_taylor_lower cf hzf hf4 h1 h2
  have V := chain_taylor_upper cv hzv hv4 h1 h2
  rw [← regVal_eq_coeff0] at F V
  exact ⟨F, V, fun i hi => he t h1 h2 i hi⟩

end BecknerOnofri.V2.Interval
