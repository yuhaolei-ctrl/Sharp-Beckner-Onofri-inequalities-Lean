module

public import BecknerOnofri.V2.Interval.ProgSound
public import BecknerOnofri.V2.Interval.Check

@[expose] public section

/-!
# Soundness of the cell checker

`Row.checkCell r k = true` implies the three scalar inequalities of the row on the whole closed
real cell, for the *program's* real functions (`semRun`).  The cell is the closed real interval
`[lo/den, hi/den]` of `Row.cell`.
-/

namespace BecknerOnofri.V2.Interval

open PowerSeries Finset

theorem Cell.ctx_ok (c : Cell) (hden : 0 < c.den) :
    CtxOK c.ctx ((c.lo : ℝ) / c.den) ((c.hi : ℝ) / c.den) := by
  have hd : (c.den : ℝ) ≠ 0 := by positivity
  refine ⟨?_, fun t ht => Iv.mem_ofRat2 hden hden ht.1 ht.2, fun s hs => ?_⟩
  · have := Iv.mem_ofRat (c.lo + c.hi) (2 * c.den) (by omega)
    have e : ((c.lo : ℝ) / c.den + (c.hi : ℝ) / c.den) / 2 =
        ((c.lo + c.hi : ℤ) : ℝ) / ((2 * c.den : ℕ) : ℝ) := by
      push_cast
      field_simp
    rw [e]
    exact this
  · rw [abs_le] at hs
    refine Iv.mem_ofRat2 (n₁ := -(c.hi - c.lo)) (n₂ := c.hi - c.lo) (by omega) (by omega) ?_ ?_
    · push_cast
      have : (0 : ℝ) < c.den := by exact_mod_cast hden
      rw [div_le_iff₀ (by positivity)]
      have := hs.1
      field_simp at this ⊢
      linarith
    · push_cast
      have : (0 : ℝ) < c.den := by exact_mod_cast hden
      rw [le_div_iff₀ (by positivity)]
      have := hs.2
      field_simp at this ⊢
      linarith

theorem absup_cast (a : Iv) : (a.absup : ℝ) = max |(a.lo : ℝ)| |(a.hi : ℝ)| := by
  have h : ∀ z : ℤ, (((z.natAbs : ℕ) : ℤ) : ℝ) = |(z : ℝ)| := by
    intro z; rw [Int.natCast_natAbs, Int.cast_abs]
  simp only [Iv.absup, Int.cast_max, h]

theorem absup_bound {a : Iv} {x : ℝ} (hx : a.Mem x) : |x| ≤ (a.absup : ℝ) / scale := by
  have hS := scale_pos
  rw [Iv.mem_iff_scaled] at hx
  rw [absup_cast, le_div_iff₀ hS, show |x| * (scale : ℝ) = |x * scale| by rw [abs_mul, abs_of_pos hS]]
  have h1 : |(a.lo : ℝ)| ≤ max |(a.lo : ℝ)| |(a.hi : ℝ)| := le_max_left _ _
  have h2 : |(a.hi : ℝ)| ≤ max |(a.lo : ℝ)| |(a.hi : ℝ)| := le_max_right _ _
  have h3 := neg_abs_le (a.lo : ℝ)
  have h4 := le_abs_self (a.hi : ℝ)
  rw [abs_le]
  constructor <;> linarith [hx.1, hx.2]

/-- Sum form of the integer error term of `taylorEnclosure`. -/
theorem foldl_add_int (f : ℕ → ℤ) (a : ℤ) (N : ℕ) :
    (List.range N).foldl (fun acc k => acc + f k) a = a + ∑ k ∈ range N, f k := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.foldl_append, ih, List.foldl_cons, List.foldl_nil, sum_range_succ]
    ring

theorem taylorEnclosure_sound {lo hi : ℝ} {Φ : ℝ → ℝ⟦X⟧} (hΦ : Coh (Set.Icc lo hi) Φ)
    {mid box : Jet} (hmid : JMem mid (Φ ((lo + hi) / 2)))
    (hbox : ∀ t ∈ Set.Icc lo hi, JMem box (Φ t)) (hlohi : lo ≤ hi)
    {rn : ℤ} {rd : ℕ} (hrd : 0 < rd) (hr : (rn : ℝ) / rd = (hi - lo) / 2)
    {t : ℝ} (ht : t ∈ Set.Icc lo hi) :
    ((taylorEnclosure mid box rn rd).1 : ℝ) / (scale * (rd : ℝ) ^ 6) ≤ coeff 0 (Φ t) ∧
      coeff 0 (Φ t) ≤ ((taylorEnclosure mid box rn rd).2 : ℝ) / (scale * (rd : ℝ) ^ 6) := by
  have hS := scale_pos
  have hD : (0 : ℝ) < rd := by exact_mod_cast hrd
  have hm : (lo + hi) / 2 ∈ Set.Icc lo hi := ⟨by linarith, by linarith⟩
  obtain ⟨ξ, hξ, hT⟩ := hΦ.taylor hm ht 5
  set m : ℝ := (lo + hi) / 2 with hmdef
  set r : ℝ := (hi - lo) / 2 with hrdef
  set d : ℝ := t - m with hd
  have hdr : |d| ≤ r := by
    rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
  have hr0 : 0 ≤ r := by linarith
  -- bounds on the coefficients
  have hc : ∀ k, 1 ≤ k → k ≤ 5 → |coeff k (Φ m)| ≤ ((mid.get k).absup : ℝ) / scale :=
    fun k _ hk => absup_bound (hmid.2 k (by omega))
  have h6 : |coeff 6 (Φ ξ)| ≤ ((box.get 6).absup : ℝ) / scale :=
    absup_bound ((hbox ξ hξ).2 6 (by omega))
  set E : ℝ := ∑ k ∈ range 5, (((mid.get (k + 1)).absup : ℝ) / scale) * r ^ (k + 1) +
    (((box.get 6).absup : ℝ) / scale) * r ^ 6 with hE
  have hdiff : |coeff 0 (Φ t) - coeff 0 (Φ m)| ≤ E := by
    have e1 : coeff 0 (Φ t) - coeff 0 (Φ m) =
        ∑ k ∈ range 5, coeff (k + 1) (Φ m) * d ^ (k + 1) + coeff 6 (Φ ξ) * d ^ 6 := by
      rw [hT, sum_range_succ' _ 5]
      simp only [pow_zero, mul_one]
      ring
    rw [e1]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k hk => ?_)
      rw [abs_mul, abs_pow]
      have hk' := mem_range.mp hk
      exact mul_le_mul (hc (k + 1) (by omega) (by omega)) (pow_le_pow_left₀ (abs_nonneg _) hdr _)
        (by positivity) (le_trans (abs_nonneg _) (hc (k + 1) (by omega) (by omega)))
    · rw [abs_mul, abs_pow]
      exact mul_le_mul h6 (pow_le_pow_left₀ (abs_nonneg _) hdr _) (by positivity)
        (le_trans (abs_nonneg _) h6)
  -- the integer error term
  have herr : (((List.range 5).foldl
      (fun acc k0 => acc + ((mid.get (k0 + 1)).absup : ℤ) * rn ^ (k0 + 1) * (rd : ℤ) ^ (5 - k0))
      ((box.get 6).absup * rn ^ 6) : ℤ) : ℝ) = E * (scale * (rd : ℝ) ^ 6) := by
    rw [foldl_add_int (fun k0 => ((mid.get (k0 + 1)).absup : ℤ) * rn ^ (k0 + 1) * (rd : ℤ) ^ (5 - k0))]
    push_cast
    rw [hE, add_mul, sum_mul]
    have hr' : r = (rn : ℝ) / rd := hr.symm
    have hterm : ∀ k ∈ range 5,
        ((mid.get (k + 1)).absup : ℝ) / scale * r ^ (k + 1) * (scale * (rd : ℝ) ^ 6) =
          ((mid.get (k + 1)).absup : ℝ) * (rn : ℝ) ^ (k + 1) * (rd : ℝ) ^ (5 - k) := by
      intro k hk
      have hk' := mem_range.mp hk
      have e6 : (rd : ℝ) ^ 6 = (rd : ℝ) ^ (k + 1) * (rd : ℝ) ^ (5 - k) := by
        rw [← pow_add]; congr 1; omega
      rw [hr', e6, div_pow]
      field_simp
    rw [sum_congr rfl hterm]
    have : (((box.get 6).absup : ℝ) / scale * r ^ 6) * (scale * (rd : ℝ) ^ 6) =
        ((box.get 6).absup : ℝ) * (rn : ℝ) ^ 6 := by
      rw [hr', div_pow]; field_simp
    rw [this]; ring
  have hD6 : (0 : ℝ) < scale * (rd : ℝ) ^ 6 := by positivity
  have hmem0 : (mid.get 0).Mem (coeff 0 (Φ m)) := hmid.2 0 (by omega)
  have hb0 : (box.get 0).Mem (coeff 0 (Φ t)) := (hbox t ht).2 0 (by omega)
  rw [Iv.mem_iff_scaled] at hmem0 hb0
  simp only [taylorEnclosure, Int.cast_max, Int.cast_min]
  push_cast
  rw [herr]
  have hdiff' := abs_le.mp hdiff
  constructor
  · rw [div_le_iff₀ hD6]
    refine max_le ?_ ?_
    · have : (rd : ℝ) ^ 6 > 0 := by positivity
      nlinarith [hdiff'.1, hmem0.1, mul_pos hS this]
    · nlinarith [hb0.1, hS, mul_pos hS (show (rd : ℝ) ^ 6 > 0 by positivity)]
  · rw [le_div_iff₀ hD6]
    refine le_min ?_ ?_
    · have p1 := mul_le_mul_of_nonneg_right hdiff'.2 hD6.le
      have p2 := mul_le_mul_of_nonneg_right hmem0.2 (pow_pos hD 6).le
      linarith
    · nlinarith [hb0.2, hS, mul_pos hS (show (rd : ℝ) ^ 6 > 0 by positivity)]


/-! ### Cells and coverage -/

/-- Positivity of the data of a row. -/
structure Row.Valid (r : Row) : Prop where
  aD : 0 < r.aD
  bD : 0 < r.bD
  count : 0 < r.count

/-- Real left end point of the real cell `k` of a row. -/
noncomputable def Row.lo' (r : Row) (k : ℕ) : ℝ := ((r.cell k).lo : ℝ) / (r.cell k).den
/-- Real right end point of the real cell `k` of a row. -/
noncomputable def Row.hi' (r : Row) (k : ℕ) : ℝ := ((r.cell k).hi : ℝ) / (r.cell k).den

theorem Row.lo'_eq (r : Row) (hr : r.Valid) (k : ℕ) :
    r.lo' k = (r.aN : ℝ) / r.aD + ((r.bN : ℝ) / r.bD - (r.aN : ℝ) / r.aD) * k / r.count := by
  have h1 : (r.aD : ℝ) ≠ 0 := by have := hr.aD; positivity
  have h2 : (r.bD : ℝ) ≠ 0 := by have := hr.bD; positivity
  have h3 : (r.count : ℝ) ≠ 0 := by have := hr.count; positivity
  simp only [Row.lo', Row.cell]
  push_cast
  field_simp

theorem Row.hi'_eq (r : Row) (hr : r.Valid) (k : ℕ) :
    r.hi' k = (r.aN : ℝ) / r.aD + ((r.bN : ℝ) / r.bD - (r.aN : ℝ) / r.aD) * (k + 1) / r.count := by
  have h1 : (r.aD : ℝ) ≠ 0 := by have := hr.aD; positivity
  have h2 : (r.bD : ℝ) ≠ 0 := by have := hr.bD; positivity
  have h3 : (r.count : ℝ) ≠ 0 := by have := hr.count; positivity
  simp only [Row.hi', Row.cell]
  push_cast
  field_simp

theorem Row.den_pos (r : Row) (hr : r.Valid) (k : ℕ) : 0 < (r.cell k).den := by
  have := hr.aD; have := hr.bD; have := hr.count
  simp only [Row.cell]
  positivity

theorem Row.lo'_le_hi' (r : Row) (hr : r.Valid) (hAB : (r.aN : ℝ) / r.aD ≤ (r.bN : ℝ) / r.bD)
    (k : ℕ) : r.lo' k ≤ r.hi' k := by
  rw [r.lo'_eq hr, r.hi'_eq hr]
  have h3 : (0 : ℝ) < r.count := by exact_mod_cast hr.count
  have : 0 ≤ ((r.bN : ℝ) / r.bD - (r.aN : ℝ) / r.aD) := by linarith
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  gcongr
  linarith

/-- The cells of a row cover its range. -/
theorem Row.cover (r : Row) (hr : r.Valid)
    {t : ℝ} (ht : (r.aN : ℝ) / r.aD ≤ t ∧ t ≤ (r.bN : ℝ) / r.bD) :
    ∃ k, k < r.count ∧ r.lo' k ≤ t ∧ t ≤ r.hi' k := by
  classical
  set N := r.count with hN
  have hN0 : 0 < N := hr.count
  set P : ℕ → Prop := fun k => r.lo' k ≤ t with hP
  have h0 : P 0 := by
    rw [hP]; simp only; rw [r.lo'_eq hr]; simpa using ht.1
  set k := Nat.findGreatest P (N - 1) with hk
  have hkP : P k := Nat.findGreatest_spec (P := P) (Nat.zero_le _) h0
  have hkle : k ≤ N - 1 := Nat.findGreatest_le _
  refine ⟨k, by omega, hkP, ?_⟩
  rcases Nat.lt_or_ge k (N - 1) with hlt | hge
  · have := Nat.findGreatest_is_greatest (P := P) (Nat.lt_succ_self k) (by omega)
    have hnot : ¬ r.lo' (k + 1) ≤ t := this
    push Not at hnot
    have e1 : r.hi' k = r.lo' (k + 1) := by
      rw [r.hi'_eq hr, r.lo'_eq hr]; push_cast; ring
    rw [e1]; exact hnot.le
  · have hkN : k + 1 = N := by omega
    rw [r.hi'_eq hr]
    have h3 : (0 : ℝ) < N := by exact_mod_cast hN0
    have : ((k : ℝ) + 1) = N := by exact_mod_cast hkN
    rw [this]
    have : (r.aN : ℝ) / r.aD + ((r.bN : ℝ) / r.bD - (r.aN : ℝ) / r.aD) * N / N = (r.bN : ℝ) / r.bD := by
      field_simp; ring
    rw [this]; exact ht.2


/-! ### One cell -/

theorem okLow_sound {m : ℤ × ℕ} {e : ℤ × ℤ} {den : ℕ} (h : Row.okLow m e den = true)
    (hm : 0 < m.2) (hden : 0 < den) : (m.1 : ℝ) / m.2 < (e.1 : ℝ) / den := by
  simp only [Row.okLow, gtQ, Bool.and_eq_true, decide_eq_true_eq] at h
  have h2 : (m.1 : ℝ) * den < (e.1 : ℝ) * m.2 := by exact_mod_cast h.2
  have hm' : (0 : ℝ) < m.2 := by exact_mod_cast hm
  have hd' : (0 : ℝ) < den := by exact_mod_cast hden
  rw [div_lt_div_iff₀ hm' hd']
  linarith

theorem Cell.rad_eq (c : Cell) (hden : 0 < c.den) :
    ((c.hi - c.lo : ℤ) : ℝ) / ((2 * c.den : ℕ) : ℝ) =
      ((c.hi : ℝ) / c.den - (c.lo : ℝ) / c.den) / 2 := by
  have hd : (c.den : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp

theorem cast_den (rd : ℕ) : ((scale.toNat * rd ^ 6 : ℕ) : ℝ) = scale * (rd : ℝ) ^ 6 := by
  have : ((scale.toNat : ℕ) : ℤ) = scale := Int.toNat_of_nonneg (by unfold scale; positivity)
  have h2 : ((scale.toNat : ℕ) : ℝ) = scale := by exact_mod_cast this
  push_cast
  rw [h2]

theorem Cell.le_real {c : Cell} (hden : 0 < c.den) (hle : c.lo ≤ c.hi) :
    (c.lo : ℝ) / c.den ≤ (c.hi : ℝ) / c.den := by
  have : (c.lo : ℝ) ≤ c.hi := by exact_mod_cast hle
  have hd : (0 : ℝ) < c.den := by exact_mod_cast hden
  gcongr

/-- The interpreter invariant on a cell. -/
theorem cell_inv {c : Cell} (hden : 0 < c.den) (hle : c.lo ≤ c.hi) {p : Prog} {st : RS}
    (hrun : runRS c.ctx p = some st) :
    st.n = st.rev.length ∧
      Inv c.ctx ((c.lo : ℝ) / c.den) ((c.hi : ℝ) / c.den) st.rev.reverse (fun s => jetRun s p) :=
  runRS_sound (Cell.ctx_ok c hden) (Cell.le_real hden hle) hrun

/-- Coherence of the chain of a register on a cell. -/
theorem cell_coh {c : Cell} (hden : 0 < c.den) (hle : c.lo ≤ c.hi) {p : Prog} {st : RS}
    (hrun : runRS c.ctx p = some st) {i : ℕ} {cj : CJet} (hi : st.get i = some cj) :
    Coh (Set.Icc ((c.lo : ℝ) / c.den) ((c.hi : ℝ) / c.den)) (fun s => (jetRun s p).getD i 0) := by
  obtain ⟨hwf, hI⟩ := cell_inv hden hle hrun
  obtain ⟨hlt, _⟩ := RS.get_some hwf hi
  exact hI.coh i hlt

/-- The box of a register encloses the normalized derivatives over the cell. -/
theorem cell_box {c : Cell} (hden : 0 < c.den) (hle : c.lo ≤ c.hi) {p : Prog} {st : RS}
    (hrun : runRS c.ctx p = some st) {i : ℕ} {cj : CJet} (hi : st.get i = some cj)
    {t : ℝ} (ht : t ∈ Set.Icc ((c.lo : ℝ) / c.den) ((c.hi : ℝ) / c.den)) (k : ℕ) (hk : k < 7) :
    (cj.box.get k).Mem (coeff k ((jetRun t p).getD i 0)) := by
  obtain ⟨hwf, hI⟩ := cell_inv hden hle hrun
  obtain ⟨hlt, hget⟩ := RS.get_some hwf hi
  have := (hI.box i hlt t ht).2 k hk
  rw [hget] at this
  exact this

theorem gtQ_sound {a : ℤ} {b : ℕ} {c : ℤ} {d : ℕ} (h : gtQ a b c d = true) (hb : 0 < b)
    (hd : 0 < d) : (c : ℝ) / d < (a : ℝ) / b := by
  simp only [gtQ, decide_eq_true_eq] at h
  have h2 : (c : ℝ) * b < (a : ℝ) * d := by exact_mod_cast h
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  rw [div_lt_div_iff₀ hd' hb']
  exact h2

theorem ltQ_sound {a : ℤ} {b : ℕ} {c : ℤ} {d : ℕ} (h : ltQ a b c d = true) (hb : 0 < b)
    (hd : 0 < d) : (a : ℝ) / b < (c : ℝ) / d := by
  simp only [ltQ, decide_eq_true_eq] at h
  have h2 : (a : ℝ) * d < (c : ℝ) * b := by exact_mod_cast h
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  rw [div_lt_div_iff₀ hb' hd']
  exact h2

theorem scale_nat_pos : 0 < scale.toNat := by
  have : (0 : ℤ) < scale := scale_pos_int
  omega

theorem cast_scale_nat : ((scale.toNat : ℕ) : ℝ) = (scale : ℝ) := by
  have : ((scale.toNat : ℕ) : ℤ) = scale := Int.toNat_of_nonneg scale_pos_int.le
  exact_mod_cast this

/-- One cell of the general (Taylor) type: the register `i` of a successful run is enclosed from
below and above by the Taylor enclosure. -/
theorem cell_taylor {c : Cell} (hden : 0 < c.den) (hle : c.lo ≤ c.hi) {p : Prog} {st : RS}
    (hrun : runRS c.ctx p = some st) {i : ℕ} {cj : CJet} (hi : st.get i = some cj)
    {t : ℝ} (ht : t ∈ Set.Icc ((c.lo : ℝ) / c.den) ((c.hi : ℝ) / c.den)) :
    ((taylorEnclosure cj.mid cj.box (c.hi - c.lo) (2 * c.den)).1 : ℝ) /
        (scale * ((2 * c.den : ℕ) : ℝ) ^ 6) ≤ (semRun t p).getD i 0 ∧
      (semRun t p).getD i 0 ≤ ((taylorEnclosure cj.mid cj.box (c.hi - c.lo) (2 * c.den)).2 : ℝ) /
        (scale * ((2 * c.den : ℕ) : ℝ) ^ 6) := by
  obtain ⟨hwf, hI⟩ := cell_inv hden hle hrun
  obtain ⟨hlt, hget⟩ := RS.get_some hwf hi
  have hbox := fun t ht => hI.box i hlt t ht
  rw [hget] at hbox
  have hmid := hI.mid i hlt
  rw [hget] at hmid
  have := taylorEnclosure_sound (hI.coh i hlt) hmid hbox (Cell.le_real hden hle)
    (rn := c.hi - c.lo) (rd := 2 * c.den) (by omega) (Cell.rad_eq c hden) ht
  rw [coeff0_jetRun] at this
  exact this

/-- Soundness of the Taylor-type test of a single register on a cell. -/
theorem okAt_sound {c : Cell} (hden : 0 < c.den) (hle : c.lo ≤ c.hi) {p : Prog} {st : RS}
    (hrun : runRS c.ctx p = some st) {m : ℤ × ℕ} (hm : 0 < m.2) {i : ℕ}
    (h : Row.okAt c st m i = true)
    {t : ℝ} (ht : t ∈ Set.Icc ((c.lo : ℝ) / c.den) ((c.hi : ℝ) / c.den)) :
    (m.1 : ℝ) / m.2 < (semRun t p).getD i 0 := by
  unfold Row.okAt at h
  cases hg : st.get i with
  | none => rw [hg] at h; simp at h
  | some cj =>
    rw [hg] at h
    have hpos : 0 < scale.toNat * (2 * c.den) ^ 6 := by
      have := scale_nat_pos; positivity
    have h1 := okLow_sound h hm hpos
    rw [cast_den] at h1
    exact lt_of_lt_of_le h1 (cell_taylor hden hle hrun hg ht).1

/-- First-row test for `f`: `f⁗/4!` exceeds `1/10 + m`. -/
theorem okSmallF_sound {c : Cell} (hden : 0 < c.den) (hle : c.lo ≤ c.hi) {p : Prog} {st : RS}
    (hrun : runRS c.ctx p = some st) {m : ℤ × ℕ} (hm : 0 < m.2) {i : ℕ}
    (h : Row.okSmallF m st i = true)
    {t : ℝ} (ht : t ∈ Set.Icc ((c.lo : ℝ) / c.den) ((c.hi : ℝ) / c.den)) :
    1 / 10 + (m.1 : ℝ) / m.2 < coeff 4 ((jetRun t p).getD i 0) := by
  unfold Row.okSmallF at h
  cases hg : st.get i with
  | none => rw [hg] at h; simp at h
  | some cj =>
    rw [hg] at h
    have h1 := gtQ_sound h scale_nat_pos (by omega : 0 < 10 * m.2)
    have hb := cell_box hden hle hrun hg ht 4 (by omega)
    rw [Iv.mem_iff_scaled] at hb
    have hS := scale_pos
    have e : (1 : ℝ) / 10 + (m.1 : ℝ) / m.2 =
        (((1 * (m.2 : ℤ) + 10 * m.1 : ℤ) : ℝ)) / ((10 * m.2 : ℕ) : ℝ) := by
      have hm0 : (0 : ℝ) < m.2 := by exact_mod_cast hm
      have : (m.2 : ℝ) ≠ 0 := hm0.ne'
      push_cast
      field_simp
    rw [e]
    refine lt_of_lt_of_le h1 ?_
    rw [cast_scale_nat, div_le_iff₀ hS]
    exact hb.1

/-- First-row test for `𝒱`: `𝒱⁗/4!` is below `1/50 - m`. -/
theorem okSmallV_sound {c : Cell} (hden : 0 < c.den) (hle : c.lo ≤ c.hi) {p : Prog} {st : RS}
    (hrun : runRS c.ctx p = some st) {m : ℤ × ℕ} (hm : 0 < m.2) {i : ℕ}
    (h : Row.okSmallV m st i = true)
    {t : ℝ} (ht : t ∈ Set.Icc ((c.lo : ℝ) / c.den) ((c.hi : ℝ) / c.den)) :
    coeff 4 ((jetRun t p).getD i 0) < 1 / 50 - (m.1 : ℝ) / m.2 := by
  unfold Row.okSmallV at h
  cases hg : st.get i with
  | none => rw [hg] at h; simp at h
  | some cj =>
    rw [hg] at h
    have h1 := ltQ_sound h scale_nat_pos (by omega : 0 < 50 * m.2)
    have hb := cell_box hden hle hrun hg ht 4 (by omega)
    rw [Iv.mem_iff_scaled] at hb
    have hS := scale_pos
    have e : (1 : ℝ) / 50 - (m.1 : ℝ) / m.2 =
        (((1 * (m.2 : ℤ) - 50 * m.1 : ℤ) : ℝ)) / ((50 * m.2 : ℕ) : ℝ) := by
      have hm0 : (0 : ℝ) < m.2 := by exact_mod_cast hm
      have : (m.2 : ℝ) ≠ 0 := hm0.ne'
      push_cast
      field_simp
    rw [e]
    refine lt_of_le_of_lt ?_ h1
    rw [cast_scale_nat, le_div_iff₀ hS]
    exact hb.2

/-- First-row test for `e_j + 1/4`: the register is above `m` (box entry 0). -/
theorem okSmallE_sound {c : Cell} (hden : 0 < c.den) (hle : c.lo ≤ c.hi) {p : Prog} {st : RS}
    (hrun : runRS c.ctx p = some st) {m : ℤ × ℕ} (hm : 0 < m.2) {i : ℕ}
    (h : Row.okSmallE m st i = true)
    {t : ℝ} (ht : t ∈ Set.Icc ((c.lo : ℝ) / c.den) ((c.hi : ℝ) / c.den)) :
    (m.1 : ℝ) / m.2 < (semRun t p).getD i 0 := by
  unfold Row.okSmallE at h
  cases hg : st.get i with
  | none => rw [hg] at h; simp at h
  | some cj =>
    rw [hg] at h
    have h1 := gtQ_sound h scale_nat_pos hm
    have hb := cell_box hden hle hrun hg ht 0 (by omega)
    rw [Iv.mem_iff_scaled] at hb
    have hS := scale_pos
    rw [← coeff0_jetRun]
    refine lt_of_lt_of_le h1 ?_
    rw [cast_scale_nat, div_le_iff₀ hS]
    exact hb.1

end BecknerOnofri.V2.Interval
