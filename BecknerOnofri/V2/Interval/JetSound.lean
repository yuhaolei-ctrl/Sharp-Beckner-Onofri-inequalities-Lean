module

public import BecknerOnofri.V2.Interval.ArithSound
public import BecknerOnofri.V2.Interval.Jet
public import BecknerOnofri.V2.Interval.Coherent

@[expose] public section

/-!
# Soundness of the interval jets

`JMem A φ` : the list `A` of seven intervals encloses the first seven coefficients of the formal
power series `φ` (the normalized derivatives `a^{(k)}/k!`).  We prove that every operation of
`Jet.lean` encloses the corresponding operation on power series (Cauchy product, reciprocal
`φ⁻¹`, logarithm `logSeries φ`), and that mean-value tightening is sound for coherent jets.
-/

namespace BecknerOnofri.V2.Interval

open PowerSeries Finset

/-- A list of seven intervals enclosing the first seven coefficients of `φ`. -/
def JMem (A : Jet) (φ : ℝ⟦X⟧) : Prop :=
  A.length = 7 ∧ ∀ k, k < 7 → (A.get k).Mem (coeff k φ)

theorem Jet.get_of_lt {A : Jet} {k : ℕ} (h : k < A.length) : A.get k = A[k] := by
  simp [Jet.get, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

/-! ### Sums -/

theorem foldl_range_mem {N : ℕ} {f : ℕ → Iv} {g : ℕ → ℝ} (h : ∀ k, k < N → (f k).Mem (g k)) :
    ((List.range N).foldl (fun acc k => acc.add (f k)) Iv.zero).Mem (∑ k ∈ range N, g k) := by
  induction N with
  | zero => simpa using Iv.mem_zero
  | succ N ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, sum_range_succ]
    exact Iv.mem_add (ih fun k hk => h k (by omega)) (h N (by omega))

theorem getD_replicate_self (n k : ℕ) (d : Iv) : (List.replicate n d).getD k d = d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split_ifs <;> simp

namespace JMem

theorem add {a b : Jet} {φ ψ : ℝ⟦X⟧} (ha : JMem a φ) (hb : JMem b ψ) :
    JMem (Jet.add a b) (φ + ψ) := by
  refine ⟨by simp [Jet.add, ha.1, hb.1], fun k hk => ?_⟩
  have h1 : k < a.length := by rw [ha.1]; exact hk
  have h2 : k < b.length := by rw [hb.1]; exact hk
  have : (Jet.add a b).get k = (a.get k).add (b.get k) := by
    simp [Jet.get, Jet.add, List.getD_eq_getElem?_getD, h1, h2]
  rw [this, map_add]
  exact Iv.mem_add (ha.2 k hk) (hb.2 k hk)

theorem neg {a : Jet} {φ : ℝ⟦X⟧} (ha : JMem a φ) : JMem (Jet.neg a) (-φ) := by
  refine ⟨by simp [Jet.neg, ha.1], fun k hk => ?_⟩
  have h1 : k < a.length := by rw [ha.1]; exact hk
  have : (Jet.neg a).get k = (a.get k).neg := by
    simp [Jet.get, Jet.neg, List.getD_eq_getElem?_getD, h1]
  rw [this, map_neg]
  exact Iv.mem_neg (ha.2 k hk)

theorem smul {a : Jet} {φ : ℝ⟦X⟧} {c : Iv} {v : ℝ} (ha : JMem a φ) (hc : c.Mem v) :
    JMem (Jet.smul a c) (C v * φ) := by
  refine ⟨by simp [Jet.smul, ha.1], fun k hk => ?_⟩
  have h1 : k < a.length := by rw [ha.1]; exact hk
  have : (Jet.smul a c).get k = (a.get k).mul c := by
    simp [Jet.get, Jet.smul, List.getD_eq_getElem?_getD, h1]
  rw [this, coeff_C_mul, mul_comm]
  exact Iv.mem_mul (ha.2 k hk) hc

theorem const {c : Iv} {v : ℝ} (hc : c.Mem v) : JMem (Jet.const c) (C v) := by
  refine ⟨by simp [Jet.const], fun k hk => ?_⟩
  rcases k with _ | k
  · simpa [Jet.get, Jet.const, coeff_C] using hc
  · have : (Jet.const c).get (k + 1) = Iv.zero := by
      simp only [Jet.get, Jet.const, List.getD_cons_succ, getD_replicate_self]
    rw [this]
    simpa [coeff_C] using Iv.mem_zero

theorem var {x : Iv} {v : ℝ} (hx : x.Mem v) : JMem (Jet.var x) (C v + X) := by
  refine ⟨by simp [Jet.var], fun k hk => ?_⟩
  rcases k with _ | _ | k
  · simpa [Jet.get, Jet.var, coeff_C, coeff_X] using hx
  · simpa [Jet.get, Jet.var, coeff_C, coeff_X] using Iv.mem_ofInt 1
  · have : (Jet.var x).get (k + 2) = Iv.zero := by
      simp only [Jet.get, Jet.var, List.getD_cons_succ, getD_replicate_self]
    rw [this]
    simpa [coeff_C, coeff_X] using Iv.mem_zero

theorem mul {a b : Jet} {φ ψ : ℝ⟦X⟧} (ha : JMem a φ) (hb : JMem b ψ) :
    JMem (Jet.mul a b) (φ * ψ) := by
  refine ⟨by simp [Jet.mul], fun n hn => ?_⟩
  have : (Jet.mul a b).get n = (List.range (n + 1)).foldl
      (fun acc k => acc.add ((a.get k).mul (b.get (n - k)))) Iv.zero := by
    simp [Jet.get, Jet.mul, List.getD_eq_getElem?_getD, hn]
  rw [this, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  exact foldl_range_mem fun k hk => Iv.mem_mul (ha.2 k (by omega)) (hb.2 (n - k) (by omega))

end JMem


/-! ### Reciprocal -/

/-- Recurrence for the coefficients of `φ⁻¹`. -/
theorem coeff_inv_succ (φ : ℝ⟦X⟧) (h0 : constantCoeff φ ≠ 0) (n : ℕ) :
    coeff (n + 1) φ⁻¹ =
      -(∑ k ∈ range (n + 1), coeff (k + 1) φ * coeff (n + 1 - (k + 1)) φ⁻¹) *
        (constantCoeff φ)⁻¹ := by
  have h := congrArg (coeff (n + 1)) (PowerSeries.mul_inv_cancel φ h0)
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, sum_range_succ'] at h
  simp only [coeff_one, Nat.succ_ne_zero, ite_false] at h
  simp only [Nat.sub_zero, coeff_zero_eq_constantCoeff_apply] at h
  field_simp
  linarith

theorem Jet.recipFold_mem {a : Jet} {φ : ℝ⟦X⟧} (ha : JMem a φ) (h0 : constantCoeff φ ≠ 0)
    {inv0 b0 : Iv} (hi : inv0.Mem (constantCoeff φ)⁻¹) (hb : b0.Mem (constantCoeff φ)⁻¹) :
    ∀ N, N ≤ 6 → (Jet.recipFold a inv0 b0 N).length = N + 1 ∧
      ∀ j, j ≤ N → ((Jet.recipFold a inv0 b0 N).getD j Iv.zero).Mem (coeff j φ⁻¹) := by
  intro N
  induction N with
  | zero =>
    intro _
    refine ⟨by simp [Jet.recipFold], fun j hj => ?_⟩
    have : j = 0 := by omega
    subst this
    simpa [Jet.recipFold, coeff_zero_eq_constantCoeff_apply] using hb
  | succ N ih =>
    intro hN
    obtain ⟨hlen, hmem⟩ := ih (by omega)
    set out := Jet.recipFold a inv0 b0 N with hout
    have hs : (List.range out.length).foldl
        (fun acc k0 => acc.add ((a.get (k0 + 1)).mul (out.getD (out.length - (k0 + 1)) Iv.zero)))
        Iv.zero |>.Mem (∑ k0 ∈ range (N + 1), coeff (k0 + 1) φ * coeff (N + 1 - (k0 + 1)) φ⁻¹) := by
      rw [hlen]
      exact foldl_range_mem fun k hk =>
        Iv.mem_mul (ha.2 (k + 1) (by omega)) (hmem _ (by omega))
    have hnew := Iv.mem_mul (Iv.mem_neg hs) hi
    have hrec := coeff_inv_succ φ h0 N
    refine ⟨?_, fun j hj => ?_⟩
    · simp [Jet.recipFold, recipStep, ← hout, hlen]
    · have e : Jet.recipFold a inv0 b0 (N + 1) = out ++ [(Iv.mul (Iv.neg
          ((List.range out.length).foldl
            (fun acc k0 => acc.add ((a.get (k0 + 1)).mul
              (out.getD (out.length - (k0 + 1)) Iv.zero))) Iv.zero)) inv0)] := rfl
      rw [e]
      rcases Nat.lt_or_ge j (N + 1) with hj' | hj'
      · rw [List.getD_append _ _ _ _ (by omega)]
        exact hmem j (by omega)
      · have : j = N + 1 := by omega
        subst this
        rw [List.getD_append_right _ _ _ _ (by omega)]
        simp only [hlen, Nat.sub_self, List.getD_cons_zero]
        rw [hrec]
        rw [hlen] at hnew
        exact hnew

theorem JMem.recip {a b : Jet} {φ : ℝ⟦X⟧} (ha : JMem a φ) (h : Jet.recip a = some b) :
    constantCoeff φ ≠ 0 ∧ JMem b φ⁻¹ := by
  unfold Jet.recip at h
  obtain ⟨b0, hb0, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨inv0, hinv0, h⟩ := Option.bind_eq_some_iff.mp h
  obtain rfl : Jet.recipFold a inv0 b0 6 = b := Option.some.inj h
  have h00 : (a.get 0).Mem (constantCoeff φ) := by
    simpa [coeff_zero_eq_constantCoeff_apply] using ha.2 0 (by omega)
  obtain ⟨hne, hm1⟩ := Iv.mem_recip h00 hb0
  obtain ⟨_, hm2⟩ := Iv.mem_recip h00 hinv0
  obtain ⟨hlen, hmem⟩ := Jet.recipFold_mem ha hne hm2 hm1 6 le_rfl
  refine ⟨hne, hlen, fun k hk => ?_⟩
  have := hmem k (by omega)
  exact this


/-! ### Logarithm -/

/-- Recurrence for the coefficients of `logSeries φ`:
`(N+1) ℓ_{N+1} φ₀ = (N+1) φ_{N+1} - Σ_{k<N} (k+1) ℓ_{k+1} φ_{N-k}`. -/
theorem coeff_logSeries_rec (φ : ℝ⟦X⟧) (h0 : constantCoeff φ ≠ 0) (N : ℕ) :
    coeff (N + 1) (logSeries φ) =
      (((N : ℝ) + 1) * coeff (N + 1) φ -
        ∑ k ∈ range N, ((coeff (k + 1) (logSeries φ)) * ((k : ℝ) + 1)) *
          coeff (N + 1 - (k + 1)) φ) / (((N : ℝ) + 1) * constantCoeff φ) := by
  have hD : d⁄dX φ = d⁄dX (logSeries φ) * φ := by
    rw [derivative_logSeries, mul_assoc, PowerSeries.inv_mul_cancel _ h0, mul_one]
  have h := congrArg (coeff N) hD
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, sum_range_succ,
    coeff_derivative] at h
  simp only [coeff_derivative, Nat.sub_self, coeff_zero_eq_constantCoeff_apply] at h
  have hN : ((N : ℝ) + 1) ≠ 0 := by positivity
  have e : ∀ k ∈ range N, coeff (k + 1) (logSeries φ) * ((k : ℝ) + 1) * coeff (N - k) φ =
      coeff (k + 1) (logSeries φ) * ((k : ℝ) + 1) * coeff (N + 1 - (k + 1)) φ := by
    intro k hk
    have hk' : N - k = N + 1 - (k + 1) := by omega
    rw [hk']
  have hsum := Finset.sum_congr (rfl : range N = range N) e
  rw [hsum] at h
  field_simp
  push_cast at h
  linarith

theorem Jet.logFold_mem {a : Jet} {φ : ℝ⟦X⟧} (ha : JMem a φ) (h0 : constantCoeff φ ≠ 0)
    {l0 : Iv} (hl : l0.Mem (Real.log (constantCoeff φ))) :
    ∀ N, N ≤ 6 → ∀ out, Jet.logFold a l0 N = some out → out.length = N + 1 ∧
      ∀ j, j ≤ N → (out.getD j Iv.zero).Mem (coeff j (logSeries φ)) := by
  intro N
  induction N with
  | zero =>
    intro _ out h
    obtain rfl : [l0] = out := Option.some.inj h
    refine ⟨by simp, fun j hj => ?_⟩
    have : j = 0 := by omega
    subst this
    simpa [coeff_logSeries_zero] using hl
  | succ N ih =>
    intro hN out h
    unfold Jet.logFold at h
    obtain ⟨prev, hprev, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨hlen, hmem⟩ := ih (by omega) prev hprev
    unfold Jet.logStep at h
    simp only [hlen, Nat.add_sub_cancel] at h
    obtain ⟨den, hden, rfl⟩ := Option.map_eq_some_iff.mp h
    have h00 : (a.get 0).Mem (constantCoeff φ) := by
      simpa [coeff_zero_eq_constantCoeff_apply] using ha.2 0 (by omega)
    have hs : ((List.range N).foldl
        (fun acc k0 => acc.add (((prev.getD (k0 + 1) Iv.zero).mul (Iv.ofInt (k0 + 1))).mul
          (a.get (N + 1 - (k0 + 1))))) Iv.zero).Mem
        (∑ k ∈ range N, ((coeff (k + 1) (logSeries φ)) * ((k : ℝ) + 1)) *
          coeff (N + 1 - (k + 1)) φ) := by
      refine foldl_range_mem fun k hk => Iv.mem_mul (Iv.mem_mul (hmem (k + 1) (by omega)) ?_)
        (ha.2 (N + 1 - (k + 1)) (by omega))
      have := Iv.mem_ofInt ((k : ℤ) + 1)
      push_cast at this
      exact this
    have hnum := Iv.mem_add (Iv.mem_mul (ha.2 (N + 1) (by omega)) (Iv.mem_ofInt ((N + 1 : ℕ) : ℤ)))
      (Iv.mem_neg hs)
    have hdenm : (((a.get 0).mul (Iv.ofInt ((N + 1 : ℕ) : ℤ))).Mem
        (constantCoeff φ * (((N + 1 : ℕ) : ℤ) : ℝ))) :=
      Iv.mem_mul h00 (Iv.mem_ofInt _)
    obtain ⟨hne, hdm⟩ := Iv.mem_recip hdenm hden
    have hnew := Iv.mem_mul hnum hdm
    refine ⟨by simp [hlen], fun j hj => ?_⟩
    rcases Nat.lt_or_ge j (N + 1) with hj' | hj'
    · rw [List.getD_append _ _ _ _ (by omega)]
      exact hmem j (by omega)
    · have : j = N + 1 := by omega
      subst this
      rw [List.getD_append_right _ _ _ _ (by omega)]
      simp only [hlen, Nat.sub_self, List.getD_cons_zero]
      rw [coeff_logSeries_rec φ h0 N]
      convert hnew using 1
      push_cast
      ring

theorem JMem.log {a b : Jet} {φ : ℝ⟦X⟧} (ha : JMem a φ) (h : Jet.log a = some b) :
    0 < constantCoeff φ ∧ JMem b (logSeries φ) := by
  unfold Jet.log at h
  obtain ⟨l0, hl0, h⟩ := Option.bind_eq_some_iff.mp h
  have h00 : (a.get 0).Mem (constantCoeff φ) := by
    simpa [coeff_zero_eq_constantCoeff_apply] using ha.2 0 (by omega)
  obtain ⟨hpos, hl⟩ := Iv.log_mem h00 hl0
  obtain ⟨hlen, hmem⟩ := Jet.logFold_mem ha hpos.ne' hl 6 le_rfl b h
  refine ⟨hpos, hlen, fun k hk => ?_⟩
  have := hmem k (by omega)
  simpa [Jet.get] using this


/-! ### Mean-value tightening -/

/-- The interval context of a cell `[lo, hi]` encloses the centre, the cell and the radius. -/
structure CtxOK (x : Ctx) (lo hi : ℝ) : Prop where
  center : x.center.Mem ((lo + hi) / 2)
  cell : ∀ t ∈ Set.Icc lo hi, x.cell.Mem t
  rad : ∀ s : ℝ, |s| ≤ (hi - lo) / 2 → x.rad.Mem s

theorem tightGo_mem {x : Ctx} {lo hi : ℝ} (hx : CtxOK x lo hi) (hlohi : lo ≤ hi)
    {A : ℝ → ℝ⟦X⟧} (hA : Coh (Set.Icc lo hi) A) {mid box : Jet}
    (hmid : JMem mid (A ((lo + hi) / 2)))
    (hbox : ∀ t ∈ Set.Icc lo hi, JMem box (A t)) :
    ∀ j, j ≤ 6 → ∀ acc : List Iv, acc.length = 7 - j →
      (∀ t ∈ Set.Icc lo hi, ∀ i, j ≤ i → i ≤ 6 → (acc.getD (i - j) Iv.zero).Mem (coeff i (A t))) →
      ∀ res, CJet.tightGo x mid box j acc = some res → res.length = 7 ∧
        ∀ t ∈ Set.Icc lo hi, ∀ i, i ≤ 6 → (res.getD i Iv.zero).Mem (coeff i (A t)) := by
  intro j
  induction j with
  | zero =>
    intro _ acc hlen hacc res h
    obtain rfl : acc = res := Option.some.inj h
    exact ⟨hlen, fun t ht i hi => by simpa using hacc t ht i (Nat.zero_le _) hi⟩
  | succ j ih =>
    intro hj acc hlen hacc res h
    have hm : (lo + hi) / 2 ∈ Set.Icc lo hi := ⟨by linarith, by linarith⟩
    obtain ⟨a0, rest, rfl⟩ : ∃ a0 rest, acc = a0 :: rest := by
      cases acc with
      | nil => simp at hlen; omega
      | cons a0 rest => exact ⟨a0, rest, rfl⟩
    unfold CJet.tightGo at h
    simp only [List.headD_cons] at h
    obtain ⟨new, hnew, h⟩ := Option.bind_eq_some_iff.mp h
    have hnewmem : ∀ t ∈ Set.Icc lo hi, new.Mem (coeff j (A t)) := by
      intro t ht
      obtain ⟨ξ, hξ, hξe⟩ := hA.mvt hm ht j
      have hbx := (hbox t ht).2 j (by omega)
      have hcand : ((mid.get j).add ((x.rad.mul (Iv.ofInt (j + 1))).mul a0)).Mem
          (coeff j (A t)) := by
        have h1 := hmid.2 j (by omega)
        have h2 : x.rad.Mem (t - (lo + hi) / 2) := by
          apply hx.rad
          rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
        have h3 : (Iv.ofInt ((j : ℤ) + 1)).Mem ((j : ℝ) + 1) := by
          have := Iv.mem_ofInt ((j : ℤ) + 1)
          push_cast at this
          exact this
        have h4 : a0.Mem (coeff (j + 1) (A ξ)) := by
          simpa using hacc ξ hξ (j + 1) le_rfl (by omega)
        have := Iv.mem_add h1 (Iv.mem_mul (Iv.mem_mul h2 h3) h4)
        convert this using 1
        linarith
      exact Iv.mem_meet hbx hcand hnew
    have hacc' : ∀ t ∈ Set.Icc lo hi, ∀ i, j ≤ i → i ≤ 6 →
        ((new :: a0 :: rest).getD (i - j) Iv.zero).Mem (coeff i (A t)) := by
      intro t ht i hji hi6
      rcases Nat.eq_or_lt_of_le hji with e | e
      · subst e; simpa using hnewmem t ht
      · have : i - j = (i - (j + 1)) + 1 := by omega
        rw [this, List.getD_cons_succ]
        exact hacc t ht i (by omega) hi6
    exact ih (by omega) (new :: a0 :: rest) (by simp at hlen ⊢; omega) hacc' res h

theorem tight_mem {x : Ctx} {lo hi : ℝ} (hx : CtxOK x lo hi) (hlohi : lo ≤ hi)
    {A : ℝ → ℝ⟦X⟧} (hA : Coh (Set.Icc lo hi) A) {mid box b : Jet}
    (hmid : JMem mid (A ((lo + hi) / 2)))
    (hbox : ∀ t ∈ Set.Icc lo hi, JMem box (A t)) (h : CJet.tight x mid box = some b)
    (t : ℝ) (ht : t ∈ Set.Icc lo hi) : JMem b (A t) := by
  unfold CJet.tight at h
  obtain ⟨hlen, hres⟩ := tightGo_mem hx hlohi hA hmid hbox 6 le_rfl [box.get 6] (by simp)
    (fun t ht i h1 h2 => by
      have : i = 6 := by omega
      subst this
      simpa [Jet.get] using (hbox t ht).2 6 (by omega)) b h
  exact ⟨hlen, fun k hk => by simpa [Jet.get] using hres t ht k (by omega)⟩

theorem build_mem {x : Ctx} {lo hi : ℝ} (hx : CtxOK x lo hi) (hlohi : lo ≤ hi)
    {A : ℝ → ℝ⟦X⟧} (hA : Coh (Set.Icc lo hi) A) {mid box : Jet} {r : CJet}
    (hmid : JMem mid (A ((lo + hi) / 2)))
    (hbox : ∀ t ∈ Set.Icc lo hi, JMem box (A t)) (h : CJet.build x mid box = some r) :
    r.mid = mid ∧ ∀ t ∈ Set.Icc lo hi, JMem r.box (A t) := by
  unfold CJet.build at h
  obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.mp h
  obtain rfl : (⟨mid, b⟩ : CJet) = r := Option.some.inj h
  exact ⟨rfl, fun t ht => tight_mem hx hlohi hA hmid hbox hb t ht⟩

end BecknerOnofri.V2.Interval
