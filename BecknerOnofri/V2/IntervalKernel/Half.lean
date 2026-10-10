module

public import BecknerOnofri.V2.IntervalKernel.Mul

@[expose] public section

/-!
# Half-registers: the packed form of one jet (7 intervals, 14 fields)

`buildHalf` assembles the 7 entries of a jet from an entry function; the specification lemma
`buildHalf_spec` says that if each entry is correct (reflects the intended `Iv`) then so is the
packed result.  The Cauchy product, termwise sum, negation and scalar multiplication of jets are
instances.
-/

namespace BecknerOnofri.V2.IntervalKernel

open BecknerOnofri.V2.Interval

/-! ### Spec-level readers -/

/-- The interval stored in positions `i, i+1` of a field list. -/
def ivL (l : List Nat) (i : Nat) : Iv := ⟨dec (l.getD i 0), dec (l.getD (i + 1) 0)⟩

/-- The jet stored at offset `base` of a field list. -/
def jetL (l : List Nat) (base : Nat) : Jet := (List.range 7).map fun k => ivL l (base + 2 * k)

theorem jetL_get (l : List Nat) (base k : Nat) (hk : k < 7) :
    (jetL l base).get k = ivL l (base + 2 * k) := by
  unfold jetL Jet.get
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]
  rfl

theorem jetL_length (l : List Nat) (base : Nat) : (jetL l base).length = 7 := by
  simp [jetL]

/-- `Jet.add` of two jets of length 7 is the entrywise sum. -/
theorem jet_add_eq (A B : Jet) (hA : A.length = 7) (hB : B.length = 7) :
    Jet.add A B = (List.range 7).map fun n => (A.get n).add (B.get n) := by
  unfold Jet.add
  apply List.ext_getElem
  · simp [hA, hB]
  · intro n h1 h2
    have hn : n < 7 := by simpa [hA, hB] using h1
    simp only [List.getElem_zipWith, List.getElem_map, List.getElem_range]
    unfold Jet.get
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)]
    rfl

theorem jet_neg_eq (A : Jet) (hA : A.length = 7) :
    Jet.neg A = (List.range 7).map fun n => (A.get n).neg := by
  unfold Jet.neg
  apply List.ext_getElem
  · simp [hA]
  · intro n h1 h2
    have hn : n < 7 := by simpa [hA] using h1
    simp only [List.getElem_map, List.getElem_range]
    unfold Jet.get
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    rfl

theorem jet_smul_eq (A : Jet) (c : Iv) (hA : A.length = 7) :
    Jet.smul A c = (List.range 7).map fun n => (A.get n).mul c := by
  unfold Jet.smul
  apply List.ext_getElem
  · simp [hA]
  · intro n h1 h2
    have hn : n < 7 := by simpa [hA] using h1
    simp only [List.getElem_map, List.getElem_range]
    unfold Jet.get
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    rfl

theorem jet_mul_length (A B : Jet) : (Jet.mul A B).length = 7 := by simp [Jet.mul]

/-! ### Assembling a half -/

/-- The fourteen fields of the seven entries `(lo, hi, ok)` produced by `e`. -/
def halfFields (e : Nat → Nat × Nat × Bool) : List Nat :=
  [(e 0).1, (e 0).2.1, (e 1).1, (e 1).2.1, (e 2).1, (e 2).2.1, (e 3).1, (e 3).2.1,
    (e 4).1, (e 4).2.1, (e 5).1, (e 5).2.1, (e 6).1, (e 6).2.1]

/-- The conjunction of the seven `ok` flags. -/
def halfOk (e : Nat → Nat × Nat × Bool) : Bool :=
  (e 0).2.2 && (e 1).2.2 && (e 2).2.2 && (e 3).2.2 && (e 4).2.2 && (e 5).2.2 && (e 6).2.2

/-- Pack the seven entries `(lo, hi, ok)` produced by `e`. -/
def buildHalf (e : Nat → Nat × Nat × Bool) : Nat × Bool :=
  let e0 := e 0
  let e1 := e 1
  let e2 := e 2
  let e3 := e 3
  let e4 := e 4
  let e5 := e 5
  let e6 := e 6
  (packList [e0.1, e0.2.1, e1.1, e1.2.1, e2.1, e2.2.1, e3.1, e3.2.1, e4.1, e4.2.1, e5.1,
      e5.2.1, e6.1, e6.2.1],
    e0.2.2 && e1.2.2 && e2.2.2 && e3.2.2 && e4.2.2 && e5.2.2 && e6.2.2)

theorem buildHalf_fst (e : Nat → Nat × Nat × Bool) : (buildHalf e).1 = packList (halfFields e) := by
  simp only [buildHalf, halfFields]

theorem buildHalf_snd (e : Nat → Nat × Nat × Bool) : (buildHalf e).2 = halfOk e := by
  simp only [buildHalf, halfOk]

/-- A packed half with field list `l`. -/
def HalfL (h : Nat) (l : List Nat) : Prop := l.length = 14 ∧ (∀ x ∈ l, x ≤ TWOB) ∧ h = packList l

theorem buildHalf_spec (e : Nat → Nat × Nat × Bool) (T : Nat → Iv)
    (h : ∀ n, n < 7 → (e n).2.2 = true →
      (e n).1 ≤ TWOB ∧ (e n).2.1 ≤ TWOB ∧ (⟨dec (e n).1, dec (e n).2.1⟩ : Iv) = T n)
    (hok : (buildHalf e).2 = true) :
    HalfL (buildHalf e).1 (halfFields e) ∧ jetL (halfFields e) 0 = (List.range 7).map T := by
  rw [buildHalf_snd] at hok
  unfold halfOk at hok
  simp only [Bool.and_eq_true] at hok
  obtain ⟨⟨⟨⟨⟨⟨o0, o1⟩, o2⟩, o3⟩, o4⟩, o5⟩, o6⟩ := hok
  obtain ⟨a0, b0, c0⟩ := h 0 (by norm_num) o0
  obtain ⟨a1, b1, c1⟩ := h 1 (by norm_num) o1
  obtain ⟨a2, b2, c2⟩ := h 2 (by norm_num) o2
  obtain ⟨a3, b3, c3⟩ := h 3 (by norm_num) o3
  obtain ⟨a4, b4, c4⟩ := h 4 (by norm_num) o4
  obtain ⟨a5, b5, c5⟩ := h 5 (by norm_num) o5
  obtain ⟨a6, b6, c6⟩ := h 6 (by norm_num) o6
  refine ⟨⟨by simp [halfFields], ?_, buildHalf_fst e⟩, ?_⟩
  · intro x hx
    simp only [halfFields, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      assumption
  · simp only [jetL, ivL, halfFields, List.range_succ, List.range_zero, List.nil_append,
      List.map_cons, List.map_nil, List.map_append, List.getD_cons_zero, List.getD_cons_succ,
      Nat.reduceAdd, Nat.reduceMul, c0, c1, c2, c3, c4, c5, c6]

/-! ### Rebiasing of sums of products -/

/-- `s + B - cnt * C0`: the biased value of a sum `s` of `cnt` terms biased by `C0`. -/
def rebias (s cnt : Nat) : Nat := Nat.sub (Nat.add s B) (Nat.mul cnt C0)

def rebiasOk (s cnt : Nat) : Bool :=
  Nat.ble (Nat.mul cnt C0) (Nat.add s B) && Nat.ble (rebias s cnt) TWOB

theorem rebias_spec {s cnt : Nat} (h : rebiasOk s cnt = true) :
    rebias s cnt ≤ TWOB ∧ dec (rebias s cnt) = (s : Int) - (cnt : Int) * C0 := by
  unfold rebiasOk at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  have h1' := ble_iff.1 h1
  have h2' := ble_iff.1 h2
  refine ⟨h2', ?_⟩
  unfold rebias at h2' ⊢
  simp only [Nat.sub_eq, Nat.add_eq, Nat.mul_eq] at h1' h2' ⊢
  unfold dec
  rw [Nat.cast_sub h1']
  push_cast
  ring

theorem fld_le {l : List Nat} (hl : ∀ x ∈ l, x ≤ TWOB) (i : Nat) :
    fld (packList l) i ≤ TWOB := by
  have h256 : ∀ x ∈ l, x < TWO256 := fun x hx => lt_of_le_of_lt (hl x hx) (by
    rw [TWOB_eq, B_eq, TWO256_eq]; norm_num)
  rw [fld_packList l i h256]
  by_cases hi : i < l.length
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    exact hl _ (List.getElem_mem hi)
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    simp

theorem fld_lt {l : List Nat} (hl : ∀ x ∈ l, x ≤ TWOB) (i : Nat) :
    fld (packList l) i = l.getD i 0 := by
  apply fld_packList
  intro x hx
  exact lt_of_le_of_lt (hl x hx) (by rw [TWOB_eq, B_eq, TWO256_eq]; norm_num)

/-! ### Cauchy product -/

/-- The sum of the first `m` terms of the Cauchy sum for output `n` (rounded products,
biased by `C0` each). -/
def cauchyS (a b base n : Nat) : Nat → Nat × Nat
  | 0 => (0, 0)
  | m + 1 =>
    let acc := cauchyS a b base n m
    let t := fmul (fld a (base + 2 * m)) (fld a (base + 2 * m + 1))
      (fld b (base + 2 * (n - m))) (fld b (base + 2 * (n - m) + 1))
    (Nat.add acc.1 t.1, Nat.add acc.2 t.2)

/-- The entry `n` of the Cauchy product. -/
def cauchyE (a b base n : Nat) : Nat × Nat × Bool :=
  let s := cauchyS a b base n (Nat.add n 1)
  (rebias s.1 (Nat.add n 1), rebias s.2 (Nat.add n 1),
    rebiasOk s.1 (Nat.add n 1) && rebiasOk s.2 (Nat.add n 1))

def mulHalf (a b base : Nat) : Nat × Bool := buildHalf (cauchyE a b base)

/-- The sum of the first `m` rounded products, at the spec level. -/
def cauchyF (A B : Jet) (n : Nat) (m : Nat) : Iv :=
  (List.range m).foldl (fun acc k => acc.add ((A.get k).mul (B.get (n - k)))) Iv.zero

theorem cauchyS_spec {la lb : List Nat} (hla : ∀ x ∈ la, x ≤ TWOB) (hlb : ∀ x ∈ lb, x ≤ TWOB)
    (base n : Nat) (hn : n ≤ 6) :
    ∀ m, m ≤ n + 1 →
      (((cauchyS (packList la) (packList lb) base n m).1 : Nat) : Int)
          = (cauchyF (jetL la base) (jetL lb base) n m).lo + (m : Int) * C0 ∧
      (((cauchyS (packList la) (packList lb) base n m).2 : Nat) : Int)
          = (cauchyF (jetL la base) (jetL lb base) n m).hi + (m : Int) * C0 := by
  intro m
  induction m with
  | zero =>
    intro _
    simp [cauchyS, cauchyF, Iv.zero]
  | succ m ih =>
    intro hm
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    have hk : m < 7 := by omega
    have hnk : n - m < 7 := by omega
    have e1 := fld_lt hla (base + 2 * m)
    have e2 := fld_lt hla (base + 2 * m + 1)
    have e3 := fld_lt hlb (base + 2 * (n - m))
    have e4 := fld_lt hlb (base + 2 * (n - m) + 1)
    have f1 := fld_le hla (base + 2 * m)
    have f2 := fld_le hla (base + 2 * m + 1)
    have f3 := fld_le hlb (base + 2 * (n - m))
    have f4 := fld_le hlb (base + 2 * (n - m) + 1)
    obtain ⟨s1, s2⟩ := fmul_spec f1 f2 f3 f4
    have hA : (jetL la base).get m = ⟨dec (fld (packList la) (base + 2 * m)),
        dec (fld (packList la) (base + 2 * m + 1))⟩ := by
      rw [jetL_get _ _ _ hk, e1, e2]; rfl
    have hB : (jetL lb base).get (n - m) = ⟨dec (fld (packList lb) (base + 2 * (n - m))),
        dec (fld (packList lb) (base + 2 * (n - m) + 1))⟩ := by
      rw [jetL_get _ _ _ hnk, e3, e4]; rfl
    have hF : cauchyF (jetL la base) (jetL lb base) n (m + 1)
        = (cauchyF (jetL la base) (jetL lb base) n m).add
          ((((jetL la base).get m)).mul ((jetL lb base).get (n - m))) := by
      unfold cauchyF
      rw [List.range_succ, List.foldl_append]
      rfl
    rw [hF, hA, hB]
    simp only [cauchyS, Nat.add_eq, Iv.add]
    push_cast
    rw [ih1, ih2, s1, s2]
    constructor <;> ring

theorem cauchyE_spec {la lb : List Nat} (hla : ∀ x ∈ la, x ≤ TWOB) (hlb : ∀ x ∈ lb, x ≤ TWOB)
    (base n : Nat) (hn : n ≤ 6)
    (hok : (cauchyE (packList la) (packList lb) base n).2.2 = true) :
    (cauchyE (packList la) (packList lb) base n).1 ≤ TWOB ∧
    (cauchyE (packList la) (packList lb) base n).2.1 ≤ TWOB ∧
    (⟨dec (cauchyE (packList la) (packList lb) base n).1,
      dec (cauchyE (packList la) (packList lb) base n).2.1⟩ : Iv)
      = cauchyF (jetL la base) (jetL lb base) n (n + 1) := by
  obtain ⟨c1, c2⟩ := cauchyS_spec hla hlb base n hn (n + 1) le_rfl
  unfold cauchyE at hok ⊢
  simp only [Bool.and_eq_true] at hok
  obtain ⟨r1, r2⟩ := hok
  obtain ⟨r1a, r1b⟩ := rebias_spec r1
  obtain ⟨r2a, r2b⟩ := rebias_spec r2
  refine ⟨r1a, r2a, ?_⟩
  simp only [Nat.add_eq] at *
  have hlo : dec (rebias (cauchyS (packList la) (packList lb) base n (n + 1)).1 (n + 1))
      = (cauchyF (jetL la base) (jetL lb base) n (n + 1)).lo := by
    rw [r1b, c1]; push_cast; ring
  have hhi : dec (rebias (cauchyS (packList la) (packList lb) base n (n + 1)).2 (n + 1))
      = (cauchyF (jetL la base) (jetL lb base) n (n + 1)).hi := by
    rw [r2b, c2]; push_cast; ring
  rw [hlo, hhi]

theorem mulHalf_spec {la lb : List Nat} (hla : ∀ x ∈ la, x ≤ TWOB) (hlb : ∀ x ∈ lb, x ≤ TWOB)
    (base : Nat)
    (hok : (mulHalf (packList la) (packList lb) base).2 = true) :
    ∃ l, HalfL (mulHalf (packList la) (packList lb) base).1 l ∧
      jetL l 0 = Jet.mul (jetL la base) (jetL lb base) := by
  have := buildHalf_spec (cauchyE (packList la) (packList lb) base)
    (fun n => cauchyF (jetL la base) (jetL lb base) n (n + 1))
    (fun n hn hok => cauchyE_spec hla hlb base n (by omega) hok) hok
  exact ⟨_, this.1, this.2⟩

/-! ### Termwise operations -/

/-- Sum of two biased intervals. -/
def addF (al ah bl bh : Nat) : Nat × Nat × Bool :=
  let sl := Nat.add al bl
  let sh := Nat.add ah bh
  (Nat.sub sl B, Nat.sub sh B,
    Nat.ble B sl && Nat.ble B sh && Nat.ble (Nat.sub sl B) TWOB && Nat.ble (Nat.sub sh B) TWOB)

theorem addF_spec {al ah bl bh : Nat} (hok : (addF al ah bl bh).2.2 = true) :
    (addF al ah bl bh).1 ≤ TWOB ∧ (addF al ah bl bh).2.1 ≤ TWOB ∧
    (⟨dec (addF al ah bl bh).1, dec (addF al ah bl bh).2.1⟩ : Iv)
      = Iv.add ⟨dec al, dec ah⟩ ⟨dec bl, dec bh⟩ := by
  unfold addF at hok ⊢
  simp only [Bool.and_eq_true, ble_iff, Nat.add_eq, Nat.sub_eq] at hok ⊢
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hok
  refine ⟨h3, h4, ?_⟩
  unfold dec Iv.add
  simp only [Iv.mk.injEq]
  constructor <;> omega

def addE (a b base n : Nat) : Nat × Nat × Bool :=
  addF (fld a (base + 2 * n)) (fld a (base + 2 * n + 1)) (fld b (base + 2 * n))
    (fld b (base + 2 * n + 1))

def addHalf (a b base : Nat) : Nat × Bool := buildHalf (addE a b base)

theorem ivL_pack {l : List Nat} (hl : ∀ x ∈ l, x ≤ TWOB) (i : Nat) :
    ivL l i = ⟨dec (fld (packList l) i), dec (fld (packList l) (i + 1))⟩ := by
  rw [fld_lt hl, fld_lt hl]; rfl

theorem addHalf_spec {la lb : List Nat} (hla : ∀ x ∈ la, x ≤ TWOB) (hlb : ∀ x ∈ lb, x ≤ TWOB)
    (base : Nat) (hok : (addHalf (packList la) (packList lb) base).2 = true) :
    ∃ l, HalfL (addHalf (packList la) (packList lb) base).1 l ∧
      jetL l 0 = Jet.add (jetL la base) (jetL lb base) := by
  rw [jet_add_eq _ _ (jetL_length _ _) (jetL_length _ _)]
  have := buildHalf_spec (addE (packList la) (packList lb) base)
    (fun n => (ivL la (base + 2 * n)).add (ivL lb (base + 2 * n)))
    (fun n hn hok => by
      have := addF_spec hok
      refine ⟨this.1, this.2.1, ?_⟩
      rw [ivL_pack hla, ivL_pack hlb]
      exact this.2.2) hok
  refine ⟨_, this.1, ?_⟩
  rw [this.2]
  apply List.map_congr_left
  intro n hn
  have hn' : n < 7 := List.mem_range.1 hn
  rw [jetL_get _ _ _ hn', jetL_get _ _ _ hn']

/-- Negation of a biased interval. -/
def negF (al ah : Nat) : Nat × Nat × Bool :=
  (Nat.sub TWOB ah, Nat.sub TWOB al, Nat.ble ah TWOB && Nat.ble al TWOB)

theorem negF_spec {al ah : Nat} (hok : (negF al ah).2.2 = true) :
    (negF al ah).1 ≤ TWOB ∧ (negF al ah).2.1 ≤ TWOB ∧
    (⟨dec (negF al ah).1, dec (negF al ah).2.1⟩ : Iv) = Iv.neg ⟨dec al, dec ah⟩ := by
  have e : TWOB = 2 * B := TWOB_eq
  unfold negF at hok ⊢
  simp only [Bool.and_eq_true, ble_iff, Nat.sub_eq] at hok ⊢
  obtain ⟨h1, h2⟩ := hok
  refine ⟨Nat.sub_le _ _, Nat.sub_le _ _, ?_⟩
  unfold dec Iv.neg
  simp only [Iv.mk.injEq]
  constructor <;> omega

def negE (a base n : Nat) : Nat × Nat × Bool :=
  negF (fld a (base + 2 * n)) (fld a (base + 2 * n + 1))

def negHalf (a base : Nat) : Nat × Bool := buildHalf (negE a base)

theorem negHalf_spec {la : List Nat} (hla : ∀ x ∈ la, x ≤ TWOB) (base : Nat)
    (hok : (negHalf (packList la) base).2 = true) :
    ∃ l, HalfL (negHalf (packList la) base).1 l ∧ jetL l 0 = Jet.neg (jetL la base) := by
  rw [jet_neg_eq _ (jetL_length _ _)]
  have := buildHalf_spec (negE (packList la) base)
    (fun n => (ivL la (base + 2 * n)).neg)
    (fun n hn hok => by
      have := negF_spec hok
      refine ⟨this.1, this.2.1, ?_⟩
      rw [ivL_pack hla]
      exact this.2.2) hok
  refine ⟨_, this.1, ?_⟩
  rw [this.2]
  apply List.map_congr_left
  intro n hn
  have hn' : n < 7 := List.mem_range.1 hn
  rw [jetL_get _ _ _ hn']

/-- Product of a biased interval with a constant (as in `Iv.mul`), rebiased. -/
def smulF (al ah cl ch : Nat) : Nat × Nat × Bool :=
  let t := fmul al ah cl ch
  (rebias t.1 1, rebias t.2 1, rebiasOk t.1 1 && rebiasOk t.2 1)

theorem smulF_spec {al ah cl ch : Nat} (h1 : al ≤ TWOB) (h2 : ah ≤ TWOB) (h3 : cl ≤ TWOB)
    (h4 : ch ≤ TWOB) (hok : (smulF al ah cl ch).2.2 = true) :
    (smulF al ah cl ch).1 ≤ TWOB ∧ (smulF al ah cl ch).2.1 ≤ TWOB ∧
    (⟨dec (smulF al ah cl ch).1, dec (smulF al ah cl ch).2.1⟩ : Iv)
      = Iv.mul ⟨dec al, dec ah⟩ ⟨dec cl, dec ch⟩ := by
  obtain ⟨s1, s2⟩ := fmul_spec h1 h2 h3 h4
  simp only [smulF] at hok ⊢
  simp only [Bool.and_eq_true] at hok
  obtain ⟨r1, r2⟩ := hok
  obtain ⟨r1a, r1b⟩ := rebias_spec r1
  obtain ⟨r2a, r2b⟩ := rebias_spec r2
  have hlo : dec (rebias (fmul al ah cl ch).1 1) = (Iv.mul ⟨dec al, dec ah⟩ ⟨dec cl, dec ch⟩).lo := by
    rw [r1b, s1]; push_cast; ring
  have hhi : dec (rebias (fmul al ah cl ch).2 1) = (Iv.mul ⟨dec al, dec ah⟩ ⟨dec cl, dec ch⟩).hi := by
    rw [r2b, s2]; push_cast; ring
  exact ⟨r1a, r2a, by rw [hlo, hhi]⟩

def smulE (a base cl ch n : Nat) : Nat × Nat × Bool :=
  smulF (fld a (base + 2 * n)) (fld a (base + 2 * n + 1)) cl ch

def smulHalf (a base cl ch : Nat) : Nat × Bool := buildHalf (smulE a base cl ch)

theorem smulHalf_spec {la : List Nat} (hla : ∀ x ∈ la, x ≤ TWOB) (base : Nat) {cl ch : Nat}
    (hcl : cl ≤ TWOB) (hch : ch ≤ TWOB)
    (hok : (smulHalf (packList la) base cl ch).2 = true) :
    ∃ l, HalfL (smulHalf (packList la) base cl ch).1 l ∧
      jetL l 0 = Jet.smul (jetL la base) ⟨dec cl, dec ch⟩ := by
  rw [jet_smul_eq _ _ (jetL_length _ _)]
  have := buildHalf_spec (smulE (packList la) base cl ch)
    (fun n => (ivL la (base + 2 * n)).mul ⟨dec cl, dec ch⟩)
    (fun n hn hok => by
      have := smulF_spec (fld_le hla _) (fld_le hla _) hcl hch hok
      refine ⟨this.1, this.2.1, ?_⟩
      rw [ivL_pack hla]
      exact this.2.2) hok
  refine ⟨_, this.1, ?_⟩
  rw [this.2]
  apply List.map_congr_left
  intro n hn
  have hn' : n < 7 := List.mem_range.1 hn
  rw [jetL_get _ _ _ hn']

/-- Adding the constant jet `c` (entry `0` is `c`, the others are zero). -/
def addcE (a base cl ch n : Nat) : Nat × Nat × Bool :=
  addF (fld a (base + 2 * n)) (fld a (base + 2 * n + 1))
    (bif Nat.beq n 0 then cl else B) (bif Nat.beq n 0 then ch else B)

def addcHalf (a base cl ch : Nat) : Nat × Bool := buildHalf (addcE a base cl ch)

theorem dec_B : dec B = 0 := by unfold dec; simp

theorem jetConst_get (c : Iv) (n : Nat) (hn : n < 7) :
    (Jet.const c).get n = if n = 0 then c else Iv.zero := by
  unfold Jet.const Jet.get
  rcases n with _ | n
  · simp
  · rw [List.getD_cons_succ]
    have : n < 6 := by omega
    simp only [List.replicate, List.getD_eq_getElem?_getD]
    interval_cases n <;> rfl

theorem addcHalf_spec {la : List Nat} (hla : ∀ x ∈ la, x ≤ TWOB) (base : Nat) {cl ch : Nat}
    (hok : (addcHalf (packList la) base cl ch).2 = true) :
    ∃ l, HalfL (addcHalf (packList la) base cl ch).1 l ∧
      jetL l 0 = Jet.add (jetL la base) (Jet.const ⟨dec cl, dec ch⟩) := by
  have hlen : (Jet.const ⟨dec cl, dec ch⟩).length = 7 := by simp [Jet.const]
  rw [jet_add_eq _ _ (jetL_length _ _) hlen]
  have := buildHalf_spec (addcE (packList la) base cl ch)
    (fun n => (ivL la (base + 2 * n)).add ((Jet.const ⟨dec cl, dec ch⟩).get n))
    (fun n hn hok => by
      unfold addcE at hok ⊢
      have := addF_spec hok
      refine ⟨this.1, this.2.1, ?_⟩
      rw [jetConst_get _ _ hn, ivL_pack hla]
      rw [this.2.2]
      rcases Nat.eq_zero_or_pos n with rfl | hpos
      · simp
      · have : Nat.beq n 0 = false := by
          cases h : Nat.beq n 0
          · rfl
          · exact absurd (Nat.eq_of_beq_eq_true h) (by omega)
        simp only [this, Bool.cond_false]
        have hn0 : n ≠ 0 := by omega
        simp only [hn0, ite_false, dec_B]
        rfl) hok
  refine ⟨_, this.1, ?_⟩
  rw [this.2]
  apply List.map_congr_left
  intro n hn
  have hn' : n < 7 := List.mem_range.1 hn
  rw [jetL_get _ _ _ hn']

end BecknerOnofri.V2.IntervalKernel
