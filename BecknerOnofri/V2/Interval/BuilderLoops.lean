module

public import BecknerOnofri.V2.Interval.BuilderSpec
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic

@[expose] public section

/-!
# Specifications of the builder combinators

`powB` (fuel recursion), `sumB` (left fold), `mapR` (indexed `mapM`) and `pochGo` (the Pochhammer
loop of the family), each with a Hoare-style specification in the logic of `BuilderSpec`.
-/

namespace BecknerOnofri.V2.Interval

open Finset

section Loops
variable {t : ℝ}

/-! ### Powers -/

theorem Tr_powB {Γ : List SFact} {a : ℕ} {x : ℝ} (ha : Impl Γ (SFact.has t a x)) :
    ∀ (fuel n : ℕ), n ≤ fuel →
      Tr Γ (powB a fuel n) (fun r => [SFact.has t r (x ^ n)]) := by
  intro fuel
  induction fuel generalizing Γ with
  | zero =>
    intro n hn
    have : n = 0 := by omega
    subst this
    rw [powB]
    exact Tr_val Tr_cst (by simp)
  | succ fuel ih =>
    intro n hn
    rw [powB]
    refine Tr_ite (fun h0 => ?_) (fun h0 => ?_)
    · subst h0
      exact Tr_val Tr_cst (by simp)
    · refine Tr_ite (fun h2 => ?_) (fun h2 => ?_)
      · refine Tr_bind (ih ha (n / 2) (by omega)) (fun b => ?_)
        refine Tr_val (Tr_mulB (x := x ^ (n / 2)) (y := x ^ (n / 2)) (Impl.of_mem (by mem))
          (Impl.of_mem (by mem))) ?_
        rw [← pow_add]
        congr 1
        omega
      · refine Tr_bind (ih ha (n - 1) (by omega)) (fun b => ?_)
        refine Tr_val (Tr_mulB (x := x) (y := x ^ (n - 1)) (ha.weaken _)
          (Impl.of_mem (by mem))) ?_
        rw [← pow_succ']
        congr 1
        omega

/-! ### Sums -/

theorem Tr_foldAdd : ∀ (xs : List ℕ) {Γ : List SFact} (X : ℕ → ℝ) (z : ℕ) (a0 : ℝ),
    Impl Γ (SFact.has t z a0) → Impl Γ (SFact.hasF t xs xs.length X) →
      Tr Γ (xs.foldlM addB z)
        (fun r => [SFact.has t r (a0 + ∑ i ∈ range xs.length, X i)])
  | [], Γ, X, z, a0, hz, _ => by
    refine Tr_pure fun s hs F hF => ?_
    rw [List.mem_singleton] at hF
    subst hF
    have : BSHas t s z a0 := hz s hs
    show BSHas t s z _
    simpa using this
  | x :: xs, Γ, X, z, a0, hz, hxs => by
    have hx : Impl Γ (SFact.has t x (X 0)) := fun s hs => by
      have := (hxs s hs).2 0 (by simp)
      show BSHas t s x (X 0)
      simpa using this
    have hxs' : Impl Γ (SFact.hasF t xs xs.length (fun j => X (j + 1))) := fun s hs => by
      obtain ⟨hl, hh⟩ := hxs s hs
      refine ⟨rfl, fun j hj => ?_⟩
      have := hh (j + 1) (by simp; omega)
      show BSHas t s (xs.getD j 0) (X (j + 1))
      simpa using this
    show Tr Γ (addB z x >>= fun z' => xs.foldlM addB z') _
    refine Tr_bind (Tr_addB hz hx) (fun z' => ?_)
    refine Tr_post (Tr_foldAdd xs (Γ := [SFact.has t z' (a0 + X 0)] ++ Γ) (fun j => X (j + 1)) z'
      (a0 + X 0) (Impl.of_mem (by mem)) (hxs'.weaken _)) ?_
    intro r s hs F hF
    rw [List.mem_singleton] at hF
    subst hF
    have : BSHas t s r (a0 + X 0 + ∑ i ∈ range xs.length, X (i + 1)) :=
      hs _ (List.mem_singleton_self _)
    show BSHas t s r _
    have e : a0 + ∑ i ∈ range (x :: xs).length, X i =
        a0 + X 0 + ∑ i ∈ range xs.length, X (i + 1) := by
      rw [List.length_cons, sum_range_succ' X]; ring
    rw [e]; exact this

theorem Tr_sumB {Γ : List SFact} {xs : List ℕ} {X : ℕ → ℝ} {n : ℕ} (hn : xs.length = n)
    (hxs : Impl Γ (SFact.hasF t xs n X)) :
    Tr Γ (sumB xs) (fun r => [SFact.has t r (∑ i ∈ range n, X i)]) := by
  subst hn
  unfold sumB
  refine Tr_bind (Tr_val (t := t) Tr_cst (show ((0 : Int) : ℝ) / ((1 : Nat) : ℝ) = 0 by simp))
    (fun z => ?_)
  refine Tr_post (Tr_foldAdd xs X z 0 (Impl.of_mem (by mem)) (hxs.weaken _)) ?_
  intro r s hs F hF
  rw [List.mem_singleton] at hF
  subst hF
  have : BSHas t s r (0 + ∑ i ∈ range xs.length, X i) := hs _ (List.mem_singleton_self _)
  show BSHas t s r _
  rwa [zero_add] at this

/-! ### Indexed `mapM` -/

/-- `[body k, body (k+1), …, body (k+m-1)]` as a monadic loop. -/
def mapR {α : Type} (body : ℕ → B α) : ℕ → ℕ → B (List α)
  | _, 0 => pure []
  | k, m + 1 => do
    let b ← body k
    let bs ← mapR body (k + 1) m
    pure (b :: bs)

theorem Tr_mapR {body : ℕ → B ℕ} {X : ℕ → ℝ} (m : ℕ) :
    ∀ (k : ℕ) {Γ : List SFact},
      (∀ j, k ≤ j → j < k + m → Tr Γ (body j) (fun r => [SFact.has t r (X j)])) →
      Tr Γ (mapR body k m) (fun rs => [SFact.hasK t rs k m X]) := by
  induction m with
  | zero =>
    intro k Γ _
    refine Tr_pure fun s hs F hF => ?_
    rw [List.mem_singleton] at hF
    subst hF
    exact ⟨rfl, fun i hi => absurd hi (by omega)⟩
  | succ m ih =>
    intro k Γ h
    show Tr Γ (body k >>= fun b => mapR body (k + 1) m >>= fun bs => pure (b :: bs)) _
    refine Tr_bind (h k le_rfl (by omega)) (fun b => ?_)
    refine Tr_bind (ih (k + 1) (Γ := [SFact.has t b (X k)] ++ Γ) (fun j hj1 hj2 =>
      Tr_ctx (h j (by omega) (by omega)) (fun s hs F hF => hs F (List.mem_append_right _ hF))))
      (fun bs => ?_)
    refine Tr_pure fun s hs F hF => ?_
    rw [List.mem_singleton] at hF
    subst hF
    have h1 : BSHas t s b (X k) := hs (SFact.has t b (X k)) (by simp)
    have h2 := hs _ (List.mem_append_left _ (List.mem_singleton_self _))
    obtain ⟨hl, hh⟩ := h2
    refine ⟨by simp [hl], fun i hi => ?_⟩
    cases i with
    | zero => simpa using h1
    | succ i =>
      have := hh i (by omega)
      have e : k + (i + 1) = k + 1 + i := by omega
      show BSHas t s ((b :: bs).getD (i + 1) 0) (X (k + (i + 1)))
      rw [e]
      simpa using this

theorem Tr_mapM {Γ : List SFact} {body : ℕ → B ℕ} {X : ℕ → ℝ} (n : ℕ)
    (h : ∀ j < n, Tr Γ (body j) (fun r => [SFact.has t r (X j)])) :
    Tr Γ (mapR body 0 n) (fun rs => [SFact.hasF t rs n X]) := by
  refine Tr_post (Tr_mapR n 0 (fun j _ hj => h j (by omega))) ?_
  intro rs s hs F hF
  rw [List.mem_singleton] at hF
  subst hF
  obtain ⟨hl, hh⟩ := hs _ (List.mem_singleton_self _)
  exact ⟨hl, fun j hj => by simpa using hh j hj⟩

/-! ### The Pochhammer loop -/

structure Poch where
  ups : List ℕ
  downs : List ℕ
  den : ℕ

/-- The loop `for k in range 12` of the producer: `ups`/`downs` collect the running products,
`den` the product of `1 + k h`; `lu`, `ld` are the last registers of the two running products. -/
def pochGo (Ap Am h : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ → B Poch
  | 0, _, _, _, den => pure ⟨[], [], den⟩
  | n + 1, k, lu, ld, den => do
    let kh ← smulB h k
    let s1 ← addB Ap kh
    let nu ← mulB lu s1
    let s2 ← addB Am kh
    let nd ← mulB ld s2
    let s3 ← addcB kh 1
    let den' ← mulB den s3
    let r ← pochGo Ap Am h n (k + 1) nu nd den'
    pure ⟨nu :: r.ups, nd :: r.downs, r.den⟩

noncomputable def pochU (a h : ℝ) (k : ℕ) : ℝ := ∏ m ∈ range k, (a + h * m)
noncomputable def pochD (h : ℝ) (k : ℕ) : ℝ := ∏ m ∈ range k, (h * m + 1)

theorem Tr_pochGo {Ap Am h : ℕ} {pA pM hv : ℝ} (n : ℕ) :
    ∀ (k lu ld den : ℕ) {xu xd xn : ℝ} {Γ : List SFact},
      SFact.has t Ap pA ∈ Γ → SFact.has t Am pM ∈ Γ → SFact.has t h hv ∈ Γ →
      SFact.has t lu xu ∈ Γ → SFact.has t ld xd ∈ Γ → SFact.has t den xn ∈ Γ →
      xu = pochU pA hv k → xd = pochU pM hv k → xn = pochD hv k →
      Tr Γ (pochGo Ap Am h n k lu ld den)
        (fun r => [SFact.hasK t r.ups (k + 1) n (pochU pA hv),
                   SFact.hasK t r.downs (k + 1) n (pochU pM hv),
                   SFact.has t r.den (pochD hv (k + n))]) := by
  induction n with
  | zero =>
    intro k lu ld den xu xd xn Γ hA hM hh hu hd hden exu exd exn
    refine Tr_pure fun s hs F hF => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hF
    rcases hF with rfl | rfl | rfl
    · exact ⟨rfl, fun i hi => absurd hi (by omega)⟩
    · exact ⟨rfl, fun i hi => absurd hi (by omega)⟩
    · have : BSHas t s den xn := hs _ hden
      rw [exn] at this
      exact this
  | succ n ih =>
    intro k lu ld den xu xd xn Γ hA hM hh hu hd hden exu exd exn
    rw [pochGo]
    subst exu exd exn
    refine Tr_bind (Tr_smulB (Impl.of_mem hh)) (fun kh => ?_)
    refine Tr_bind (Tr_addB (Impl.of_mem (by mem)) (Impl.of_mem (by mem))) (fun s1 => ?_)
    refine Tr_bind (Tr_val (Tr_mulB (Impl.of_mem (by mem)) (Impl.of_mem (by mem)))
      (show _ = pochU pA hv (k + 1) by simp [pochU, prod_range_succ])) (fun nu => ?_)
    refine Tr_bind (Tr_addB (Impl.of_mem (by mem)) (Impl.of_mem (by mem))) (fun s2 => ?_)
    refine Tr_bind (Tr_val (Tr_mulB (Impl.of_mem (by mem)) (Impl.of_mem (by mem)))
      (show _ = pochU pM hv (k + 1) by simp [pochU, prod_range_succ])) (fun nd => ?_)
    refine Tr_bind (Tr_addcB (Impl.of_mem (by mem))) (fun s3 => ?_)
    refine Tr_bind (Tr_val (Tr_mulB (Impl.of_mem (by mem)) (Impl.of_mem (by mem)))
      (show _ = pochD hv (k + 1) by simp [pochD, prod_range_succ])) (fun den' => ?_)
    refine Tr_bind (ih (k + 1) nu nd den' (by mem) (by mem) (by mem) (by mem) (by mem) (by mem) rfl rfl rfl)
      (fun r => ?_)
    refine Tr_pure fun s hs F hF => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hF
    have hnu : BSHas t s nu (pochU pA hv (k + 1)) :=
      hs (SFact.has t nu (pochU pA hv (k + 1))) (by mem)
    have hnd : BSHas t s nd (pochU pM hv (k + 1)) :=
      hs (SFact.has t nd (pochU pM hv (k + 1))) (by mem)
    rcases hF with rfl | rfl | rfl
    · obtain ⟨hl, hh⟩ := hs (SFact.hasK t r.ups (k + 1 + 1) n (pochU pA hv)) (by mem)
      refine ⟨by simp [hl], fun i hi => ?_⟩
      cases i with
      | zero => simpa using hnu
      | succ i =>
        have := hh i (by omega)
        have e : k + 1 + (i + 1) = k + 1 + 1 + i := by omega
        show BSHas t s ((nu :: r.ups).getD (i + 1) 0) (pochU pA hv (k + 1 + (i + 1)))
        rw [e]; simpa using this
    · obtain ⟨hl, hh⟩ := hs (SFact.hasK t r.downs (k + 1 + 1) n (pochU pM hv)) (by mem)
      refine ⟨by simp [hl], fun i hi => ?_⟩
      cases i with
      | zero => simpa using hnd
      | succ i =>
        have := hh i (by omega)
        have e : k + 1 + (i + 1) = k + 1 + 1 + i := by omega
        show BSHas t s ((nd :: r.downs).getD (i + 1) 0) (pochU pM hv (k + 1 + (i + 1)))
        rw [e]; simpa using this
    · have := hs (SFact.has t r.den (pochD hv (k + 1 + n))) (by mem)
      have e : k + 1 + n = k + (n + 1) := by omega
      rw [e] at this
      exact this


end Loops

end BecknerOnofri.V2.Interval

namespace BecknerOnofri.V2.Interval

theorem choose_eq (n k : ℕ) : choose n k = Nat.choose n k := by
  induction n generalizing k with
  | zero => cases k <;> simp [choose]
  | succ n ih =>
    cases k with
    | zero => simp [choose]
    | succ k => rw [choose, ih, ih, Nat.choose_succ_succ]

theorem Tr_fact {Γ : List SFact} {α : Type} {m : B α} {Q : α → List SFact} (F : SFact)
    (hF : Impl Γ F) (h : Tr (F :: Γ) m Q) : Tr Γ m Q := by
  intro s w hs
  refine h s w (fun G hG => ?_)
  rcases List.mem_cons.1 hG with rfl | hG
  · exact hF s hs
  · exact hs G hG

theorem Impl.getF {t : ℝ} {Γ : List SFact} {rs : List ℕ} {n : ℕ} {X : ℕ → ℝ} {j : ℕ} (d : ℕ)
    (h : Impl Γ (SFact.hasF t rs n X)) (hj : j < n) :
    Impl Γ (SFact.has t (rs.getD j d) (X j)) := fun s hs => by
  obtain ⟨hl, hh⟩ := h s hs
  have := hh j hj
  show BSHas t s (rs.getD j d) (X j)
  have e : rs.getD j d = rs.getD j 0 := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by omega : j < rs.length)]
    rfl
  rw [e]; exact this

theorem Impl.hasF_cons {t : ℝ} {Γ : List SFact} {c : ℕ} {rs : List ℕ} {n : ℕ} {X : ℕ → ℝ} {x : ℝ}
    (hc : Impl Γ (SFact.has t c x)) (hx : x = X 0) (hr : Impl Γ (SFact.hasK t rs 1 n X)) :
    Impl Γ (SFact.hasF t (c :: rs) (n + 1) X) := fun s hs => by
  have h1 : BSHas t s c x := hc s hs
  obtain ⟨hl, hh⟩ := hr s hs
  refine ⟨by simp [hl], fun j hj => ?_⟩
  cases j with
  | zero => rw [hx] at h1; simpa using h1
  | succ j =>
    have := hh j (by omega)
    have e : 1 + j = j + 1 := by omega
    rw [e] at this
    simpa using this

end BecknerOnofri.V2.Interval

namespace BecknerOnofri.V2.Interval

theorem Tr_sumB' {t : ℝ} {Γ : List SFact} {xs : List ℕ} {X : ℕ → ℝ} {n : ℕ}
    (hxs : Impl Γ (SFact.hasF t xs n X)) :
    Tr Γ (sumB xs) (fun r => [SFact.has t r (∑ i ∈ Finset.range n, X i)]) := by
  intro s w hs
  exact Tr_sumB (hxs s hs).1 hxs s w hs

end BecknerOnofri.V2.Interval
