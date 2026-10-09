module

public import BecknerOnofri.V2.Interval.ProgSound

@[expose] public section

/-!
# Hoare-style specification of the program builder

The builder monad `B = StateM BS` appends one `Op` per primitive.  We give a *monotone-fact*
Hoare logic for it: a context `Γ : List SFact` of facts (each persistent under extension of the
builder state) and a triple `Tr Γ m Q`: running `m` from any well-formed state satisfying `Γ`
yields a well-formed extension of the state satisfying the new facts `Q result`.  The semantic
content of a fact is about the *real values* `semRun t ops` of the registers, so a proof about a
builder computation yields the values of its registers for every real `t`, with no domain
hypotheses (`⁻¹` and `Real.log` are total).
-/

namespace BecknerOnofri.V2.Interval

/-! ### Value lists -/

theorem semFold_append (t : ℝ) (p q : Prog) (v : List ℝ) :
    semFold t (p ++ q) v = semFold t q (semFold t p v) := by
  simp only [semFold, List.foldl_append]

theorem semFold_cons (t : ℝ) (o : Op) (p : Prog) (v : List ℝ) :
    semFold t (o :: p) v = semFold t p (v ++ [semStep t v o]) := rfl

theorem semFold_nil (t : ℝ) (v : List ℝ) : semFold t [] v = v := rfl

theorem semFold_length (t : ℝ) (p : Prog) (v : List ℝ) :
    (semFold t p v).length = v.length + p.length := by
  induction p generalizing v with
  | nil => rfl
  | cons o p ih => rw [semFold_cons, ih]; simp; omega

theorem semFold_prefix (t : ℝ) (p : Prog) (v : List ℝ) : ∃ r, semFold t p v = v ++ r := by
  induction p generalizing v with
  | nil => exact ⟨[], by simp [semFold_nil]⟩
  | cons o p ih =>
    obtain ⟨r, hr⟩ := ih (v ++ [semStep t v o])
    exact ⟨[semStep t v o] ++ r, by rw [semFold_cons, hr]; simp⟩

/-- Register values of a builder state. -/
noncomputable def bsVals (t : ℝ) (s : BS) : List ℝ := semRun t s.ops.reverse

def BSWF (s : BS) : Prop := s.n = s.ops.length

/-- `s'` extends `s` by emitting further operations. -/
def BSExt (s s' : BS) : Prop := ∃ l, s'.ops = l ++ s.ops

def BSHas (t : ℝ) (s : BS) (i : ℕ) (x : ℝ) : Prop :=
  i < s.ops.length ∧ (bsVals t s).getD i 0 = x

theorem bsVals_length (t : ℝ) (s : BS) : (bsVals t s).length = s.ops.length := by
  simp [bsVals, semRun, semFold_length]

theorem BSExt.refl (s : BS) : BSExt s s := ⟨[], rfl⟩

theorem BSExt.trans {s s' s'' : BS} (h : BSExt s s') (h' : BSExt s' s'') : BSExt s s'' := by
  obtain ⟨l, hl⟩ := h
  obtain ⟨l', hl'⟩ := h'
  exact ⟨l' ++ l, by rw [hl', hl, List.append_assoc]⟩

theorem BSExt.vals {s s' : BS} (t : ℝ) (h : BSExt s s') :
    ∃ r, bsVals t s' = bsVals t s ++ r := by
  obtain ⟨l, hl⟩ := h
  obtain ⟨r, hr⟩ := semFold_prefix t l.reverse (bsVals t s)
  refine ⟨r, ?_⟩
  have : bsVals t s' = semFold t l.reverse (bsVals t s) := by
    rw [bsVals, hl, List.reverse_append, semRun, semFold_append]
    rfl
  rw [this, hr]

theorem BSHas.mono {t : ℝ} {s s' : BS} {i : ℕ} {x : ℝ} (h : BSExt s s')
    (hh : BSHas t s i x) : BSHas t s' i x := by
  obtain ⟨r, hr⟩ := h.vals t
  obtain ⟨hi, hx⟩ := hh
  have hl : i < (bsVals t s).length := by rwa [bsVals_length]
  refine ⟨?_, ?_⟩
  · obtain ⟨l, hl'⟩ := h
    rw [hl']; simp; omega
  · rw [hr, List.getD_append _ _ _ _ hl]; exact hx

/-! ### Facts and triples -/

/-- A persistent fact about a builder state. -/
structure SFact where
  P : BS → Prop
  mono : ∀ {s s' : BS}, BSExt s s' → P s → P s'

/-- Register `i` holds the value `x`. -/
def SFact.has (t : ℝ) (i : ℕ) (x : ℝ) : SFact := ⟨fun s => BSHas t s i x, BSHas.mono⟩

/-- `rs` is a list of `m` registers; the `i`-th holds `X (k + i)`. -/
def SFact.hasK (t : ℝ) (rs : List ℕ) (k m : ℕ) (X : ℕ → ℝ) : SFact :=
  ⟨fun s => rs.length = m ∧ ∀ i < m, BSHas t s (rs.getD i 0) (X (k + i)),
    fun h ⟨hl, hh⟩ => ⟨hl, fun i hi => (hh i hi).mono h⟩⟩

/-- `rs` is a list of `n` registers; the `j`-th holds `X j`. -/
def SFact.hasF (t : ℝ) (rs : List ℕ) (n : ℕ) (X : ℕ → ℝ) : SFact :=
  ⟨fun s => rs.length = n ∧ ∀ j < n, BSHas t s (rs.getD j 0) (X j),
    fun h ⟨hl, hh⟩ => ⟨hl, fun i hi => (hh i hi).mono h⟩⟩

def Sat (Γ : List SFact) (s : BS) : Prop := ∀ F ∈ Γ, F.P s

theorem Sat.mono {Γ : List SFact} {s s' : BS} (h : BSExt s s') (hs : Sat Γ s) : Sat Γ s' :=
  fun F hF => F.mono h (hs F hF)

/-- `Γ` entails the fact `F` (in every state). -/
def Impl (Γ : List SFact) (F : SFact) : Prop := ∀ s, Sat Γ s → F.P s

theorem Impl.of_mem {Γ : List SFact} {F : SFact} (h : F ∈ Γ) : Impl Γ F := fun _ hs => hs F h

/-- Hoare triple: from a well-formed state satisfying `Γ`, `m` returns a result whose new facts
`Q result` hold in a well-formed extension of the state. -/
def Tr (Γ : List SFact) {α : Type} (m : B α) (Q : α → List SFact) : Prop :=
  ∀ s : BS, BSWF s → Sat Γ s →
    BSWF (m.run s).2 ∧ BSExt s (m.run s).2 ∧ Sat (Q (m.run s).1) (m.run s).2

section Rules
variable {t : ℝ} {Γ : List SFact} {α β : Type}

theorem Tr_bind {m : B α} {f : α → B β} {Q : α → List SFact} {R : β → List SFact}
    (hm : Tr Γ m Q) (hf : ∀ a, Tr (Q a ++ Γ) (f a) R) : Tr Γ (m >>= f) R := by
  intro s w hs
  obtain ⟨w1, e1, q1⟩ := hm s w hs
  have hs1 : Sat (Q (m.run s).1 ++ Γ) (m.run s).2 := by
    intro F hF
    rcases List.mem_append.1 hF with h | h
    · exact q1 F h
    · exact F.mono e1 (hs F h)
  obtain ⟨w2, e2, r2⟩ := hf _ _ w1 hs1
  exact ⟨w2, e1.trans e2, r2⟩

theorem Tr_pure {a : α} {Q : α → List SFact} (h : ∀ s, Sat Γ s → Sat (Q a) s) :
    Tr Γ (pure a) Q := by
  intro s w hs
  exact ⟨w, BSExt.refl s, h s hs⟩

theorem Tr_ctx {m : B α} {Q : α → List SFact} {Γ' : List SFact} (h : Tr Γ m Q)
    (hΓ : ∀ s, Sat Γ' s → Sat Γ s) : Tr Γ' m Q :=
  fun s w hs => h s w (hΓ s hs)

theorem Tr_post {m : B α} {Q Q' : α → List SFact} (h : Tr Γ m Q)
    (hQ : ∀ a s, Sat (Q a) s → Sat (Q' a) s) : Tr Γ m Q' := by
  intro s w hs
  obtain ⟨w1, e1, q1⟩ := h s w hs
  exact ⟨w1, e1, hQ _ _ q1⟩

theorem Tr_ite {c : Prop} [Decidable c] {m₁ m₂ : B α} {Q : α → List SFact}
    (h₁ : c → Tr Γ m₁ Q) (h₂ : ¬c → Tr Γ m₂ Q) : Tr Γ (if c then m₁ else m₂) Q := by
  by_cases hc : c
  · simp only [hc, ↓reduceIte]; exact h₁ hc
  · simp only [hc, ↓reduceIte]; exact h₂ hc

theorem Tr_bind_g {m : B ℕ} {f : ℕ → B β} {z : ℝ} {R : β → List SFact}
    (hm : Tr Γ m (fun r => [SFact.has t r z]))
    (hf : ∀ r, ∀ z', z' = z → Tr ([SFact.has t r z'] ++ Γ) (f r) R) : Tr Γ (m >>= f) R :=
  Tr_bind hm (fun r => hf r z rfl)

theorem Tr_bind_gF {m : B (List ℕ)} {f : List ℕ → B β} {n : ℕ} {X : ℕ → ℝ} {R : β → List SFact}
    (hm : Tr Γ m (fun rs => [SFact.hasF t rs n X]))
    (hf : ∀ rs, ∀ X' : ℕ → ℝ, (∀ j < n, X' j = X j) →
      Tr ([SFact.hasF t rs n X'] ++ Γ) (f rs) R) : Tr Γ (m >>= f) R :=
  Tr_bind hm (fun rs => hf rs X (fun _ _ => rfl))

end Rules

/-! ### Primitives -/

theorem emit_run (o : Op) (s : BS) :
    (emit o).run s = (s.n, ⟨o :: s.ops, s.n + 1⟩) := rfl

theorem bsVals_cons (t : ℝ) (o : Op) (s : BS) :
    bsVals t ⟨o :: s.ops, s.n + 1⟩ = bsVals t s ++ [semStep t (bsVals t s) o] := by
  show semRun t (o :: s.ops).reverse = _
  rw [List.reverse_cons, semRun, semFold_append]
  rfl

theorem Tr_emit {t : ℝ} {Γ : List SFact} (o : Op) (z : ℝ)
    (h : ∀ s, BSWF s → Sat Γ s → semStep t (bsVals t s) o = z) :
    Tr Γ (emit o) (fun r => [SFact.has t r z]) := by
  intro s w hs
  have w' : s.n = s.ops.length := w
  rw [emit_run]
  refine ⟨?_, ⟨[o], rfl⟩, ?_⟩
  · show s.n + 1 = (o :: s.ops).length
    simp [w']
  · intro F hF
    rw [List.mem_singleton] at hF
    subst hF
    have hlen := bsVals_length t s
    refine ⟨?_, ?_⟩
    · simp; omega
    · show (bsVals t ⟨o :: s.ops, s.n + 1⟩).getD s.n 0 = z
      rw [bsVals_cons, List.getD_append_right _ _ _ _ (by rw [hlen, w']),
        ← h s w hs]
      have : s.n - (bsVals t s).length = 0 := by rw [hlen, w']; simp
      rw [this]
      rfl

theorem Impl.has {t : ℝ} {Γ : List SFact} {a : ℕ} {x : ℝ} (h : Impl Γ (SFact.has t a x))
    {s : BS} (hs : Sat Γ s) : (bsVals t s).getD a 0 = x := (h s hs).2

/-- Find a fact in the context list. -/
syntax "mem" : tactic
macro_rules
  | `(tactic| mem) => `(tactic| first
    | exact List.mem_cons_self
    | assumption
    | (refine List.mem_cons_of_mem _ ?_; mem))

/-- Discharge `Impl Γ F` by finding `F` in `Γ`. -/
syntax "impl_mem" : tactic
macro_rules
  | `(tactic| impl_mem) => `(tactic| exact Impl.of_mem (by mem))

theorem Impl.weaken {Γ : List SFact} {F : SFact} (G : List SFact) (h : Impl Γ F) :
    Impl (G ++ Γ) F :=
  fun s hs => h s (fun F' hF' => hs F' (List.mem_append_right _ hF'))

theorem Tr_val {t : ℝ} {Γ : List SFact} {m : B ℕ} {z z' : ℝ}
    (h : Tr Γ m (fun r => [SFact.has t r z])) (hz : z = z') :
    Tr Γ m (fun r => [SFact.has t r z']) := by
  subst hz; exact h

section Prims
variable {t : ℝ} {Γ : List SFact}

theorem Tr_var : Tr Γ (emit .var) (fun r => [SFact.has t r t]) :=
  Tr_emit _ _ (fun _ _ _ => rfl)

theorem Tr_cst {n : Int} {d : Nat} :
    Tr Γ (cst n d) (fun r => [SFact.has t r ((n : ℝ) / (d : ℝ))]) :=
  Tr_emit _ _ (fun _ _ _ => rfl)

theorem Tr_addB {a b : ℕ} {x y : ℝ} (ha : Impl Γ (SFact.has t a x) := by impl_mem)
    (hb : Impl Γ (SFact.has t b y) := by impl_mem) :
    Tr Γ (addB a b) (fun r => [SFact.has t r (x + y)]) :=
  Tr_emit _ _ (fun _ _ hs => by
    simp only [semStep]; rw [ha.has hs, hb.has hs])

theorem Tr_negB {a : ℕ} {x : ℝ} (ha : Impl Γ (SFact.has t a x) := by impl_mem) :
    Tr Γ (negB a) (fun r => [SFact.has t r (-x)]) :=
  Tr_emit _ _ (fun _ _ hs => by
    simp only [semStep]; rw [ha.has hs])

theorem Tr_mulB {a b : ℕ} {x y : ℝ} (ha : Impl Γ (SFact.has t a x) := by impl_mem)
    (hb : Impl Γ (SFact.has t b y) := by impl_mem) :
    Tr Γ (mulB a b) (fun r => [SFact.has t r (x * y)]) :=
  Tr_emit _ _ (fun _ _ hs => by
    simp only [semStep]; rw [ha.has hs, hb.has hs])

theorem Tr_smulB {a : ℕ} {x : ℝ} {n : Int} {d : Nat} (ha : Impl Γ (SFact.has t a x) := by impl_mem) :
    Tr Γ (smulB a n d) (fun r => [SFact.has t r (x * ((n : ℝ) / (d : ℝ)))]) :=
  Tr_emit _ _ (fun _ _ hs => by
    simp only [semStep, Const.val]; rw [ha.has hs])

theorem Tr_sdivB {a : ℕ} {x : ℝ} {n : Int} {d : Nat} (ha : Impl Γ (SFact.has t a x) := by impl_mem) :
    Tr Γ (sdivB a n d) (fun r => [SFact.has t r (x * ((n : ℝ) / (d : ℝ))⁻¹)]) :=
  Tr_emit _ _ (fun _ _ hs => by
    simp only [semStep, Const.val]; rw [ha.has hs])

theorem Tr_addcB {a : ℕ} {x : ℝ} {n : Int} {d : Nat} (ha : Impl Γ (SFact.has t a x) := by impl_mem) :
    Tr Γ (addcB a n d) (fun r => [SFact.has t r (x + (n : ℝ) / (d : ℝ))]) :=
  Tr_emit _ _ (fun _ _ hs => by
    simp only [semStep, Const.val]; rw [ha.has hs])

theorem Tr_invB {a : ℕ} {x : ℝ} (ha : Impl Γ (SFact.has t a x) := by impl_mem) :
    Tr Γ (invB a) (fun r => [SFact.has t r x⁻¹]) :=
  Tr_emit _ _ (fun _ _ hs => by
    simp only [semStep]; rw [ha.has hs])

theorem Tr_logB {a : ℕ} {x : ℝ} (ha : Impl Γ (SFact.has t a x) := by impl_mem) :
    Tr Γ (logB a) (fun r => [SFact.has t r (Real.log x)]) :=
  Tr_emit _ _ (fun _ _ hs => by
    simp only [semStep]; rw [ha.has hs])

theorem Tr_emit_smul {a : ℕ} {x : ℝ} {c : Const} (ha : Impl Γ (SFact.has t a x) := by impl_mem) :
    Tr Γ (emit (.smul a c)) (fun r => [SFact.has t r (x * c.val)]) :=
  Tr_emit _ _ (fun _ _ hs => by
    simp only [semStep]; rw [ha.has hs])

end Prims

end BecknerOnofri.V2.Interval
