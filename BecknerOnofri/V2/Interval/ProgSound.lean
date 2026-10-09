module

public import BecknerOnofri.V2.Interval.JetSound
public import BecknerOnofri.V2.Interval.Prog

@[expose] public section

/-!
# Soundness of the straight-line program interpreter

Two real semantics of a program `p`:

* `jetRun t p` : the list of formal power series (jets) of all registers at the point `t`
  (the variable register is `C t + X`; `+`, `*`, scalar multiples are the ring operations of
  `ℝ⟦X⟧`, `inv` is the power series inverse, `log` is `logSeries`);
* `semRun t p` : the list of real values (the same operations on `ℝ`; `Real.log`, `⁻¹`).

`jetRun_map_coeff` says `semRun` is the zeroth coefficient of `jetRun`.

If the interval interpreter `run x p` succeeds on a cell `[lo, hi]` (with `CtxOK x lo hi`), then
for every register `i` the family `s ↦ (jetRun s p)[i]` is a coherent jet on the cell, the box of
register `i` encloses the whole jet at every `t` in the cell, and `mid` encloses it at the centre.
Success also certifies the domain conditions (nonzero denominators, positive logarithm arguments).
-/

namespace BecknerOnofri.V2.Interval

open PowerSeries

/-- Real value of a program constant. -/
noncomputable def Const.val : Const → ℝ
  | .q n d => (n : ℝ) / d
  | .prod n₁ d₁ n₂ d₂ => ((n₁ : ℝ) / d₁) * ((n₂ : ℝ) / d₂)
  | .inv n d => ((n : ℝ) / d)⁻¹

theorem Const.toIv_mem {c : Const} {iv : Iv} (h : c.toIv = some iv) : iv.Mem c.val := by
  cases c with
  | q n d =>
    simp only [Const.toIv] at h
    split_ifs at h with hd
    obtain rfl := Option.some.inj h
    exact Iv.mem_ofRat n d hd
  | prod n₁ d₁ n₂ d₂ =>
    simp only [Const.toIv] at h
    split_ifs at h with hd
    obtain rfl := Option.some.inj h
    exact Iv.mem_mul (Iv.mem_ofRat n₁ d₁ hd.1) (Iv.mem_ofRat n₂ d₂ hd.2)
  | inv n d =>
    simp only [Const.toIv] at h
    split_ifs at h with hd
    exact (Iv.mem_recip (Iv.mem_ofRat n d hd) h).2

/-! ### Real semantics -/

/-- One step of the real semantics. -/
noncomputable def semStep (t : ℝ) (vals : List ℝ) : Op → ℝ
  | .var => t
  | .const c => c.val
  | .add i j => vals.getD i 0 + vals.getD j 0
  | .neg i => -vals.getD i 0
  | .mul i j => vals.getD i 0 * vals.getD j 0
  | .smul i c => vals.getD i 0 * c.val
  | .addc i c => vals.getD i 0 + c.val
  | .inv i => (vals.getD i 0)⁻¹
  | .log i => Real.log (vals.getD i 0)

/-- Real semantics of a program, continuing from the register values `vals`. -/
noncomputable def semFold (t : ℝ) (p : Prog) (vals : List ℝ) : List ℝ :=
  p.foldl (fun vals op => vals ++ [semStep t vals op]) vals

/-- Real semantics of a program: the list of all register values at `t`. -/
noncomputable def semRun (t : ℝ) (p : Prog) : List ℝ := semFold t p []

/-- One step of the jet semantics. -/
noncomputable def jetStep (t : ℝ) (vals : List ℝ⟦X⟧) : Op → ℝ⟦X⟧
  | .var => C t + X
  | .const c => C c.val
  | .add i j => vals.getD i 0 + vals.getD j 0
  | .neg i => -vals.getD i 0
  | .mul i j => vals.getD i 0 * vals.getD j 0
  | .smul i c => C c.val * vals.getD i 0
  | .addc i c => vals.getD i 0 + C c.val
  | .inv i => (vals.getD i 0)⁻¹
  | .log i => logSeries (vals.getD i 0)

noncomputable def jetFold (t : ℝ) (p : Prog) (vals : List ℝ⟦X⟧) : List ℝ⟦X⟧ :=
  p.foldl (fun vals op => vals ++ [jetStep t vals op]) vals

/-- The jets of all registers of `p` at `t`. -/
noncomputable def jetRun (t : ℝ) (p : Prog) : List ℝ⟦X⟧ := jetFold t p []

theorem getD_map_cc (J : List ℝ⟦X⟧) (i : ℕ) :
    (J.map constantCoeff).getD i 0 = constantCoeff (J.getD i 0) := by
  induction J generalizing i with
  | nil => simp
  | cons a J ih =>
    cases i with
    | zero => simp only [List.map_cons, List.getD_cons_zero]
    | succ i => simp only [List.map_cons, List.getD_cons_succ]; exact ih i

theorem constantCoeff_logSeries (φ : ℝ⟦X⟧) :
    constantCoeff (logSeries φ) = Real.log (constantCoeff φ) := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_logSeries_zero]

theorem cc_jetStep (t : ℝ) (J : List ℝ⟦X⟧) (op : Op) :
    constantCoeff (jetStep t J op) = semStep t (J.map constantCoeff) op := by
  cases op with
  | var => simp [jetStep, semStep]
  | const c => simp [jetStep, semStep]
  | add i j => simp only [jetStep, semStep, map_add, getD_map_cc]
  | neg i => simp only [jetStep, semStep, map_neg, getD_map_cc]
  | mul i j => simp only [jetStep, semStep, map_mul, getD_map_cc]
  | smul i c =>
    simp only [jetStep, semStep, map_mul, constantCoeff_C, getD_map_cc]; ring
  | addc i c => simp only [jetStep, semStep, map_add, constantCoeff_C, getD_map_cc]
  | inv i => simp only [jetStep, semStep, constantCoeff_inv, getD_map_cc]
  | log i => simp only [jetStep, semStep, constantCoeff_logSeries, getD_map_cc]

theorem jetFold_map_cc (t : ℝ) (p : Prog) :
    ∀ J : List ℝ⟦X⟧, (jetFold t p J).map constantCoeff = semFold t p (J.map constantCoeff) := by
  induction p with
  | nil => intro J; rfl
  | cons op p ih =>
    intro J
    simp only [jetFold, semFold, List.foldl_cons] at ih ⊢
    rw [ih (J ++ [jetStep t J op]), List.map_append, List.map_singleton, cc_jetStep]

theorem jetRun_map_cc (t : ℝ) (p : Prog) : (jetRun t p).map constantCoeff = semRun t p := by
  simpa [jetRun, semRun] using jetFold_map_cc t p []

theorem cc_jetRun (t : ℝ) (p : Prog) (i : ℕ) :
    constantCoeff ((jetRun t p).getD i 0) = (semRun t p).getD i 0 := by
  rw [← jetRun_map_cc, getD_map_cc]

theorem coeff0_jetRun (t : ℝ) (p : Prog) (i : ℕ) :
    coeff 0 ((jetRun t p).getD i 0) = (semRun t p).getD i 0 := by
  rw [coeff_zero_eq_constantCoeff_apply, cc_jetRun]

/-! ### The invariant -/

/-- The default register used for out-of-range reads. -/
def dflt : CJet := CJet.const Iv.zero

/-- The invariant relating interval registers to the coherent jets `J s`. -/
structure Inv (x : Ctx) (lo hi : ℝ) (regs : List CJet) (J : ℝ → List ℝ⟦X⟧) : Prop where
  len : ∀ s, (J s).length = regs.length
  coh : ∀ i, i < regs.length → Coh (Set.Icc lo hi) (fun s => (J s).getD i 0)
  box : ∀ i, i < regs.length → ∀ t ∈ Set.Icc lo hi,
    JMem (regs.getD i dflt).box ((J t).getD i 0)
  mid : ∀ i, i < regs.length → JMem (regs.getD i dflt).mid ((J ((lo + hi) / 2)).getD i 0)

theorem RS.get_some {st : RS} (hwf : st.n = st.rev.length) {i : ℕ} {a : CJet}
    (h : st.get i = some a) : i < st.rev.reverse.length ∧ st.rev.reverse.getD i dflt = a := by
  unfold RS.get at h
  split_ifs at h with hi
  have hi' : i < st.rev.length := hwf ▸ hi
  have h2 : st.rev[st.n - 1 - i]? = some a := h
  rw [hwf] at h2
  have h3 : st.rev.reverse[i]? = some a := by
    rw [List.getElem?_reverse hi']; exact h2
  refine ⟨(List.getElem?_eq_some_iff.mp h3).1, ?_⟩
  rw [List.getD_eq_getElem?_getD, h3]
  rfl

/-- What a successful step produces. -/
def StepOK (lo hi : ℝ) (J : ℝ → List ℝ⟦X⟧) (op : Op) (r : CJet) : Prop :=
  Coh (Set.Icc lo hi) (fun s => jetStep s (J s) op) ∧
    (∀ t ∈ Set.Icc lo hi, JMem r.box (jetStep t (J t) op)) ∧
    JMem r.mid (jetStep ((lo + hi) / 2) (J ((lo + hi) / 2)) op)

theorem step_sound {x : Ctx} {lo hi : ℝ} (hx : CtxOK x lo hi) (hlohi : lo ≤ hi)
    {st : RS} (hwf : st.n = st.rev.length) {J : ℝ → List ℝ⟦X⟧}
    (hI : Inv x lo hi st.rev.reverse J)
    {op : Op} {r : CJet} (h : step x st op = some r) : StepOK lo hi J op r := by
  cases op with
  | var =>
    simp only [step] at h
    obtain ⟨hm, hb⟩ := build_mem hx hlohi (A := fun s => C s + X) Coh.var
      (JMem.var hx.center) (fun t ht => JMem.var (hx.cell t ht)) h
    exact ⟨Coh.var, hb, hm ▸ JMem.var hx.center⟩
  | const c =>
    simp only [step] at h
    obtain ⟨iv, hiv, rfl⟩ := Option.map_eq_some_iff.mp h
    have hc := JMem.const (Const.toIv_mem hiv)
    exact ⟨Coh.const _, fun _ _ => hc, hc⟩
  | add i j =>
    simp only [step] at h
    obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨hia, rfl⟩ := RS.get_some hwf ha
    obtain ⟨hib, rfl⟩ := RS.get_some hwf hb
    unfold CJet.add at h
    obtain ⟨hm, hbx⟩ := build_mem hx hlohi (A := fun s => (J s).getD i 0 + (J s).getD j 0)
      ((hI.coh i hia).add (hI.coh j hib)) ((hI.mid i hia).add (hI.mid j hib))
      (fun t ht => (hI.box i hia t ht).add (hI.box j hib t ht)) h
    exact ⟨(hI.coh i hia).add (hI.coh j hib), hbx, by rw [hm]; exact (hI.mid i hia).add (hI.mid j hib)⟩
  | neg i =>
    simp only [step] at h
    obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨hia, rfl⟩ := RS.get_some hwf ha
    unfold CJet.neg at h
    obtain ⟨hm, hbx⟩ := build_mem hx hlohi (A := fun s => -(J s).getD i 0)
      (hI.coh i hia).neg (hI.mid i hia).neg (fun t ht => (hI.box i hia t ht).neg) h
    exact ⟨(hI.coh i hia).neg, hbx, by rw [hm]; exact (hI.mid i hia).neg⟩
  | mul i j =>
    simp only [step] at h
    obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨hia, rfl⟩ := RS.get_some hwf ha
    obtain ⟨hib, rfl⟩ := RS.get_some hwf hb
    unfold CJet.mul at h
    obtain ⟨hm, hbx⟩ := build_mem hx hlohi (A := fun s => (J s).getD i 0 * (J s).getD j 0)
      ((hI.coh i hia).mul (hI.coh j hib)) ((hI.mid i hia).mul (hI.mid j hib))
      (fun t ht => (hI.box i hia t ht).mul (hI.box j hib t ht)) h
    exact ⟨(hI.coh i hia).mul (hI.coh j hib), hbx, by rw [hm]; exact (hI.mid i hia).mul (hI.mid j hib)⟩
  | smul i c =>
    simp only [step] at h
    obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨iv, hiv, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨hia, rfl⟩ := RS.get_some hwf ha
    unfold CJet.smul at h
    have hc := Const.toIv_mem hiv
    obtain ⟨hm, hbx⟩ := build_mem hx hlohi (A := fun s => C c.val * (J s).getD i 0)
      ((hI.coh i hia).smul c.val) ((hI.mid i hia).smul hc)
      (fun t ht => (hI.box i hia t ht).smul hc) h
    exact ⟨(hI.coh i hia).smul c.val, hbx, by rw [hm]; exact (hI.mid i hia).smul hc⟩
  | addc i c =>
    simp only [step] at h
    obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨iv, hiv, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨hia, rfl⟩ := RS.get_some hwf ha
    unfold CJet.addc at h
    have hc := JMem.const (Const.toIv_mem hiv)
    obtain ⟨hm, hbx⟩ := build_mem hx hlohi (A := fun s => (J s).getD i 0 + C c.val)
      ((hI.coh i hia).add (Coh.const _)) ((hI.mid i hia).add hc)
      (fun t ht => (hI.box i hia t ht).add hc) h
    exact ⟨(hI.coh i hia).add (Coh.const _), hbx, by rw [hm]; exact (hI.mid i hia).add hc⟩
  | inv i =>
    simp only [step] at h
    obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨hia, rfl⟩ := RS.get_some hwf ha
    unfold CJet.recip at h
    obtain ⟨m, hmr, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨b, hbr, h⟩ := Option.bind_eq_some_iff.mp h
    have hne : ∀ t ∈ Set.Icc lo hi, constantCoeff ((J t).getD i 0) ≠ 0 :=
      fun t ht => ((hI.box i hia t ht).recip hbr).1
    have hcoh := (hI.coh i hia).inv hne
    obtain ⟨hm', hbx⟩ := build_mem hx hlohi (A := fun s => ((J s).getD i 0)⁻¹) hcoh
      ((hI.mid i hia).recip hmr).2 (fun t ht => ((hI.box i hia t ht).recip hbr).2) h
    exact ⟨hcoh, hbx, by rw [hm']; exact ((hI.mid i hia).recip hmr).2⟩
  | log i =>
    simp only [step] at h
    obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨hia, rfl⟩ := RS.get_some hwf ha
    unfold CJet.log at h
    obtain ⟨m, hmr, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨b, hbr, h⟩ := Option.bind_eq_some_iff.mp h
    have hne : ∀ t ∈ Set.Icc lo hi, constantCoeff ((J t).getD i 0) ≠ 0 :=
      fun t ht => ((hI.box i hia t ht).log hbr).1.ne'
    have hcoh := (hI.coh i hia).log hne
    obtain ⟨hm', hbx⟩ := build_mem hx hlohi (A := fun s => logSeries ((J s).getD i 0)) hcoh
      ((hI.mid i hia).log hmr).2 (fun t ht => ((hI.box i hia t ht).log hbr).2) h
    exact ⟨hcoh, hbx, by rw [hm']; exact ((hI.mid i hia).log hmr).2⟩

/-- Extending the invariant by one successful step. -/
theorem Inv.snoc {x : Ctx} {lo hi : ℝ} {regs : List CJet} {J : ℝ → List ℝ⟦X⟧}
    (hI : Inv x lo hi regs J) {op : Op} {r : CJet} (hs : StepOK lo hi J op r) :
    Inv x lo hi (regs ++ [r]) (fun s => J s ++ [jetStep s (J s) op]) := by
  obtain ⟨hA, hbx, hmid⟩ := hs
  have hdflt : ∀ i, i < regs.length → (regs ++ [r]).getD i dflt = regs.getD i dflt :=
    fun i hi => List.getD_append _ _ _ _ hi
  have hlast : (regs ++ [r]).getD regs.length dflt = r := by
    rw [List.getD_append_right _ _ _ _ le_rfl]; simp
  have hJ : ∀ s i, i < regs.length → (J s ++ [jetStep s (J s) op]).getD i 0 = (J s).getD i 0 :=
    fun s i hi => List.getD_append _ _ _ _ (by rw [hI.len s]; exact hi)
  have hJl : ∀ s, (J s ++ [jetStep s (J s) op]).getD regs.length 0 = jetStep s (J s) op := by
    intro s
    rw [List.getD_append_right _ _ _ _ (by rw [hI.len s])]
    simp [hI.len s]
  refine ⟨fun s => by simp [hI.len s], fun i hi => ?_, fun i hi t ht => ?_, fun i hi => ?_⟩
  · simp only [List.length_append, List.length_singleton] at hi
    by_cases e : i = regs.length
    · subst e
      have : (fun s => (J s ++ [jetStep s (J s) op]).getD regs.length 0) =
          fun s => jetStep s (J s) op := funext hJl
      rw [this]; exact hA
    · have : (fun s => (J s ++ [jetStep s (J s) op]).getD i 0) = fun s => (J s).getD i 0 :=
        funext fun s => hJ s i (by omega)
      rw [this]; exact hI.coh i (by omega)
  · simp only [List.length_append, List.length_singleton] at hi
    by_cases e : i = regs.length
    · subst e; rw [hlast, hJl]; exact hbx t ht
    · rw [hdflt i (by omega), hJ t i (by omega)]; exact hI.box i (by omega) t ht
  · simp only [List.length_append, List.length_singleton] at hi
    by_cases e : i = regs.length
    · subst e; rw [hlast, hJl]; exact hmid
    · rw [hdflt i (by omega), hJ _ i (by omega)]; exact hI.mid i (by omega)

theorem foldlM_sound {x : Ctx} {lo hi : ℝ} (hx : CtxOK x lo hi) (hlohi : lo ≤ hi) :
    ∀ (p : Prog) (st0 st : RS) (J0 : ℝ → List ℝ⟦X⟧), st0.n = st0.rev.length →
      Inv x lo hi st0.rev.reverse J0 →
      p.foldlM (fun st op => do
        let r ← step x st op
        pure (⟨st.n + 1, r :: st.rev⟩ : RS)) st0 = some st →
      st.n = st.rev.length ∧ Inv x lo hi st.rev.reverse (fun s => jetFold s p (J0 s)) := by
  intro p
  induction p with
  | nil =>
    intro st0 st J0 hwf hI h
    obtain rfl : st0 = st := Option.some.inj h
    exact ⟨hwf, hI⟩
  | cons op p ih =>
    intro st0 st J0 hwf hI h
    simp only [List.foldlM_cons] at h
    obtain ⟨st1, h1, h2⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨r, hr, h1'⟩ := Option.bind_eq_some_iff.mp h1
    simp only [Option.pure_def, Option.some.injEq] at h1'
    subst h1'
    have hI1 := hI.snoc (step_sound hx hlohi hwf hI hr)
    refine ih _ st _ (by simp [hwf]) ?_ h2
    simpa [List.reverse_cons] using hI1

/-- Soundness of the interpreter. -/
theorem runRS_sound {x : Ctx} {lo hi : ℝ} (hx : CtxOK x lo hi) (hlohi : lo ≤ hi) {p : Prog}
    {st : RS} (h : runRS x p = some st) :
    st.n = st.rev.length ∧ Inv x lo hi st.rev.reverse (fun s => jetRun s p) := by
  refine foldlM_sound hx hlohi p ⟨0, []⟩ st (fun _ => []) rfl ?_ h
  exact ⟨fun s => rfl, fun i hi => by simp at hi, fun i hi => by simp at hi,
    fun i hi => by simp at hi⟩

end BecknerOnofri.V2.Interval
