module

public import BecknerOnofri.V2.Interval.FamilyMath

@[expose] public section

/-!
# Specification of the family builder, phase 3: entropy, functional, gradient
-/

namespace BecknerOnofri.V2.Interval

open BecknerOnofri.V2.FiniteState BecknerOnofri.HighDim.Spin Finset

attribute [local irreducible] addB negB mulB smulB sdivB addcB invB logB cst powB sumB mapR pochGo

theorem lsBody_spec (t : ℝ) {Γ : List SFact} (c1 : ℕ) (ps : List ℕ) (j : ℕ) (hj : j < 13)
    (hps : SFact.hasF t ps 13 (psVal t) ∈ Γ := by mem) :
    Tr Γ (lsBody c1 ps j) (fun r => [SFact.has t r (lsVal t j)]) := by
  unfold lsBody
  refine Tr_fact (SFact.has t (ps.getD j c1) (psVal t j))
    (Impl.getF c1 (Impl.of_mem hps) hj) ?_
  st y
  refine Tr_val (Tr_logB (Impl.of_mem (by mem))) ?_
  subst_vars
  simp only [lsVal, Const.val, choose_eq]
  push_cast
  rfl

theorem msBody_spec (t : ℝ) {Γ : List SFact} (c1 : ℕ) (ps : List ℕ) (s0 : ℕ)
    (hps : SFact.hasF t ps 13 (psVal t) ∈ Γ := by mem) :
    Tr Γ (msBody c1 ps s0) (fun r => [SFact.has t r (msVal t s0)]) := by
  unfold msBody
  refine Tr_bind (Tr_mapM (t := t) 13 (X := fun j => psVal t j * momR s0 j) ?_) (fun terms => ?_)
  · intro j hj
    unfold msTerm
    refine Tr_fact (SFact.has t (ps.getD j c1) (psVal t j))
      (Impl.getF c1 (Impl.of_mem hps) hj) ?_
    refine Tr_val (Tr_emit_smul (Impl.of_mem (by mem))) ?_
    simp only [Const.val, momR]
  · exact Tr_sumB' (Impl.of_mem (by mem))

theorem mpBody_spec (t : ℝ) {Γ : List SFact} (c1 : ℕ) (ms : List ℕ) (j : ℕ)
    (hms : SFact.hasF t ms 12 (msVal t) ∈ Γ := by mem) :
    Tr Γ (mpBody c1 ms j) (fun r => [SFact.has t r (MpVal t j)]) := by
  unfold mpBody
  refine Tr_bind (Tr_mapM (t := t) 12 (X := fun s0 => msVal t s0 * (wR s0 * momR s0 j)) ?_)
    (fun terms => ?_)
  · intro s0 hs0
    unfold mpTerm
    refine Tr_fact (SFact.has t (ms.getD s0 c1) (msVal t s0))
      (Impl.getF c1 (Impl.of_mem hms) hs0) ?_
    refine Tr_val (Tr_emit_smul (Impl.of_mem (by mem))) ?_
    simp only [Const.val, wR, momR]
  · exact Tr_sumB' (Impl.of_mem (by mem))

theorem en2Term_spec (t : ℝ) {Γ : List SFact} (c1 : ℕ) (ms : List ℕ) (s0 : ℕ) (hs0 : s0 < 12)
    (hms : SFact.hasF t ms 12 (msVal t) ∈ Γ := by mem) :
    Tr Γ (en2Term c1 ms s0) (fun r => [SFact.has t r (msVal t s0 ^ 2 * wR s0)]) := by
  unfold en2Term
  refine Tr_fact (SFact.has t (ms.getD s0 c1) (msVal t s0))
    (Impl.getF c1 (Impl.of_mem hms) hs0) ?_
  st pw
  refine Tr_val (Tr_emit_smul (Impl.of_mem (by mem))) ?_
  subst_vars
  simp only [Const.val, wR]

theorem gBody_spec (t : ℝ) {Γ : List SFact} (c1 : ℕ) (ls Mp : List ℕ) (j : ℕ) (hj : j < 13)
    (hls : SFact.hasF t ls 13 (lsVal t) ∈ Γ := by mem)
    (hMp : SFact.hasF t Mp 13 (MpVal t) ∈ Γ := by mem) :
    Tr Γ (gBody c1 ls Mp j) (fun r => [SFact.has t r (gVal t j)]) := by
  unfold gBody
  refine Tr_fact (SFact.has t (ls.getD j c1) (lsVal t j))
    (Impl.getF c1 (Impl.of_mem hls) hj) ?_
  refine Tr_fact (SFact.has t (Mp.getD j c1) (MpVal t j))
    (Impl.getF c1 (Impl.of_mem (by mem)) hj) ?_
  st y1
  st ny
  st y2
  refine Tr_val (Tr_smulB (Impl.of_mem (by mem))) ?_
  subst_vars
  simp only [gVal]
  push_cast
  ring

theorem phase3_spec (t : ℝ) {Γ : List SFact} (c1 : ℕ) (ps : List ℕ)
    (hps : SFact.hasF t ps 13 (psVal t) ∈ Γ := by mem) :
    Tr Γ (phase3 c1 ps) (fun r => [SFact.has t r.f (functional (famLaw t)),
      SFact.hasF t r.g 13 (gF t),
      SFact.has t r.meang (regMean (famLaw t) (gradient (famLaw t)))]) := by
  unfold phase3
  refine Tr_bind (Tr_mapM (t := t) 13 (X := lsVal t) (fun j hj => lsBody_spec t c1 ps j hj))
    (fun ls => ?_)
  refine Tr_bind (Tr_mapM (t := t) 12 (X := msVal t) (fun s0 _ => msBody_spec t c1 ps s0))
    (fun ms => ?_)
  refine Tr_bind (Tr_mapM (t := t) 13 (X := MpVal t) (fun j _ => mpBody_spec t c1 ms j))
    (fun Mp => ?_)
  refine Tr_bind (Tr_mapM (t := t) 13 (X := fun j => psVal t j * lsVal t j) ?_) (fun entT => ?_)
  · intro j hj
    refine Tr_fact (SFact.has t (ps.getD j c1) (psVal t j))
      (Impl.getF c1 (Impl.of_mem (by mem)) hj) ?_
    refine Tr_fact (SFact.has t (ls.getD j c1) (lsVal t j))
      (Impl.getF c1 (Impl.of_mem (by mem)) hj) ?_
    exact Tr_mulB
  refine Tr_bind (Tr_val (t := t) (Tr_sumB' (Impl.of_mem (by mem))) (show _ = entVal t from rfl))
    (fun ent => ?_)
  refine Tr_bind (Tr_mapM (t := t) 12 (X := fun s0 => msVal t s0 ^ 2 * wR s0)
    (fun s0 hs0 => en2Term_spec t c1 ms s0 hs0)) (fun en2T => ?_)
  refine Tr_bind (Tr_val (t := t) (Tr_sumB' (Impl.of_mem (by mem))) (show _ = en2Val t from rfl))
    (fun en2 => ?_)
  st f1
  st f2
  st f
  refine Tr_bind (Tr_mapM (t := t) 13 (X := gVal t) (fun j hj => gBody_spec t c1 ls Mp j hj))
    (fun g => ?_)
  refine Tr_bind (Tr_mapM (t := t) 13 (X := fun j => psVal t j * gVal t j) ?_) (fun mgT => ?_)
  · intro j hj
    refine Tr_fact (SFact.has t (ps.getD j c1) (psVal t j))
      (Impl.getF c1 (Impl.of_mem (by mem)) hj) ?_
    refine Tr_fact (SFact.has t (g.getD j c1) (gVal t j))
      (Impl.getF c1 (Impl.of_mem (by mem)) hj) ?_
    exact Tr_mulB
  refine Tr_bind (Tr_val (t := t) (Tr_sumB' (Impl.of_mem (by mem)))
    (show _ = ∑ j ∈ range 13, psVal t j * gVal t j from rfl)) (fun meang => ?_)
  refine Tr_pure fun s hs F hF => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hF
  rcases hF with rfl | rfl | rfl
  · fin fR
    subst_vars
    rw [← f_eq]
    push_cast
    ring
  · obtain ⟨hl, hh⟩ := hs (SFact.hasF t g 13 (gVal t)) (by mem)
    exact ⟨hl, fun j hj => by rw [← gVal_gF t hj]; exact hh j hj⟩
  · have h1 : BSHas t s meang (∑ j ∈ range 13, psVal t j * gVal t j) :=
      hs (SFact.has t meang (∑ j ∈ range 13, psVal t j * gVal t j)) (by mem)
    have h2 : ∑ j ∈ range 13, psVal t j * gVal t j = ∑ j ∈ range 13, psVal t j * gF t j :=
      Finset.sum_congr rfl fun j hj => by rw [gVal_gF t (mem_range.1 hj)]
    show BSHas t s meang _
    rw [← meang_eq, ← h2]
    exact h1

end BecknerOnofri.V2.Interval
