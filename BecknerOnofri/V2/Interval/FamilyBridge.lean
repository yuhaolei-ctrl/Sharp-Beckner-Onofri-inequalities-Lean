module

public import BecknerOnofri.V2.Interval.FamilySpec5
public import BecknerOnofri.V2.Interval.Final

@[expose] public section

/-!
# The registers of the family programs equal the FiniteState quantities

For `0 ≤ t < 1` (and additionally `t ≠ 0` for the normalised program) the output registers of
`familyProg true` / `familyProg false` evaluate to `famF`, `famResidVar`, `famResid + 1/4`
(respectively `famF/t⁴ - 1/10`, `1/50 - famResidVar/t⁴`, `famResid + 1/4`).  No denominator
hypotheses are needed beyond `t ≠ 0` and the positivity of the spin variance
(`0 ≤ t < 1`, used through `famSpinVar_eq_formula`): `⁻¹` and `Real.log` are total in the real
semantics of the interpreter and the program's expressions agree with those of `FiniteState`
as total functions.
-/

namespace BecknerOnofri.V2.Interval

open BecknerOnofri.V2.FiniteState BecknerOnofri.HighDim.Spin Finset

/-- Nonvanishing of the denominators of the program on `[0, 1)`: `1 + L`, the denominator of
`ω`, `ω ≥ 0` (so `1 + kω > 0` and `h + 1 > 0`), `14 - 10 t²` and the spin variance
`vz = regVar`.  The identification of the registers does not need them (the interpreter's
inverse is total); the last one is used in the form `vz = famVarFormula`. -/
theorem family_denominators_pos {t : ℝ} (h0 : 0 ≤ t) (h1 : t < 1) :
    0 < 1 + famL t ∧ 0 < famP (t ^ 2) * (1 - t) + t ^ 4 / 10 ∧ 0 ≤ famOmega t ∧
      (∀ k : ℕ, 0 < 1 + (k : ℝ) * famOmega t) ∧ 0 < 14 - 10 * t ^ 2 ∧
      0 < regVar (famLaw t) meanCoordinate t := by
  have h1t : 0 < 1 - t := by linarith
  have ht2 : 0 < 1 - t ^ 2 := by nlinarith
  have hL : 0 < 1 + famL t := by unfold famL; positivity
  have hP : 0 < famP (t ^ 2) * (1 - t) + t ^ 4 / 10 := by
    have hb : 0 < 31 * (1 - t ^ 2) ^ 3 + 61 * t ^ 2 * (1 - t ^ 2) ^ 2 +
        29 * t ^ 4 * (1 - t ^ 2) + 11 * t ^ 6 := by positivity
    have hid : famP (t ^ 2) = 31 * (1 - t ^ 2) ^ 3 + 61 * t ^ 2 * (1 - t ^ 2) ^ 2 +
        29 * t ^ 4 * (1 - t ^ 2) + 11 * t ^ 6 := by unfold famP; ring
    rw [hid]; positivity
  have hω : 0 ≤ famOmega t := by
    unfold famOmega
    exact div_nonneg (mul_nonneg (sq_nonneg t) h1t.le) hP.le
  refine ⟨hL, hP, hω, fun k => by positivity, by nlinarith, ?_⟩
  exact famSpinVar_pos_of_nonneg h0 h1

theorem family2_raw_spec (t : ℝ) (h0 : 0 ≤ t) (h1 : t < 1) :
    Tr [] (family2 true) (fun o => [SFact.has t o.f (famF t),
      SFact.has t o.v (famResidVar t), SFact.hasF t o.e 13 (outE t)]) := by
  unfold family2
  refine Tr_bind (phase1_spec t) (fun s1 => ?_)
  refine Tr_bind (phase2_spec t s1) (fun s2 => ?_)
  refine Tr_bind (phase3_spec t s1.c1 s2.ps) (fun s3 => ?_)
  refine Tr_bind (phase4_spec t h0 h1 s1 s2 s3) (fun s4 => ?_)
  exact phase5_raw_spec t s1 s3 s4

theorem family2_norm_spec (t : ℝ) (h0 : 0 < t) (h1 : t < 1) :
    Tr [] (family2 false) (fun o => [SFact.has t o.f (famF t / t ^ 4 - 1 / 10),
      SFact.has t o.v (1 / 50 - famResidVar t / t ^ 4), SFact.hasF t o.e 13 (outE t)]) := by
  unfold family2
  refine Tr_bind (phase1_spec t) (fun s1 => ?_)
  refine Tr_bind (phase2_spec t s1) (fun s2 => ?_)
  refine Tr_bind (phase3_spec t s1.c1 s2.ps) (fun s3 => ?_)
  refine Tr_bind (phase4_spec t h0.le h1 s1 s2 s3) (fun s4 => ?_)
  exact phase5_norm_spec t h0.ne' s1 s3 s4

theorem Tr_run {α : Type} {Q : α → List SFact} {m : B α} (h : Tr [] m Q) :
    BSWF (m.run ⟨[], 0⟩).2 ∧ Sat (Q (m.run ⟨[], 0⟩).1) (m.run ⟨[], 0⟩).2 :=
  let ⟨a, _, c⟩ := h ⟨[], 0⟩ rfl (fun _ hF => absurd hF List.not_mem_nil)
  ⟨a, c⟩

theorem regVal_familyProg (raw : Bool) (t : ℝ) (i : ℕ) :
    regVal (familyProg raw).1 i t = (bsVals t ((family2 raw).run ⟨[], 0⟩).2).getD i 0 := by
  rw [familyProg_eq]
  unfold family2Prog
  generalize (family2 raw).run ⟨[], 0⟩ = r
  rfl

theorem familyProg_outs (raw : Bool) : (familyProg raw).2 = ((family2 raw).run ⟨[], 0⟩).1 := by
  rw [familyProg_eq]
  unfold family2Prog
  generalize (family2 raw).run ⟨[], 0⟩ = r
  rfl

theorem registers_of_run {raw : Bool} {t : ℝ} {F V : ℝ} {E : ℕ → ℝ}
    (h : Sat [SFact.has t ((family2 raw).run ⟨[], 0⟩).1.f F,
      SFact.has t ((family2 raw).run ⟨[], 0⟩).1.v V,
      SFact.hasF t ((family2 raw).run ⟨[], 0⟩).1.e 13 E] ((family2 raw).run ⟨[], 0⟩).2) :
    regVal (familyProg raw).1 (familyProg raw).2.f t = F ∧
      regVal (familyProg raw).1 (familyProg raw).2.v t = V ∧
      ∀ j < 13, regVal (familyProg raw).1 ((familyProg raw).2.e.getD j 0) t = E j := by
  have e2 := familyProg_outs raw
  have e1 := regVal_familyProg raw t
  rw [e2]
  simp only [e1]
  generalize (family2 raw).run ⟨[], 0⟩ = r at h
  obtain ⟨hf, hv, he⟩ : BSHas t r.2 r.1.f F ∧ BSHas t r.2 r.1.v V ∧
      (r.1.e.length = 13 ∧ ∀ j < 13, BSHas t r.2 (r.1.e.getD j 0) (E j)) :=
    ⟨h _ (List.Mem.head _), h _ (List.Mem.tail _ (List.Mem.head _)),
      h _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))⟩
  exact ⟨hf.2, hv.2, fun j hj => (he.2 j hj).2⟩

/-- First row: the registers of `P1 = familyProg true` on `[0, 1)`. -/
theorem P1_registers {t : ℝ} (h0 : 0 ≤ t) (h1 : t < 1) :
    regVal P1.1 P1.2.f t = famF t ∧ regVal P1.1 P1.2.v t = famResidVar t ∧
      ∀ (j : ℕ) (hj : j < 13), regVal P1.1 (P1.2.e.getD j 0) t = famResid t ⟨j, hj⟩ + 1 / 4 := by
  obtain ⟨hf, hv, he⟩ := registers_of_run (Tr_run (family2_raw_spec t h0 h1)).2
  refine ⟨hf, hv, fun j hj => ?_⟩
  have := he j hj
  show regVal (familyProg true).1 ((familyProg true).2.e.getD j 0) t = _
  rw [this]
  simp [outE, famResidF, hj]

/-- Second and third rows: the registers of `P2 = familyProg false` on `(0, 1)`. -/
theorem P2_registers {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    regVal P2.1 P2.2.f t = famF t / t ^ 4 - 1 / 10 ∧
      regVal P2.1 P2.2.v t = 1 / 50 - famResidVar t / t ^ 4 ∧
      ∀ (j : ℕ) (hj : j < 13), regVal P2.1 (P2.2.e.getD j 0) t = famResid t ⟨j, hj⟩ + 1 / 4 := by
  obtain ⟨hf, hv, he⟩ := registers_of_run (Tr_run (family2_norm_spec t h0 h1)).2
  refine ⟨hf, hv, fun j hj => ?_⟩
  have := he j hj
  show regVal (familyProg false).1 ((familyProg false).2.e.getD j 0) t = _
  rw [this]
  simp [outE, famResidF, hj]

end BecknerOnofri.V2.Interval
