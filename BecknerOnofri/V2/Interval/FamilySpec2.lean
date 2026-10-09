module

public import BecknerOnofri.V2.Interval.FamilySpec1

@[expose] public section

/-!
# Specification of the family builder, phase 2: the law `p(t)`
-/

namespace BecknerOnofri.V2.Interval

open BecknerOnofri.V2.FiniteState BecknerOnofri.HighDim.Spin

attribute [local irreducible] addB negB mulB smulB sdivB addcB invB logB cst powB sumB mapR pochGo

/-- The law `p(t)` as a function on `ℕ` (zero outside the 13 states). -/
noncomputable def psVal (t : ℝ) (j : ℕ) : ℝ := if hj : j < 13 then famLaw t ⟨j, hj⟩ else 0

theorem famLaw_eq_prog (t : ℝ) (j : Count) :
    famLaw t j = (1 - famLam t) * (Nat.choose 12 j.val : ℝ) *
        pochU ((1 + famBias t) / 2) (famOmega t) j.val *
        pochU ((1 - famBias t) / 2) (famOmega t) (12 - j.val) * (pochD (famOmega t) 12)⁻¹ +
      (if j.val = 12 then famLam t else 0) := by
  unfold famLaw famNu pochU pochD
  have h1 : ∏ k ∈ Finset.range j.val, ((1 + famBias t) / 2 + (k : ℝ) * famOmega t) =
      ∏ m ∈ Finset.range j.val, ((1 + famBias t) / 2 + famOmega t * (m : ℝ)) :=
    Finset.prod_congr rfl fun k _ => by ring
  have h2 : ∏ k ∈ Finset.range (12 - j.val), ((1 - famBias t) / 2 + (k : ℝ) * famOmega t) =
      ∏ m ∈ Finset.range (12 - j.val), ((1 - famBias t) / 2 + famOmega t * (m : ℝ)) :=
    Finset.prod_congr rfl fun k _ => by ring
  have h3 : ∏ k ∈ Finset.range 12, (1 + (k : ℝ) * famOmega t) =
      ∏ m ∈ Finset.range 12, (famOmega t * (m : ℝ) + 1) :=
    Finset.prod_congr rfl fun k _ => by ring
  rw [h1, h2, h3]
  by_cases hj : j.val = 12 <;> simp [hj, div_eq_mul_inv] <;> ring

theorem phase2_spec (t : ℝ) {Γ : List SFact} (s : S1)
    (hc1 : SFact.has t s.c1 1 ∈ Γ := by mem)
    (hlam : SFact.has t s.lam (famLam t) ∈ Γ := by mem)
    (hh : SFact.has t s.h (famOmega t) ∈ Γ := by mem)
    (hAp : SFact.has t s.Ap ((1 + famBias t) / 2) ∈ Γ := by mem)
    (hAm : SFact.has t s.Am ((1 - famBias t) / 2) ∈ Γ := by mem) :
    Tr Γ (phase2 s) (fun r => [SFact.has t r.omlam (1 - famLam t),
      SFact.hasF t r.ps 13 (psVal t)]) := by
  unfold phase2
  refine Tr_bind (Tr_pochGo (t := t) (pA := (1 + famBias t) / 2) (pM := (1 - famBias t) / 2)
    (hv := famOmega t) 12 0 s.c1 s.c1 s.c1 (xu := 1) (xd := 1) (xn := 1) hAp hAm hh hc1 hc1 hc1
    (by simp [pochU]) (by simp [pochU]) (by simp [pochD])) (fun pr => ?_)
  refine Tr_fact (SFact.hasF t (s.c1 :: pr.ups) 13 (pochU ((1 + famBias t) / 2) (famOmega t)))
    (Impl.hasF_cons (x := 1) (Impl.of_mem (by mem)) (by simp [pochU]) (Impl.of_mem (by mem))) ?_
  refine Tr_fact (SFact.hasF t (s.c1 :: pr.downs) 13 (pochU ((1 - famBias t) / 2) (famOmega t)))
    (Impl.hasF_cons (x := 1) (Impl.of_mem (by mem)) (by simp [pochU]) (Impl.of_mem (by mem))) ?_
  dsimp only
  st nl
  st omlam
  st invden
  refine Tr_bind (Tr_mapM (t := t) 13 (X := psVal t) ?_) (fun ps => ?_)
  · intro j hj
    unfold psBody
    refine Tr_fact (SFact.has t ((s.c1 :: pr.ups).getD j s.c1)
      (pochU ((1 + famBias t) / 2) (famOmega t) j))
      (Impl.getF s.c1 (Impl.of_mem (by mem)) hj) ?_
    refine Tr_fact (SFact.has t ((s.c1 :: pr.downs).getD (12 - j) s.c1)
      (pochU ((1 - famBias t) / 2) (famOmega t) (12 - j)))
      (Impl.getF s.c1 (Impl.of_mem (by mem)) (by omega)) ?_
    st x1
    st x2
    st x3
    st x4
    have hF : (⟨j, hj⟩ : Count) = ⟨j, hj⟩ := rfl
    refine Tr_ite (fun hj12 => ?_) (fun hj12 => ?_)
    · refine Tr_val (Tr_addB (Impl.of_mem (by mem)) (Impl.of_mem (by mem))) ?_
      subst_vars
      simp only [psVal, hj, ↓reduceDIte]
      rw [famLaw_eq_prog t ⟨12, hj⟩]
      simp only [choose_eq, Int.cast_natCast, Nat.cast_one, div_one, zero_add, ↓reduceIte]
      ring
    · refine Tr_pure fun s hs F hF => ?_
      rw [List.mem_singleton] at hF
      subst hF
      fin x4R
      subst_vars
      simp only [psVal, hj, ↓reduceDIte]
      rw [famLaw_eq_prog t ⟨j, hj⟩]
      simp only [choose_eq, Int.cast_natCast, Nat.cast_one, div_one, zero_add, hj12, ↓reduceIte,
        add_zero]
      ring
  · refine Tr_pure fun s hs F hF => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hF
    rcases hF with rfl | rfl
    · fin omlamR
      subst_vars; ring
    · exact hs _ (by mem)

end BecknerOnofri.V2.Interval
