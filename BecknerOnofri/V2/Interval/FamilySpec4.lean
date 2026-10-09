module

public import BecknerOnofri.V2.Interval.FamilyMath4

@[expose] public section

/-!
# Specification of the family builder, phase 4: variance, slope, residuals
-/

namespace BecknerOnofri.V2.Interval

open BecknerOnofri.V2.FiniteState BecknerOnofri.HighDim.Spin Finset

attribute [local irreducible] addB negB mulB smulB sdivB addcB invB logB cst powB sumB mapR pochGo

theorem xtBody_spec (t : ℝ) {Γ : List SFact} (tR : ℕ) (j : ℕ)
    (ht : SFact.has t tR t ∈ Γ := by mem) :
    Tr Γ (xtBody tR j) (fun r => [SFact.has t r (xtVal t j)]) := by
  unfold xtBody
  st c
  st n
  refine Tr_val (Tr_addB (Impl.of_mem (by mem)) (Impl.of_mem (by mem))) ?_
  subst_vars
  rfl

theorem etTerm_spec (t : ℝ) {Γ : List SFact} (c1 : ℕ) (ps xt g : List ℕ) (j : ℕ) (hj : j < 13)
    (hps : SFact.hasF t ps 13 (psVal t) ∈ Γ := by mem)
    (hxt : SFact.hasF t xt 13 (xtVal t) ∈ Γ := by mem)
    (hg : SFact.hasF t g 13 (gF t) ∈ Γ := by mem) :
    Tr Γ (etTerm c1 ps xt g j) (fun r => [SFact.has t r (etVal t j)]) := by
  unfold etTerm
  refine Tr_fact (SFact.has t (ps.getD j c1) (psVal t j)) (Impl.getF c1 (Impl.of_mem hps) hj) ?_
  refine Tr_fact (SFact.has t (xt.getD j c1) (xtVal t j)) (Impl.getF c1 (Impl.of_mem (by mem)) hj) ?_
  refine Tr_fact (SFact.has t (g.getD j c1) (gF t j)) (Impl.getF c1 (Impl.of_mem (by mem)) hj) ?_
  st m1
  refine Tr_val (Tr_mulB (Impl.of_mem (by mem)) (Impl.of_mem (by mem))) ?_
  subst_vars
  rfl

theorem eBody_spec (t M η : ℝ) {Γ : List SFact} (c1 meang eta : ℕ) (g xt : List ℕ) (j : ℕ)
    (hj : j < 13)
    (hM : SFact.has t meang M ∈ Γ := by mem) (hη : SFact.has t eta η ∈ Γ := by mem)
    (hg : SFact.hasF t g 13 (gF t) ∈ Γ := by mem)
    (hxt : SFact.hasF t xt 13 (xtVal t) ∈ Γ := by mem) :
    Tr Γ (eBody c1 meang eta g xt j) (fun r => [SFact.has t r (eVal M η t j)]) := by
  unfold eBody
  refine Tr_fact (SFact.has t (g.getD j c1) (gF t j)) (Impl.getF c1 (Impl.of_mem hg) hj) ?_
  refine Tr_fact (SFact.has t (xt.getD j c1) (xtVal t j)) (Impl.getF c1 (Impl.of_mem (by mem)) hj) ?_
  st nm
  st z1
  st z2
  st nz
  refine Tr_val (Tr_addB (Impl.of_mem (by mem)) (Impl.of_mem (by mem))) ?_
  subst_vars
  rfl

theorem varTerm_spec (t : ℝ) (E : ℕ → ℝ) {Γ : List SFact} (c1 : ℕ) (ps e : List ℕ) (j : ℕ)
    (hj : j < 13)
    (hps : SFact.hasF t ps 13 (psVal t) ∈ Γ := by mem)
    (he : SFact.hasF t e 13 E ∈ Γ := by mem) :
    Tr Γ (varTerm c1 ps e j) (fun r => [SFact.has t r (psVal t j * E j ^ 2)]) := by
  unfold varTerm
  refine Tr_fact (SFact.has t (ps.getD j c1) (psVal t j)) (Impl.getF c1 (Impl.of_mem hps) hj) ?_
  refine Tr_fact (SFact.has t (e.getD j c1) (E j)) (Impl.getF c1 (Impl.of_mem (by mem)) hj) ?_
  st pw
  refine Tr_val Tr_mulB ?_
  subst_vars
  rfl

theorem phase4_spec (t : ℝ) (h0 : 0 ≤ t) (h1 : t < 1) {Γ : List SFact} (s1 : S1) (s2 : S2)
    (s3 : S3)
    (ht : SFact.has t s1.t t ∈ Γ := by mem)
    (hc1 : SFact.has t s1.c1 1 ∈ Γ := by mem)
    (hlam : SFact.has t s1.lam (famLam t) ∈ Γ := by mem)
    (ha : SFact.has t s1.a (famBias t) ∈ Γ := by mem)
    (homa : SFact.has t s1.oma (1 - famBias t) ∈ Γ := by mem)
    (hh : SFact.has t s1.h (famOmega t) ∈ Γ := by mem)
    (homlam : SFact.has t s2.omlam (1 - famLam t) ∈ Γ := by mem)
    (hps : SFact.hasF t s2.ps 13 (psVal t) ∈ Γ := by mem)
    (hg : SFact.hasF t s3.g 13 (gF t) ∈ Γ := by mem)
    (hmg : SFact.has t s3.meang (regMean (famLaw t) (gradient (famLaw t))) ∈ Γ := by mem) :
    Tr Γ (phase4 s1 s2 s3) (fun r => [SFact.hasF t r.e 13 (famResidF t),
      SFact.has t r.var (famResidVar t)]) := by
  unfold phase4
  st aa
  st naa
  st ab
  st A1
  st A2
  st hh1
  st hh2
  st A3
  st ih1
  st ih2
  st A4
  st lo
  st po
  st B1
  st vz
  have hvz : vz = regVar (famLaw t) meanCoordinate t := by
    rw [regVar_formula h0 h1]
    subst_vars
    unfold famVarFormula
    push_cast
    ring
  subst hvz
  refine Tr_bind (Tr_mapM (t := t) 13 (X := xtVal t) (fun j _ => xtBody_spec t s1.t j))
    (fun xt => ?_)
  refine Tr_bind (Tr_mapM (t := t) 13 (X := etVal t)
    (fun j hj => etTerm_spec t s1.c1 s2.ps xt s3.g j hj)) (fun etT => ?_)
  refine Tr_bind (Tr_val (t := t) (Tr_sumB' (Impl.of_mem (by mem))) (show _ = esVal t from rfl))
    (fun es => ?_)
  st ivz
  st eta
  have hη : eta = regSlope (famLaw t) meanCoordinate (gradient (famLaw t)) t := by
    rw [← eta_eq]
    subst_vars
    rfl
  subst hη
  refine Tr_bind (Tr_mapM (t := t) 13
    (X := eVal (regMean (famLaw t) (gradient (famLaw t)))
      (regSlope (famLaw t) meanCoordinate (gradient (famLaw t)) t) t)
    (fun j hj => eBody_spec t _ _ s1.c1 s3.meang etaR s3.g xt j hj)) (fun e => ?_)
  refine Tr_bind (Tr_mapM (t := t) 13
    (X := fun j => psVal t j *
      eVal (regMean (famLaw t) (gradient (famLaw t)))
        (regSlope (famLaw t) meanCoordinate (gradient (famLaw t)) t) t j ^ 2)
    (fun j hj => varTerm_spec t _ s1.c1 s2.ps e j hj)) (fun vT => ?_)
  refine Tr_bind (Tr_val (t := t) (Tr_sumB' (Impl.of_mem (by mem))) (var_eq t)) (fun var => ?_)
  refine Tr_pure fun s hs F hF => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hF
  rcases hF with rfl | rfl
  · obtain ⟨hl, hh⟩ := hs (SFact.hasF t e 13 (eVal (regMean (famLaw t) (gradient (famLaw t)))
      (regSlope (famLaw t) meanCoordinate (gradient (famLaw t)) t) t)) (by mem)
    exact ⟨hl, fun j hj => by rw [← eVal_famResidF t hj]; exact hh j hj⟩
  · exact hs _ (by mem)

end BecknerOnofri.V2.Interval
