module

public import BecknerOnofri.V2.Interval.FamilySpec4

@[expose] public section

/-!
# Specification of the family builder, phase 5: the output registers; the whole family
-/

namespace BecknerOnofri.V2.Interval

open BecknerOnofri.V2.FiniteState BecknerOnofri.HighDim.Spin Finset

attribute [local irreducible] addB negB mulB smulB sdivB addcB invB logB cst powB sumB mapR pochGo

/-- `e_j + 1/4` as a function on `ℕ`. -/
noncomputable def outE (t : ℝ) (j : ℕ) : ℝ := famResidF t j + 1 / 4

theorem phase5_raw_spec (t : ℝ) {Γ : List SFact} (s1 : S1) (s3 : S3) (s4 : S4)
    (ht : SFact.has t s1.t t ∈ Γ := by mem)
    (hu : SFact.has t s1.u (t ^ 2) ∈ Γ := by mem)
    (hf : SFact.has t s3.f (functional (famLaw t)) ∈ Γ := by mem)
    (hv : SFact.has t s4.var (famResidVar t) ∈ Γ := by mem)
    (he : SFact.hasF t s4.e 13 (famResidF t) ∈ Γ := by mem) :
    Tr Γ (phase5 true s1 s3 s4) (fun o => [SFact.has t o.f (famF t),
      SFact.has t o.v (famResidVar t), SFact.hasF t o.e 13 (outE t)]) := by
  unfold phase5
  st t4
  st c14
  st su
  st nsu
  st den14
  refine Tr_bind (Tr_mapM (t := t) 13 (X := outE t) ?_) (fun e' => ?_)
  · intro j hj
    refine Tr_fact (SFact.has t (s4.e.getD j s1.c1) (famResidF t j))
      (Impl.getF s1.c1 (Impl.of_mem (by mem)) hj) ?_
    refine Tr_val (Tr_addcB (Impl.of_mem (by mem))) ?_
    unfold outE
    push_cast
    rfl
  simp only [↓reduceIte]
  st k1
  st k2
  st k3
  st fr
  refine Tr_pure fun s hs F hF => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hF
  rcases hF with rfl | rfl | rfl
  · fin frR
    subst_vars
    unfold famF psiV2
    push_cast
    ring
  · exact hs _ (by mem)
  · exact hs _ (by mem)

theorem phase5_norm_spec (t : ℝ) (ht0 : t ≠ 0) {Γ : List SFact} (s1 : S1) (s3 : S3) (s4 : S4)
    (ht : SFact.has t s1.t t ∈ Γ := by mem)
    (hu : SFact.has t s1.u (t ^ 2) ∈ Γ := by mem)
    (hf : SFact.has t s3.f (functional (famLaw t)) ∈ Γ := by mem)
    (hv : SFact.has t s4.var (famResidVar t) ∈ Γ := by mem)
    (he : SFact.hasF t s4.e 13 (famResidF t) ∈ Γ := by mem) :
    Tr Γ (phase5 false s1 s3 s4) (fun o => [SFact.has t o.f (famF t / t ^ 4 - 1 / 10),
      SFact.has t o.v (1 / 50 - famResidVar t / t ^ 4), SFact.hasF t o.e 13 (outE t)]) := by
  have h4 : t ^ 4 ≠ 0 := pow_ne_zero 4 ht0
  have key : t ^ 4 * (t ^ 4)⁻¹ = 1 := mul_inv_cancel₀ h4
  unfold phase5
  st t4
  st c14
  st su
  st nsu
  st den14
  refine Tr_bind (Tr_mapM (t := t) 13 (X := outE t) ?_) (fun e' => ?_)
  · intro j hj
    refine Tr_fact (SFact.has t (s4.e.getD j s1.c1) (famResidF t j))
      (Impl.getF s1.c1 (Impl.of_mem (by mem)) hj) ?_
    refine Tr_val (Tr_addcB (Impl.of_mem (by mem))) ?_
    unfold outE
    push_cast
    rfl
  simp only [Bool.false_eq_true, ↓reduceIte]
  st it4
  st x1
  st id14
  st x2
  st x12
  st fr
  st c50
  st it4'
  st vt
  st nvt
  st w
  refine Tr_pure fun s hs F hF => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hF
  rcases hF with rfl | rfl | rfl
  · fin frR
    subst_vars
    unfold famF psiV2
    push_cast
    simp only [div_eq_mul_inv]
    linear_combination (-12 * (14 - 10 * t ^ 2)⁻¹) * key
  · fin wR
    subst_vars
    push_cast
    simp only [div_eq_mul_inv]
    ring
  · exact hs _ (by mem)

end BecknerOnofri.V2.Interval
