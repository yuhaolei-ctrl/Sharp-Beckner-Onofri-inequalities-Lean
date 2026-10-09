module

public import BecknerOnofri.V2.Interval.FamilyBuilder
public import BecknerOnofri.V2.FiniteState.FamilyDefs
public import BecknerOnofri.V2.FiniteState.FamilyVariance

@[expose] public section

/-!
# Specification of the family builder, phase 1: the scalar parameters

Proof tactics `st x` (run the next primitive, binding the result register `xR` and its value `x`
with the defining equation `hx`) and the first phase of `family2`.
-/

namespace BecknerOnofri.V2.Interval

theorem BSHas.cast {t : ℝ} {s : BS} {i : ℕ} {x y : ℝ} (h : BSHas t s i x) (e : x = y) :
    BSHas t s i y := e ▸ h

attribute [local irreducible] addB negB mulB smulB sdivB addcB invB logB cst powB sumB mapR pochGo

set_option hygiene false in
/-- `st x`: symbolic execution of the next builder primitive; the result register is `xR`, its
real value `x`, and `hx` is the defining equation. -/
syntax "st " ident : tactic

set_option hygiene false in
macro_rules
  | `(tactic| st $x:ident) => do
    let hn := Lean.mkIdent (Lean.Name.mkSimple ("h" ++ x.getId.toString))
    let rn := Lean.mkIdent (Lean.Name.mkSimple (x.getId.toString ++ "R"))
    `(tactic| first
      | refine Tr_bind_g (t := t) Tr_var (fun $rn $x $hn => ?_)
      | refine Tr_bind_g (t := t) Tr_cst (fun $rn $x $hn => ?_)
      | refine Tr_bind_g (t := t) Tr_addB (fun $rn $x $hn => ?_)
      | refine Tr_bind_g (t := t) Tr_negB (fun $rn $x $hn => ?_)
      | refine Tr_bind_g (t := t) Tr_mulB (fun $rn $x $hn => ?_)
      | refine Tr_bind_g (t := t) Tr_smulB (fun $rn $x $hn => ?_)
      | refine Tr_bind_g (t := t) Tr_sdivB (fun $rn $x $hn => ?_)
      | refine Tr_bind_g (t := t) Tr_addcB (fun $rn $x $hn => ?_)
      | refine Tr_bind_g (t := t) Tr_invB (fun $rn $x $hn => ?_)
      | refine Tr_bind_g (t := t) Tr_logB (fun $rn $x $hn => ?_)
      | refine Tr_bind_g (t := t) Tr_emit_smul (fun $rn $x $hn => ?_)
      | refine Tr_bind_g (t := t) (Tr_powB (Impl.of_mem (by mem)) _ _ (by norm_num)) (fun $rn $x $hn => ?_))

set_option hygiene false in
/-- Close a `Tr_pure` obligation for register `r` by the fact found in the context. -/
macro "fin " r:term : tactic =>
  `(tactic| (refine BSHas.cast (hs (SFact.has _ $r _) (by mem)) ?_; clear hs))

end BecknerOnofri.V2.Interval

namespace BecknerOnofri.V2.Interval

open BecknerOnofri.V2.FiniteState

attribute [local irreducible] addB negB mulB smulB sdivB addcB invB logB cst powB sumB mapR pochGo

theorem phase1_spec (t : ℝ) {Γ : List SFact} :
    Tr Γ phase1 (fun s => [SFact.has t s.t t, SFact.has t s.c1 1, SFact.has t s.u (t ^ 2),
      SFact.has t s.lam (famLam t), SFact.has t s.a (famBias t),
      SFact.has t s.oma (1 - famBias t), SFact.has t s.h (famOmega t),
      SFact.has t s.Ap ((1 + famBias t) / 2), SFact.has t s.Am ((1 - famBias t) / 2)]) := by
  unfold phase1
  st tv
  st c1
  st u
  st t10
  st L
  st lx1
  st lx2
  st lam
  st nt
  st omt
  st ly1
  st ly2
  st a
  st nu
  st omu
  st p1
  st T1
  st q1
  st q2
  st T2
  st w1
  st w2
  st T3
  st r1
  st T4
  st P1
  st P2
  st P
  st uu
  st h1
  st h2
  st hden
  st g1
  st g2
  st h
  st ap1
  st Ap
  st na
  st oma
  st Am
  refine Tr_pure fun s hs F hF => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hF
  rcases hF with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · fin tvR
    exact htv
  · fin c1R
    rw [hc1]; simp
  · fin uR
    subst_vars; ring
  · fin lamR
    subst_vars; unfold famLam famL; push_cast; ring
  · fin aR
    subst_vars; unfold famBias famL; push_cast; ring
  · fin omaR
    subst_vars; unfold famBias famL; push_cast; ring
  · fin hR
    subst_vars; unfold famOmega famP; push_cast; ring
  · fin ApR
    subst_vars; unfold famBias famL; push_cast; ring
  · fin AmR
    subst_vars; unfold famBias famL; push_cast; ring

end BecknerOnofri.V2.Interval
