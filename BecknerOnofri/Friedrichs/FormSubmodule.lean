import BecknerOnofri.Friedrichs.SpatialClosability
import Mathlib.Topology.Algebra.Module.Basic

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped ContDiff
namespace BecknerOnofri.Friedrichs.SpatialForm

lemma zero_mem_core (m : ℕ) : (0 : EnergySpace)∈core m := by
  refine ⟨0,contDiff_const,?_,?_,?_,?_,?_⟩
  · exact HasCompactSupport.zero
  · simp
  · exact Lp.coeFn_zero ℝ 2 intervalMeasure
  · simpa using Lp.coeFn_zero ℝ 2 intervalMeasure
  · filter_upwards [Lp.coeFn_zero ℝ 2 intervalMeasure] with t ht
    change (0 : H) t=potentialFactor m t*0
    simpa only [Pi.zero_apply,mul_zero] using ht

lemma add_mem_core {m : ℕ} {u v : EnergySpace} (hu : u∈core m) (hv : v∈core m) :
    u+v∈core m := by
  obtain ⟨f,hf,hfc,hfs,hu0,hu1,huV⟩ := hu
  obtain ⟨g,hg,hgc,hgs,hv0,hv1,hvV⟩ := hv
  refine ⟨f+g,hf.add hg,hfc.add hgc,(tsupport_add f g).trans (union_subset hfs hgs),?_,?_,?_⟩
  · exact (Lp.coeFn_add u.1 v.1).trans (hu0.add hv0)
  · have hd : deriv (f+g)=deriv f+deriv g := funext (fun t =>
      deriv_add (hf.differentiable (by simp) t) (hg.differentiable (by simp) t))
    rw [hd]
    exact (Lp.coeFn_add u.2.1 v.2.1).trans (hu1.add hv1)
  · filter_upwards [Lp.coeFn_add u.2.2 v.2.2,huV,hvV] with t ht huf hvf
    change (u.2.2+v.2.2) t=potentialFactor m t*(f t+g t)
    rw [ht]
    simp only [Pi.add_apply,huf,hvf]
    ring

lemma smul_mem_core {m : ℕ} {u : EnergySpace} (hu : u∈core m) (c : ℝ) : c • u∈core m := by
  obtain ⟨f,hf,hfc,hfs,hu0,hu1,huV⟩ := hu
  refine ⟨fun t => c*f t,contDiff_const.mul hf,hfc.mul_left,
    tsupport_mul_subset_right.trans hfs,?_,?_,?_⟩
  · exact (Lp.coeFn_smul c u.1).trans (hu0.const_smul c)
  · have hd : deriv (fun t => c*f t)=fun t => c*deriv f t := deriv_const_mul_field' c
    rw [hd]
    exact (Lp.coeFn_smul c u.2.1).trans (hu1.const_smul c)
  · filter_upwards [Lp.coeFn_smul c u.2.2,huV] with t ht huf
    change (c • u.2.2) t=potentialFactor m t*(c*f t)
    rw [ht]
    simp only [Pi.smul_apply,smul_eq_mul,huf]
    ring

def coreSubmodule (m : ℕ) : Submodule ℝ EnergySpace where
  carrier := core m
  zero_mem' := zero_mem_core m
  add_mem' := add_mem_core
  smul_mem' := fun c _ hu => smul_mem_core hu c

def closedFormSubmodule (m : ℕ) : Submodule ℝ EnergySpace :=
  (coreSubmodule m).topologicalClosure

@[simp] lemma mem_closedFormSubmodule (m : ℕ) (u : EnergySpace) :
    u∈closedFormSubmodule m ↔ u∈formClosure m := Iff.rfl

#print axioms closedFormSubmodule
end BecknerOnofri.Friedrichs.SpatialForm
